import V185TrunkScan23Chunk0325

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1927369 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_1927369 : Nat := 118140960795 + 1927369 * 2 ^ 59
def prefixEnd_1927369 : Nat := 4983230072969 + 3 ^ 40 * 1927369 * 2
def baseEnd_1927369 : Nat := 329888898525191631207899

theorem tailTrace_1927369 : CollatzResearch.WordTrace tailWord_1927369 prefixEnd_1927369 329888898525191631207899 := by
  unfold tailWord_1927369
  simp only [CollatzResearch.WordTrace]
  refine ⟨70296922554478756263873161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46864615036319170842582107 70296922554478756263873161)
  ·
    refine ⟨52722691915859067197904871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70296922554478756263873161 52722691915859067197904871)
    ·
      refine ⟨79084037873788600796857307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52722691915859067197904871 79084037873788600796857307)
      ·
        refine ⟨118626056810682901195285961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79084037873788600796857307 118626056810682901195285961)
        ·
          refine ⟨88969542608012175896464471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118626056810682901195285961 88969542608012175896464471)
          ·
            refine ⟨133454313912018263844696707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88969542608012175896464471 133454313912018263844696707)
            ·
              refine ⟨200181470868027395767045061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133454313912018263844696707 200181470868027395767045061)
              ·
                refine ⟨37534025787755136706320949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200181470868027395767045061 37534025787755136706320949)
                ·
                  refine ⟨3518814917602044066217589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37534025787755136706320949 3518814917602044066217589)
                  ·
                    refine ⟨329888898525191631207899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3518814917602044066217589 329888898525191631207899)
                    ·
                      rfl

theorem cell23_1927369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_1927369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927369 prefixEnd_1927369 := by exact prefixLift 1927369
  have htrace : WordTrace (prefixWord ++ tailWord_1927369) baseStart_1927369 baseEnd_1927369 := by
    simpa [prefixWord, tailWord_1927369, baseEnd_1927369] using wordTrace_append hprefix tailTrace_1927369
  have hstable : (prefixWord ++ tailWord_1927369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927369).length < 2 ^ (prefixWord ++ tailWord_1927369).sum := by decide
  have hdescent : baseEnd_1927369 < baseStart_1927369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927450 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_1927450 : Nat := 118140960795 + 1927450 * 2 ^ 59
def prefixEnd_1927450 : Nat := 4983230072969 + 3 ^ 40 * 1927450 * 2
def baseEnd_1927450 : Nat := 329902762502863025570275

theorem tailTrace_1927450 : CollatzResearch.WordTrace tailWord_1927450 prefixEnd_1927450 329902762502863025570275 := by
  unfold tailWord_1927450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574969216796326774392951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46866584578123538065047869 17574969216796326774392951)
  ·
    refine ⟨26362453825194490161589427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17574969216796326774392951 26362453825194490161589427)
    ·
      refine ⟨39543680737791735242384141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26362453825194490161589427 39543680737791735242384141)
      ·
        refine ⟨14828880276671900715894053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39543680737791735242384141 14828880276671900715894053)
        ·
          refine ⟨2780415051875981384230135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14828880276671900715894053 2780415051875981384230135)
          ·
            refine ⟨4170622577813972076345203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780415051875981384230135 4170622577813972076345203)
            ·
              refine ⟨6255933866720958114517805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170622577813972076345203 6255933866720958114517805)
              ·
                refine ⟨2345975200020359292944177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6255933866720958114517805 2345975200020359292944177)
                ·
                  refine ⟨1759481400015269469708133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345975200020359292944177 1759481400015269469708133)
                  ·
                    refine ⟨329902762502863025570275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759481400015269469708133 329902762502863025570275)
                    ·
                      rfl

theorem cell23_1927450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_1927450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927450 prefixEnd_1927450 := by exact prefixLift 1927450
  have htrace : WordTrace (prefixWord ++ tailWord_1927450) baseStart_1927450 baseEnd_1927450 := by
    simpa [prefixWord, tailWord_1927450, baseEnd_1927450] using wordTrace_append hprefix tailTrace_1927450
  have hstable : (prefixWord ++ tailWord_1927450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927450).length < 2 ^ (prefixWord ++ tailWord_1927450).sum := by decide
  have hdescent : baseEnd_1927450 < baseStart_1927450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927460 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1927460 : Nat := 118140960795 + 1927460 * 2 ^ 59
def prefixEnd_1927460 : Nat := 4983230072969 + 3 ^ 40 * 1927460 * 2
def baseEnd_1927460 : Nat := 989713422315134037585779

theorem tailTrace_1927460 : CollatzResearch.WordTrace tailWord_1927460 prefixEnd_1927460 989713422315134037585779 := by
  unfold tailWord_1927460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150120798574539402717917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46866827731432719203623889 35150120798574539402717917)
  ·
    refine ⟨13181295299465452276019219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35150120798574539402717917 13181295299465452276019219)
    ·
      refine ⟨19771942949198178414028829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13181295299465452276019219 19771942949198178414028829)
      ·
        refine ⟨7414478605949316905260811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19771942949198178414028829 7414478605949316905260811)
        ·
          refine ⟨11121717908923975357891217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414478605949316905260811 11121717908923975357891217)
          ·
            refine ⟨8341288431692981518418413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11121717908923975357891217 8341288431692981518418413)
            ·
              refine ⟨3127983161884868069406905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8341288431692981518418413 3127983161884868069406905)
              ·
                refine ⟨2345987371413651052055179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127983161884868069406905 2345987371413651052055179)
                ·
                  refine ⟨3518981057120476578082769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345987371413651052055179 3518981057120476578082769)
                  ·
                    refine ⟨2639235792840357433562077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518981057120476578082769 2639235792840357433562077)
                    ·
                      refine ⟨989713422315134037585779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639235792840357433562077 989713422315134037585779)
                      ·
                        rfl

theorem cell23_1927460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1927460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927460 prefixEnd_1927460 := by exact prefixLift 1927460
  have htrace : WordTrace (prefixWord ++ tailWord_1927460) baseStart_1927460 baseEnd_1927460 := by
    simpa [prefixWord, tailWord_1927460, baseEnd_1927460] using wordTrace_append hprefix tailTrace_1927460
  have hstable : (prefixWord ++ tailWord_1927460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927460).length < 2 ^ (prefixWord ++ tailWord_1927460).sum := by decide
  have hdescent : baseEnd_1927460 < baseStart_1927460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927496 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1927496 : Nat := 118140960795 + 1927496 * 2 ^ 59
def prefixEnd_1927496 : Nat := 4983230072969 + 3 ^ 40 * 1927496 * 2
def baseEnd_1927496 : Nat := 989731907618695896735613

theorem tailTrace_1927496 : CollatzResearch.WordTrace tailWord_1927496 prefixEnd_1927496 989731907618695896735613 := by
  unfold tailWord_1927496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150777312509328476873171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46867703083345771302497561 35150777312509328476873171)
  ·
    refine ⟨52726165968763992715309757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35150777312509328476873171 52726165968763992715309757)
    ·
      refine ⟨19772312238286497268241159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52726165968763992715309757 19772312238286497268241159)
      ·
        refine ⟨29658468357429745902361739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19772312238286497268241159 29658468357429745902361739)
        ·
          refine ⟨44487702536144618853542609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29658468357429745902361739 44487702536144618853542609)
          ·
            refine ⟨33365776902108464140156957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44487702536144618853542609 33365776902108464140156957)
            ·
              refine ⟨12512166338290674052558859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33365776902108464140156957 12512166338290674052558859)
              ·
                refine ⟨18768249507436011078838289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512166338290674052558859 18768249507436011078838289)
                ·
                  refine ⟨14076187130577008309128717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768249507436011078838289 14076187130577008309128717)
                  ·
                    refine ⟨5278570173966378115923269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076187130577008309128717 5278570173966378115923269)
                    ·
                      refine ⟨989731907618695896735613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5278570173966378115923269 989731907618695896735613)
                      ·
                        rfl

theorem cell23_1927496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1927496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927496 prefixEnd_1927496 := by exact prefixLift 1927496
  have htrace : WordTrace (prefixWord ++ tailWord_1927496) baseStart_1927496 baseEnd_1927496 := by
    simpa [prefixWord, tailWord_1927496, baseEnd_1927496] using wordTrace_append hprefix tailTrace_1927496
  have hstable : (prefixWord ++ tailWord_1927496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927496).length < 2 ^ (prefixWord ++ tailWord_1927496).sum := by decide
  have hdescent : baseEnd_1927496 < baseStart_1927496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927506 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1927506 : Nat := 118140960795 + 1927506 * 2 ^ 59
def prefixEnd_1927506 : Nat := 4983230072969 + 3 ^ 40 * 1927506 * 2
def baseEnd_1927506 : Nat := 329912347475080285870189

theorem tailTrace_1927506 : CollatzResearch.WordTrace tailWord_1927506 prefixEnd_1927506 329912347475080285870189 := by
  unfold tailWord_1927506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575479838745607165402593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46867946236654952441073581 17575479838745607165402593)
  ·
    refine ⟨13181609879059205374051945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17575479838745607165402593 13181609879059205374051945)
    ·
      refine ⟨9886207409294404030538959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13181609879059205374051945 9886207409294404030538959)
      ·
        refine ⟨14829311113941606045808439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9886207409294404030538959 14829311113941606045808439)
        ·
          refine ⟨22243966670912409068712659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829311113941606045808439 22243966670912409068712659)
          ·
            refine ⟨33365950006368613603068989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22243966670912409068712659 33365950006368613603068989)
            ·
              refine ⟨12512231252388230101150871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33365950006368613603068989 12512231252388230101150871)
              ·
                refine ⟨18768346878582345151726307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512231252388230101150871 18768346878582345151726307)
                ·
                  refine ⟨28152520317873517727589461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18768346878582345151726307 28152520317873517727589461)
                  ·
                    refine ⟨329912347475080285870189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28152520317873517727589461 329912347475080285870189)
                    ·
                      rfl

theorem cell23_1927506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1927506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927506 prefixEnd_1927506 := by exact prefixLift 1927506
  have htrace : WordTrace (prefixWord ++ tailWord_1927506) baseStart_1927506 baseEnd_1927506 := by
    simpa [prefixWord, tailWord_1927506, baseEnd_1927506] using wordTrace_append hprefix tailTrace_1927506
  have hstable : (prefixWord ++ tailWord_1927506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927506).length < 2 ^ (prefixWord ++ tailWord_1927506).sum := by decide
  have hdescent : baseEnd_1927506 < baseStart_1927506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927547 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 2, 2, 2]
def baseStart_1927547 : Nat := 118140960795 + 1927547 * 2 ^ 59
def prefixEnd_1927547 : Nat := 4983230072969 + 3 ^ 40 * 1927547 * 2
def baseEnd_1927547 : Nat := 989758095132075197197879

theorem tailTrace_1927547 : CollatzResearch.WordTrace tailWord_1927547 prefixEnd_1927547 989758095132075197197879 := by
  unfold tailWord_1927547
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303414747833892663852895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46868943165222595109235263 70303414747833892663852895)
  ·
    refine ⟨105455122121750838995779343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70303414747833892663852895 105455122121750838995779343)
    ·
      refine ⟨158182683182626258493669015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105455122121750838995779343 158182683182626258493669015)
      ·
        refine ⟨237274024773939387740503523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158182683182626258493669015 237274024773939387740503523)
        ·
          refine ⟨355911037160909081610755285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237274024773939387740503523 355911037160909081610755285)
          ·
            refine ⟨8341664933458806600252077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 355911037160909081610755285 8341664933458806600252077)
            ·
              refine ⟨3128124350047052475094529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8341664933458806600252077 3128124350047052475094529)
              ·
                refine ⟨2346093262535289356320897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128124350047052475094529 2346093262535289356320897)
                ·
                  refine ⟨1759569946901467017240673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2346093262535289356320897 1759569946901467017240673)
                  ·
                    refine ⟨1319677460176100262930505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759569946901467017240673 1319677460176100262930505)
                    ·
                      refine ⟨989758095132075197197879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319677460176100262930505 989758095132075197197879)
                      ·
                        rfl

theorem cell23_1927547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2, 2].length) (baseStart_1927547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927547 prefixEnd_1927547 := by exact prefixLift 1927547
  have htrace : WordTrace (prefixWord ++ tailWord_1927547) baseStart_1927547 baseEnd_1927547 := by
    simpa [prefixWord, tailWord_1927547, baseEnd_1927547] using wordTrace_append hprefix tailTrace_1927547
  have hstable : (prefixWord ++ tailWord_1927547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927547).length < 2 ^ (prefixWord ++ tailWord_1927547).sum := by decide
  have hdescent : baseEnd_1927547 < baseStart_1927547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927553 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 7]
def baseStart_1927553 : Nat := 118140960795 + 1927553 * 2 ^ 59
def prefixEnd_1927553 : Nat := 4983230072969 + 3 ^ 40 * 1927553 * 2
def baseEnd_1927553 : Nat := 109973464001778019302539

theorem tailTrace_1927553 : CollatzResearch.WordTrace tailWord_1927553 prefixEnd_1927553 109973464001778019302539 := by
  unfold tailWord_1927553
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303633585812155688571313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46869089057208103792380875 70303633585812155688571313)
  ·
    refine ⟨52727725189359116766428485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70303633585812155688571313 52727725189359116766428485)
    ·
      refine ⟨9886448473004834393705341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52727725189359116766428485 9886448473004834393705341)
      ·
        refine ⟨3707418177376812897639503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9886448473004834393705341 3707418177376812897639503)
        ·
          refine ⟨5561127266065219346459255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707418177376812897639503 5561127266065219346459255)
          ·
            refine ⟨8341690899097829019688883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561127266065219346459255 8341690899097829019688883)
            ·
              refine ⟨12512536348646743529533325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341690899097829019688883 12512536348646743529533325)
              ·
                refine ⟨4692201130742528823574997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12512536348646743529533325 4692201130742528823574997)
                ·
                  refine ⟨109973464001778019302539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4692201130742528823574997 109973464001778019302539)
                  ·
                    rfl

theorem cell23_1927553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_1927553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927553 prefixEnd_1927553 := by exact prefixLift 1927553
  have htrace : WordTrace (prefixWord ++ tailWord_1927553) baseStart_1927553 baseEnd_1927553 := by
    simpa [prefixWord, tailWord_1927553, baseEnd_1927553] using wordTrace_append hprefix tailTrace_1927553
  have hstable : (prefixWord ++ tailWord_1927553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927553).length < 2 ^ (prefixWord ++ tailWord_1927553).sum := by decide
  have hdescent : baseEnd_1927553 < baseStart_1927553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927563 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3]
def baseStart_1927563 : Nat := 118140960795 + 1927563 * 2 ^ 59
def prefixEnd_1927563 : Nat := 4983230072969 + 3 ^ 40 * 1927563 * 2
def baseEnd_1927563 : Nat := 989766310822547134597805

theorem tailTrace_1927563 : CollatzResearch.WordTrace tailWord_1927563 prefixEnd_1927563 989766310822547134597805 := by
  unfold tailWord_1927563
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303998315775927396435343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46869332210517284930956895 70303998315775927396435343)
  ·
    refine ⟨105455997473663891094653015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70303998315775927396435343 105455997473663891094653015)
    ·
      refine ⟨158183996210495836641979523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105455997473663891094653015 158183996210495836641979523)
      ·
        refine ⟨237275994315743754962969285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158183996210495836641979523 237275994315743754962969285)
        ·
          refine ⟨44489248934201954055556741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237275994315743754962969285 44489248934201954055556741)
          ·
            refine ⟨8341734175162866385416889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44489248934201954055556741 8341734175162866385416889)
            ·
              refine ⟨6256300631372149789062667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8341734175162866385416889 6256300631372149789062667)
              ·
                refine ⟨9384450947058224683594001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256300631372149789062667 9384450947058224683594001)
                ·
                  refine ⟨7038338210293668512695501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9384450947058224683594001 7038338210293668512695501)
                  ·
                    refine ⟨2639376828860125692260813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7038338210293668512695501 2639376828860125692260813)
                    ·
                      refine ⟨989766310822547134597805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639376828860125692260813 989766310822547134597805)
                      ·
                        rfl

theorem cell23_1927563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].length) (baseStart_1927563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927563 prefixEnd_1927563 := by exact prefixLift 1927563
  have htrace : WordTrace (prefixWord ++ tailWord_1927563) baseStart_1927563 baseEnd_1927563 := by
    simpa [prefixWord, tailWord_1927563, baseEnd_1927563] using wordTrace_append hprefix tailTrace_1927563
  have hstable : (prefixWord ++ tailWord_1927563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927563).length < 2 ^ (prefixWord ++ tailWord_1927563).sum := by decide
  have hdescent : baseEnd_1927563 < baseStart_1927563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927564 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_1927564 : Nat := 118140960795 + 1927564 * 2 ^ 59
def prefixEnd_1927564 : Nat := 4983230072969 + 3 ^ 40 * 1927564 * 2
def baseEnd_1927564 : Nat := 989766824303201630685301

theorem tailTrace_1927564 : CollatzResearch.WordTrace tailWord_1927564 prefixEnd_1927564 989766824303201630685301 := by
  unfold tailWord_1927564
  simp only [CollatzResearch.WordTrace]
  refine ⟨35152017394386152283610873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46869356525848203044814497 35152017394386152283610873)
  ·
    refine ⟨26364013045789614212708155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35152017394386152283610873 26364013045789614212708155)
    ·
      refine ⟨39546019568684421319062233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26364013045789614212708155 39546019568684421319062233)
      ·
        refine ⟨29659514676513315989296675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39546019568684421319062233 29659514676513315989296675)
        ·
          refine ⟨44489272014769973983945013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29659514676513315989296675 44489272014769973983945013)
          ·
            refine ⟨4170869251384685060994845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44489272014769973983945013 4170869251384685060994845)
            ·
              refine ⟨1564075969269256897873067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4170869251384685060994845 1564075969269256897873067)
              ·
                refine ⟨2346113953903885346809601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564075969269256897873067 2346113953903885346809601)
                ·
                  refine ⟨1759585465427914010107201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2346113953903885346809601 1759585465427914010107201)
                  ·
                    refine ⟨1319689099070935507580401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759585465427914010107201 1319689099070935507580401)
                    ·
                      refine ⟨989766824303201630685301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319689099070935507580401 989766824303201630685301)
                      ·
                        rfl

theorem cell23_1927564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_1927564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927564 prefixEnd_1927564 := by exact prefixLift 1927564
  have htrace : WordTrace (prefixWord ++ tailWord_1927564) baseStart_1927564 baseEnd_1927564 := by
    simpa [prefixWord, tailWord_1927564, baseEnd_1927564] using wordTrace_append hprefix tailTrace_1927564
  have hstable : (prefixWord ++ tailWord_1927564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927564).length < 2 ^ (prefixWord ++ tailWord_1927564).sum := by decide
  have hdescent : baseEnd_1927564 < baseStart_1927564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927583 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 2, 5]
def baseStart_1927583 : Nat := 118140960795 + 1927583 * 2 ^ 59
def prefixEnd_1927583 : Nat := 4983230072969 + 3 ^ 40 * 1927583 * 2
def baseEnd_1927583 : Nat := 329925526811879018782571

theorem tailTrace_1927583 : CollatzResearch.WordTrace tailWord_1927583 prefixEnd_1927583 329925526811879018782571 := by
  unfold tailWord_1927583
  simp only [CollatzResearch.WordTrace]
  refine ⟨70304727775703470812163403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46869818517135647208108935 70304727775703470812163403)
  ·
    refine ⟨105457091663555206218245105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70304727775703470812163403 105457091663555206218245105)
    ·
      refine ⟨79092818747666404663683829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105457091663555206218245105 79092818747666404663683829)
      ·
        refine ⟨7414951757593725437220359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79092818747666404663683829 7414951757593725437220359)
        ·
          refine ⟨11122427636390588155830539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414951757593725437220359 11122427636390588155830539)
          ·
            refine ⟨16683641454585882233745809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11122427636390588155830539 16683641454585882233745809)
            ·
              refine ⟨12512731090939411675309357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16683641454585882233745809 12512731090939411675309357)
              ·
                refine ⟨4692274159102279378241009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12512731090939411675309357 4692274159102279378241009)
                ·
                  refine ⟨3519205619326709533680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4692274159102279378241009 3519205619326709533680757)
                  ·
                    refine ⟨329925526811879018782571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3519205619326709533680757 329925526811879018782571)
                    ·
                      rfl

theorem cell23_1927583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_1927583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927583 prefixEnd_1927583 := by exact prefixLift 1927583
  have htrace : WordTrace (prefixWord ++ tailWord_1927583) baseStart_1927583 baseEnd_1927583 := by
    simpa [prefixWord, tailWord_1927583, baseEnd_1927583] using wordTrace_append hprefix tailTrace_1927583
  have hstable : (prefixWord ++ tailWord_1927583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927583).length < 2 ^ (prefixWord ++ tailWord_1927583).sum := by decide
  have hdescent : baseEnd_1927583 < baseStart_1927583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927604 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1927604 : Nat := 118140960795 + 1927604 * 2 ^ 59
def prefixEnd_1927604 : Nat := 4983230072969 + 3 ^ 40 * 1927604 * 2
def baseEnd_1927604 : Nat := 109976373725486830465013

theorem tailTrace_1927604 : CollatzResearch.WordTrace tailWord_1927604 prefixEnd_1927604 109976373725486830465013 := by
  unfold tailWord_1927604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35152746854313695699338933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46870329139084927599118577 35152746854313695699338933)
  ·
    refine ⟨3295570017591908971813025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35152746854313695699338933 3295570017591908971813025)
    ·
      refine ⟨2471677513193931728859769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3295570017591908971813025 2471677513193931728859769)
      ·
        refine ⟨1853758134895448796644827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471677513193931728859769 1853758134895448796644827)
        ·
          refine ⟨2780637202343173194967241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853758134895448796644827 2780637202343173194967241)
          ·
            refine ⟨2085477901757379896225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780637202343173194967241 2085477901757379896225431)
            ·
              refine ⟨3128216852636069844338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085477901757379896225431 3128216852636069844338147)
              ·
                refine ⟨4692325278954104766507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128216852636069844338147 4692325278954104766507221)
                ·
                  refine ⟨109976373725486830465013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4692325278954104766507221 109976373725486830465013)
                  ·
                    rfl

theorem cell23_1927604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1927604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927604 prefixEnd_1927604 := by exact prefixLift 1927604
  have htrace : WordTrace (prefixWord ++ tailWord_1927604) baseStart_1927604 baseEnd_1927604 := by
    simpa [prefixWord, tailWord_1927604, baseEnd_1927604] using wordTrace_append hprefix tailTrace_1927604
  have hstable : (prefixWord ++ tailWord_1927604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927604).length < 2 ^ (prefixWord ++ tailWord_1927604).sum := by decide
  have hdescent : baseEnd_1927604 < baseStart_1927604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927673 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_1927673 : Nat := 118140960795 + 1927673 * 2 ^ 59
def prefixEnd_1927673 : Nat := 4983230072969 + 3 ^ 40 * 1927673 * 2
def baseEnd_1927673 : Nat := 329940931231513901407433

theorem tailTrace_1927673 : CollatzResearch.WordTrace tailWord_1927673 prefixEnd_1927673 329940931231513901407433 := by
  unfold tailWord_1927673
  simp only [CollatzResearch.WordTrace]
  refine ⟨70308010345377416182939673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46872006896918277455293115 70308010345377416182939673)
  ·
    refine ⟨52731007759033062137204755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70308010345377416182939673 52731007759033062137204755)
    ·
      refine ⟨79096511638549593205807133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52731007759033062137204755 79096511638549593205807133)
      ·
        refine ⟨29661191864456097452177675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79096511638549593205807133 29661191864456097452177675)
        ·
          refine ⟨44491787796684146178266513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29661191864456097452177675 44491787796684146178266513)
          ·
            refine ⟨33368840847513109633699885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44491787796684146178266513 33368840847513109633699885)
            ·
              refine ⟨12513315317817416112637457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33368840847513109633699885 12513315317817416112637457)
              ·
                refine ⟨9384986488363062084478093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12513315317817416112637457 9384986488363062084478093)
                ·
                  refine ⟨3519369933136148281679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9384986488363062084478093 3519369933136148281679285)
                  ·
                    refine ⟨329940931231513901407433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3519369933136148281679285 329940931231513901407433)
                    ·
                      rfl

theorem cell23_1927673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_1927673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927673 prefixEnd_1927673 := by exact prefixLift 1927673
  have htrace : WordTrace (prefixWord ++ tailWord_1927673) baseStart_1927673 baseEnd_1927673 := by
    simpa [prefixWord, tailWord_1927673, baseEnd_1927673] using wordTrace_append hprefix tailTrace_1927673
  have hstable : (prefixWord ++ tailWord_1927673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927673).length < 2 ^ (prefixWord ++ tailWord_1927673).sum := by decide
  have hdescent : baseEnd_1927673 < baseStart_1927673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927690 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1927690 : Nat := 118140960795 + 1927690 * 2 ^ 59
def prefixEnd_1927690 : Nat := 4983230072969 + 3 ^ 40 * 1927690 * 2
def baseEnd_1927690 : Nat := 329943840955222712569907

theorem tailTrace_1927690 : CollatzResearch.WordTrace tailWord_1927690 prefixEnd_1927690 329943840955222712569907 := by
  unfold tailWord_1927690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17577157596578957021577131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46872420257543885390872349 17577157596578957021577131)
  ·
    refine ⟨26365736394868435532365697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17577157596578957021577131 26365736394868435532365697)
    ·
      refine ⟨19774302296151326649274273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26365736394868435532365697 19774302296151326649274273)
      ·
        refine ⟨14830726722113494986955705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19774302296151326649274273 14830726722113494986955705)
        ·
          refine ⟨11123045041585121240216779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14830726722113494986955705 11123045041585121240216779)
          ·
            refine ⟨16684567562377681860325169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123045041585121240216779 16684567562377681860325169)
            ·
              refine ⟨12513425671783261395243877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684567562377681860325169 12513425671783261395243877)
              ·
                refine ⟨2346267313459361511608227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12513425671783261395243877 2346267313459361511608227)
                ·
                  refine ⟨3519400970189042267412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346267313459361511608227 3519400970189042267412341)
                  ·
                    refine ⟨329943840955222712569907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3519400970189042267412341 329943840955222712569907)
                    ·
                      rfl

theorem cell23_1927690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1927690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927690 prefixEnd_1927690 := by exact prefixLift 1927690
  have htrace : WordTrace (prefixWord ++ tailWord_1927690) baseStart_1927690 baseEnd_1927690 := by
    simpa [prefixWord, tailWord_1927690, baseEnd_1927690] using wordTrace_append hprefix tailTrace_1927690
  have hstable : (prefixWord ++ tailWord_1927690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927690).length < 2 ^ (prefixWord ++ tailWord_1927690).sum := by decide
  have hdescent : baseEnd_1927690 < baseStart_1927690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927704 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_1927704 : Nat := 118140960795 + 1927704 * 2 ^ 59
def prefixEnd_1927704 : Nat := 4983230072969 + 3 ^ 40 * 1927704 * 2
def baseEnd_1927704 : Nat := 989838711594831082934657

theorem tailTrace_1927704 : CollatzResearch.WordTrace tailWord_1927704 prefixEnd_1927704 989838711594831082934657 := by
  unfold tailWord_1927704
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154570504132554238659083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46872760672176738984878777 35154570504132554238659083)
  ·
    refine ⟨52731855756198831357988625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35154570504132554238659083 52731855756198831357988625)
    ·
      refine ⟨39548891817149123518491469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52731855756198831357988625 39548891817149123518491469)
      ·
        refine ⟨14830834431430921319434301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39548891817149123518491469 14830834431430921319434301)
        ·
          refine ⟨5561562911786595494787863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14830834431430921319434301 5561562911786595494787863)
          ·
            refine ⟨8342344367679893242181795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561562911786595494787863 8342344367679893242181795)
            ·
              refine ⟨12513516551519839863272693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342344367679893242181795 12513516551519839863272693)
              ·
                refine ⟨1173142176704984987181815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12513516551519839863272693 1173142176704984987181815)
                ·
                  refine ⟨1759713265057477480772723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173142176704984987181815 1759713265057477480772723)
                  ·
                    refine ⟨2639569897586216221159085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1759713265057477480772723 2639569897586216221159085)
                    ·
                      refine ⟨989838711594831082934657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639569897586216221159085 989838711594831082934657)
                      ·
                        rfl

theorem cell23_1927704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_1927704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927704 prefixEnd_1927704 := by exact prefixLift 1927704
  have htrace : WordTrace (prefixWord ++ tailWord_1927704) baseStart_1927704 baseEnd_1927704 := by
    simpa [prefixWord, tailWord_1927704, baseEnd_1927704] using wordTrace_append hprefix tailTrace_1927704
  have hstable : (prefixWord ++ tailWord_1927704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927704).length < 2 ^ (prefixWord ++ tailWord_1927704).sum := by decide
  have hdescent : baseEnd_1927704 < baseStart_1927704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927723 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_1927723 : Nat := 118140960795 + 1927723 * 2 ^ 59
def prefixEnd_1927723 : Nat := 4983230072969 + 3 ^ 40 * 1927723 * 2
def baseEnd_1927723 : Nat := 989848467727266508597069

theorem tailTrace_1927723 : CollatzResearch.WordTrace tailWord_1927723 prefixEnd_1927723 989848467727266508597069 := by
  unfold tailWord_1927723
  simp only [CollatzResearch.WordTrace]
  refine ⟨70309833995196274722259823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46873222663464183148173215 70309833995196274722259823)
  ·
    refine ⟨105464750992794412083389735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70309833995196274722259823 105464750992794412083389735)
    ·
      refine ⟨158197126489191618125084603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105464750992794412083389735 158197126489191618125084603)
      ·
        refine ⟨237295689733787427187626905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158197126489191618125084603 237295689733787427187626905)
        ·
          refine ⟨177971767300340570390720179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237295689733787427187626905 177971767300340570390720179)
          ·
            refine ⟨266957650950510855586080269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177971767300340570390720179 266957650950510855586080269)
            ·
              refine ⟨100109119106441570844780101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266957650950510855586080269 100109119106441570844780101)
              ·
                refine ⟨18770459832457794533396269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100109119106441570844780101 18770459832457794533396269)
                ·
                  refine ⟨7038922437171672950023601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18770459832457794533396269 7038922437171672950023601)
                  ·
                    refine ⟨5279191827878754712517701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038922437171672950023601 5279191827878754712517701)
                    ·
                      refine ⟨989848467727266508597069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5279191827878754712517701 989848467727266508597069)
                      ·
                        rfl

theorem cell23_1927723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_1927723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927723 prefixEnd_1927723 := by exact prefixLift 1927723
  have htrace : WordTrace (prefixWord ++ tailWord_1927723) baseStart_1927723 baseEnd_1927723 := by
    simpa [prefixWord, tailWord_1927723, baseEnd_1927723] using wordTrace_append hprefix tailTrace_1927723
  have hstable : (prefixWord ++ tailWord_1927723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927723).length < 2 ^ (prefixWord ++ tailWord_1927723).sum := by decide
  have hdescent : baseEnd_1927723 < baseStart_1927723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927730 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1927730 : Nat := 118140960795 + 1927730 * 2 ^ 59
def prefixEnd_1927730 : Nat := 4983230072969 + 3 ^ 40 * 1927730 * 2
def baseEnd_1927730 : Nat := 989852062091847981209537

theorem tailTrace_1927730 : CollatzResearch.WordTrace tailWord_1927730 prefixEnd_1927730 989852062091847981209537 := by
  unfold tailWord_1927730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17577522326542728729441161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46873392870780609945176429 17577522326542728729441161)
  ·
    refine ⟨13183141744907046547080871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17577522326542728729441161 13183141744907046547080871)
    ·
      refine ⟨19774712617360569820621307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183141744907046547080871 19774712617360569820621307)
      ·
        refine ⟨29662068926040854730931961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774712617360569820621307 29662068926040854730931961)
        ·
          refine ⟨22246551694530641048198971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29662068926040854730931961 22246551694530641048198971)
          ·
            refine ⟨33369827541795961572298457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246551694530641048198971 33369827541795961572298457)
            ·
              refine ⟨25027370656346971179223843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33369827541795961572298457 25027370656346971179223843)
              ·
                refine ⟨37541055984520456768835765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25027370656346971179223843 37541055984520456768835765)
                ·
                  refine ⟨3519473998548792822078353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37541055984520456768835765 3519473998548792822078353)
                  ·
                    refine ⟨2639605498911594616558765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519473998548792822078353 2639605498911594616558765)
                    ·
                      refine ⟨989852062091847981209537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639605498911594616558765 989852062091847981209537)
                      ·
                        rfl

theorem cell23_1927730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1927730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927730 prefixEnd_1927730 := by exact prefixLift 1927730
  have htrace : WordTrace (prefixWord ++ tailWord_1927730) baseStart_1927730 baseEnd_1927730 := by
    simpa [prefixWord, tailWord_1927730, baseEnd_1927730] using wordTrace_append hprefix tailTrace_1927730
  have hstable : (prefixWord ++ tailWord_1927730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927730).length < 2 ^ (prefixWord ++ tailWord_1927730).sum := by decide
  have hdescent : baseEnd_1927730 < baseStart_1927730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927733 : List Nat := [1, 3, 3, 1, 1, 2, 2, 10]
def baseStart_1927733 : Nat := 118140960795 + 1927733 * 2 ^ 59
def prefixEnd_1927733 : Nat := 4983230072969 + 3 ^ 40 * 1927733 * 2
def baseEnd_1927733 : Nat := 36661244538289313684149

theorem tailTrace_1927733 : CollatzResearch.WordTrace tailWord_1927733 prefixEnd_1927733 36661244538289313684149 := by
  unfold tailWord_1927733
  simp only [CollatzResearch.WordTrace]
  refine ⟨70310198725160046430123853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46873465816773364286749235 70310198725160046430123853)
  ·
    refine ⟨26366324521935017411296445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70310198725160046430123853 26366324521935017411296445)
    ·
      refine ⟨9887371695725631529236167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26366324521935017411296445 9887371695725631529236167)
      ·
        refine ⟨14831057543588447293854251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887371695725631529236167 14831057543588447293854251)
        ·
          refine ⟨22246586315382670940781377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831057543588447293854251 22246586315382670940781377)
          ·
            refine ⟨16684939736537003205586033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22246586315382670940781377 16684939736537003205586033)
            ·
              refine ⟨12513704802402752404189525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684939736537003205586033 12513704802402752404189525)
              ·
                refine ⟨36661244538289313684149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12513704802402752404189525 36661244538289313684149)
                ·
                  rfl

theorem cell23_1927733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 10].length) (baseStart_1927733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927733 prefixEnd_1927733 := by exact prefixLift 1927733
  have htrace : WordTrace (prefixWord ++ tailWord_1927733) baseStart_1927733 baseEnd_1927733 := by
    simpa [prefixWord, tailWord_1927733, baseEnd_1927733] using wordTrace_append hprefix tailTrace_1927733
  have hstable : (prefixWord ++ tailWord_1927733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927733).length < 2 ^ (prefixWord ++ tailWord_1927733).sum := by decide
  have hdescent : baseEnd_1927733 < baseStart_1927733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927740 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1927740 : Nat := 118140960795 + 1927740 * 2 ^ 59
def prefixEnd_1927740 : Nat := 4983230072969 + 3 ^ 40 * 1927740 * 2
def baseEnd_1927740 : Nat := 989857196898392942084491

theorem tailTrace_1927740 : CollatzResearch.WordTrace tailWord_1927740 prefixEnd_1927740 989857196898392942084491 := by
  unfold tailWord_1927740
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155227018067343312814337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46873636024089791083752449 35155227018067343312814337)
  ·
    refine ⟨26366420263550507484610753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35155227018067343312814337 26366420263550507484610753)
    ·
      refine ⟨19774815197662880613458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26366420263550507484610753 19774815197662880613458065)
      ·
        refine ⟨14831111398247160460093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19774815197662880613458065 14831111398247160460093549)
        ·
          refine ⟨5561666774342685172535081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14831111398247160460093549 5561666774342685172535081)
          ·
            refine ⟨4171250080757013879401311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561666774342685172535081 4171250080757013879401311)
            ·
              refine ⟨6256875121135520819101967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171250080757013879401311 6256875121135520819101967)
              ·
                refine ⟨9385312681703281228652951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256875121135520819101967 9385312681703281228652951)
                ·
                  refine ⟨14077969022554921842979427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9385312681703281228652951 14077969022554921842979427)
                  ·
                    refine ⟨21116953533832382764469141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14077969022554921842979427 21116953533832382764469141)
                    ·
                      refine ⟨989857196898392942084491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21116953533832382764469141 989857196898392942084491)
                      ·
                        rfl

theorem cell23_1927740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1927740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927740 prefixEnd_1927740 := by exact prefixLift 1927740
  have htrace : WordTrace (prefixWord ++ tailWord_1927740) baseStart_1927740 baseEnd_1927740 := by
    simpa [prefixWord, tailWord_1927740, baseEnd_1927740] using wordTrace_append hprefix tailTrace_1927740
  have hstable : (prefixWord ++ tailWord_1927740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927740).length < 2 ^ (prefixWord ++ tailWord_1927740).sum := by decide
  have hdescent : baseEnd_1927740 < baseStart_1927740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927761 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_1927761 : Nat := 118140960795 + 1927761 * 2 ^ 59
def prefixEnd_1927761 : Nat := 4983230072969 + 3 ^ 40 * 1927761 * 2
def baseEnd_1927761 : Nat := 989867979992137359921895

theorem tailTrace_1927761 : CollatzResearch.WordTrace tailWord_1927761 prefixEnd_1927761 989867979992137359921895 := by
  unfold tailWord_1927761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70311219969058607212143137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46874146646039071474762091 70311219969058607212143137)
  ·
    refine ⟨52733414976793955409107353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70311219969058607212143137 52733414976793955409107353)
    ·
      refine ⟨39550061232595466556830515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52733414976793955409107353 39550061232595466556830515)
      ·
        refine ⟨59325091848893199835245773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39550061232595466556830515 59325091848893199835245773)
        ·
          refine ⟨22246909443334949938217165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59325091848893199835245773 22246909443334949938217165)
          ·
            refine ⟨8342591041250606226831437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22246909443334949938217165 8342591041250606226831437)
            ·
              refine ⟨3128471640468977335061789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8342591041250606226831437 3128471640468977335061789)
              ·
                refine ⟨1173176865175866500648171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3128471640468977335061789 1173176865175866500648171)
                ·
                  refine ⟨1759765297763799750972257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173176865175866500648171 1759765297763799750972257)
                  ·
                    refine ⟨1319823973322849813229193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759765297763799750972257 1319823973322849813229193)
                    ·
                      refine ⟨989867979992137359921895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319823973322849813229193 989867979992137359921895)
                      ·
                        rfl

theorem cell23_1927761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_1927761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927761 prefixEnd_1927761 := by exact prefixLift 1927761
  have htrace : WordTrace (prefixWord ++ tailWord_1927761) baseStart_1927761 baseEnd_1927761 := by
    simpa [prefixWord, tailWord_1927761, baseEnd_1927761] using wordTrace_append hprefix tailTrace_1927761
  have hstable : (prefixWord ++ tailWord_1927761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927761).length < 2 ^ (prefixWord ++ tailWord_1927761).sum := by decide
  have hdescent : baseEnd_1927761 < baseStart_1927761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927777 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1927777 : Nat := 118140960795 + 1927777 * 2 ^ 59
def prefixEnd_1927777 : Nat := 4983230072969 + 3 ^ 40 * 1927777 * 2
def baseEnd_1927777 : Nat := 989876195682609297321821

theorem tailTrace_1927777 : CollatzResearch.WordTrace tailWord_1927777 prefixEnd_1927777 989876195682609297321821 := by
  unfold tailWord_1927777
  simp only [CollatzResearch.WordTrace]
  refine ⟨70311803537000641944725585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46874535691333761296483723 70311803537000641944725585)
  ·
    refine ⟨52733852652750481458544189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70311803537000641944725585 52733852652750481458544189)
    ·
      refine ⟨19775194744781430546954071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52733852652750481458544189 19775194744781430546954071)
      ·
        refine ⟨29662792117172145820431107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19775194744781430546954071 29662792117172145820431107)
        ·
          refine ⟨44494188175758218730646661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29662792117172145820431107 44494188175758218730646661)
          ·
            refine ⟨8342660282954666011996249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44494188175758218730646661 8342660282954666011996249)
            ·
              refine ⟨6256995212215999508997187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342660282954666011996249 6256995212215999508997187)
              ·
                refine ⟨9385492818323999263495781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256995212215999508997187 9385492818323999263495781)
                ·
                  refine ⟨1759779903435749861905459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9385492818323999263495781 1759779903435749861905459)
                  ·
                    refine ⟨2639669855153624792858189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1759779903435749861905459 2639669855153624792858189)
                    ·
                      refine ⟨989876195682609297321821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639669855153624792858189 989876195682609297321821)
                      ·
                        rfl

theorem cell23_1927777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1927777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927777 prefixEnd_1927777 := by exact prefixLift 1927777
  have htrace : WordTrace (prefixWord ++ tailWord_1927777) baseStart_1927777 baseEnd_1927777 := by
    simpa [prefixWord, tailWord_1927777, baseEnd_1927777] using wordTrace_append hprefix tailTrace_1927777
  have hstable : (prefixWord ++ tailWord_1927777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927777).length < 2 ^ (prefixWord ++ tailWord_1927777).sum := by decide
  have hdescent : baseEnd_1927777 < baseStart_1927777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927798 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1927798 : Nat := 118140960795 + 1927798 * 2 ^ 59
def prefixEnd_1927798 : Nat := 4983230072969 + 3 ^ 40 * 1927798 * 2
def baseEnd_1927798 : Nat := 989886978776353715159225

theorem tailTrace_1927798 : CollatzResearch.WordTrace tailWord_1927798 prefixEnd_1927798 989886978776353715159225 := by
  unfold tailWord_1927798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394535591870285158202503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46875046313283041687493365 4394535591870285158202503)
  ·
    refine ⟨6591803387805427737303755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394535591870285158202503 6591803387805427737303755)
    ·
      refine ⟨9887705081708141605955633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591803387805427737303755 9887705081708141605955633)
      ·
        refine ⟨7415778811281106204466725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887705081708141605955633 7415778811281106204466725)
        ·
          refine ⟨1390458527115207413337511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7415778811281106204466725 1390458527115207413337511)
          ·
            refine ⟨2085687790672811120006267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390458527115207413337511 2085687790672811120006267)
            ·
              refine ⟨3128531686009216680009401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085687790672811120006267 3128531686009216680009401)
              ·
                refine ⟨2346398764506912510007051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128531686009216680009401 2346398764506912510007051)
                ·
                  refine ⟨3519598146760368765010577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346398764506912510007051 3519598146760368765010577)
                  ·
                    refine ⟨2639698610070276573757933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519598146760368765010577 2639698610070276573757933)
                    ·
                      refine ⟨989886978776353715159225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639698610070276573757933 989886978776353715159225)
                      ·
                        rfl

theorem cell23_1927798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1927798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927798 prefixEnd_1927798 := by exact prefixLift 1927798
  have htrace : WordTrace (prefixWord ++ tailWord_1927798) baseStart_1927798 baseEnd_1927798 := by
    simpa [prefixWord, tailWord_1927798, baseEnd_1927798] using wordTrace_append hprefix tailTrace_1927798
  have hstable : (prefixWord ++ tailWord_1927798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927798).length < 2 ^ (prefixWord ++ tailWord_1927798).sum := by decide
  have hdescent : baseEnd_1927798 < baseStart_1927798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927804 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_1927804 : Nat := 118140960795 + 1927804 * 2 ^ 59
def prefixEnd_1927804 : Nat := 4983230072969 + 3 ^ 40 * 1927804 * 2
def baseEnd_1927804 : Nat := 989890059660280691684197

theorem tailTrace_1927804 : CollatzResearch.WordTrace tailWord_1927804 prefixEnd_1927804 989890059660280691684197 := by
  unfold tailWord_1927804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156394153951412777979233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46875192205268550370638977 35156394153951412777979233)
  ·
    refine ⟨26367295615463559583484425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35156394153951412777979233 26367295615463559583484425)
    ·
      refine ⟨19775471711597669687613319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26367295615463559583484425 19775471711597669687613319)
      ·
        refine ⟨29663207567396504531419979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19775471711597669687613319 29663207567396504531419979)
        ·
          refine ⟨44494811351094756797129969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29663207567396504531419979 44494811351094756797129969)
          ·
            refine ⟨33371108513321067597847477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44494811351094756797129969 33371108513321067597847477)
            ·
              refine ⟨3128541423123850087298201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33371108513321067597847477 3128541423123850087298201)
              ·
                refine ⟨2346406067342887565473651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128541423123850087298201 2346406067342887565473651)
                ·
                  refine ⟨3519609101014331348210477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346406067342887565473651 3519609101014331348210477)
                  ·
                    refine ⟨1319853412880374255578929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3519609101014331348210477 1319853412880374255578929)
                    ·
                      refine ⟨989890059660280691684197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319853412880374255578929 989890059660280691684197)
                      ·
                        rfl

theorem cell23_1927804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_1927804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927804 prefixEnd_1927804 := by exact prefixLift 1927804
  have htrace : WordTrace (prefixWord ++ tailWord_1927804) baseStart_1927804 baseEnd_1927804 := by
    simpa [prefixWord, tailWord_1927804, baseEnd_1927804] using wordTrace_append hprefix tailTrace_1927804
  have hstable : (prefixWord ++ tailWord_1927804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927804).length < 2 ^ (prefixWord ++ tailWord_1927804).sum := by decide
  have hdescent : baseEnd_1927804 < baseStart_1927804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927823 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 9]
def baseStart_1927823 : Nat := 118140960795 + 1927823 * 2 ^ 59
def prefixEnd_1927823 : Nat := 4983230072969 + 3 ^ 40 * 1927823 * 2
def baseEnd_1927823 : Nat := 109988868421412901927401

theorem tailTrace_1927823 : CollatzResearch.WordTrace tailWord_1927823 prefixEnd_1927823 109988868421412901927401 := by
  unfold tailWord_1927823
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313481294833991800900123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46875654196555994533933415 70313481294833991800900123)
  ·
    refine ⟨105470221942250987701350185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70313481294833991800900123 105470221942250987701350185)
    ·
      refine ⟨79102666456688240776012639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105470221942250987701350185 79102666456688240776012639)
      ·
        refine ⟨118653999685032361164018959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79102666456688240776012639 118653999685032361164018959)
        ·
          refine ⟨177980999527548541746028439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118653999685032361164018959 177980999527548541746028439)
          ·
            refine ⟨266971499291322812619042659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177980999527548541746028439 266971499291322812619042659)
            ·
              refine ⟨400457248936984218928563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266971499291322812619042659 400457248936984218928563989)
              ·
                refine ⟨18771433543921135262276437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 400457248936984218928563989 18771433543921135262276437)
                ·
                  refine ⟨109988868421412901927401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18771433543921135262276437 109988868421412901927401)
                  ·
                    rfl

theorem cell23_1927823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 9].length) (baseStart_1927823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927823 prefixEnd_1927823 := by exact prefixLift 1927823
  have htrace : WordTrace (prefixWord ++ tailWord_1927823) baseStart_1927823 baseEnd_1927823 := by
    simpa [prefixWord, tailWord_1927823, baseEnd_1927823] using wordTrace_append hprefix tailTrace_1927823
  have hstable : (prefixWord ++ tailWord_1927823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927823).length < 2 ^ (prefixWord ++ tailWord_1927823).sum := by decide
  have hdescent : baseEnd_1927823 < baseStart_1927823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927907 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1927907 : Nat := 118140960795 + 1927907 * 2 ^ 59
def prefixEnd_1927907 : Nat := 4983230072969 + 3 ^ 40 * 1927907 * 2
def baseEnd_1927907 : Nat := 989942948167693788696223

theorem tailTrace_1927907 : CollatzResearch.WordTrace tailWord_1927907 prefixEnd_1927907 989942948167693788696223 := by
  unfold tailWord_1927907
  simp only [CollatzResearch.WordTrace]
  refine ⟨70316545026529674146957975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46877696684353116097971983 70316545026529674146957975)
  ·
    refine ⟨105474817539794511220436963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70316545026529674146957975 105474817539794511220436963)
    ·
      refine ⟨158212226309691766830655445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105474817539794511220436963 158212226309691766830655445)
      ·
        refine ⟨3708099054133400785093487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 158212226309691766830655445 3708099054133400785093487)
        ·
          refine ⟨5562148581200101177640231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708099054133400785093487 5562148581200101177640231)
          ·
            refine ⟨8343222871800151766460347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562148581200101177640231 8343222871800151766460347)
            ·
              refine ⟨12514834307700227649690521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343222871800151766460347 12514834307700227649690521)
              ·
                refine ⟨9386125730775170737267891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12514834307700227649690521 9386125730775170737267891)
                ·
                  refine ⟨14079188596162756105901837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386125730775170737267891 14079188596162756105901837)
                  ·
                    refine ⟨5279695723561033539713189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14079188596162756105901837 5279695723561033539713189)
                    ·
                      refine ⟨989942948167693788696223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5279695723561033539713189 989942948167693788696223)
                      ·
                        rfl

theorem cell23_1927907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1927907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927907 prefixEnd_1927907 := by exact prefixLift 1927907
  have htrace : WordTrace (prefixWord ++ tailWord_1927907) baseStart_1927907 baseEnd_1927907 := by
    simpa [prefixWord, tailWord_1927907, baseEnd_1927907] using wordTrace_append hprefix tailTrace_1927907
  have hstable : (prefixWord ++ tailWord_1927907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927907).length < 2 ^ (prefixWord ++ tailWord_1927907).sum := by decide
  have hdescent : baseEnd_1927907 < baseStart_1927907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927920 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1927920 : Nat := 118140960795 + 1927920 * 2 ^ 59
def prefixEnd_1927920 : Nat := 4983230072969 + 3 ^ 40 * 1927920 * 2
def baseEnd_1927920 : Nat := 989949623416202237833663

theorem tailTrace_1927920 : CollatzResearch.WordTrace tailWord_1927920 prefixEnd_1927920 989949623416202237833663 := by
  unfold tailWord_1927920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158509587741288683590607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46878012783655051578120809 35158509587741288683590607)
  ·
    refine ⟨52737764381611933025385911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35158509587741288683590607 52737764381611933025385911)
    ·
      refine ⟨79106646572417899538078867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52737764381611933025385911 79106646572417899538078867)
      ·
        refine ⟨118659969858626849307118301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79106646572417899538078867 118659969858626849307118301)
        ·
          refine ⟨44497488696985068490169363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118659969858626849307118301 44497488696985068490169363)
          ·
            refine ⟨66746233045477602735254045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44497488696985068490169363 66746233045477602735254045)
            ·
              refine ⟨25029837392054101025720267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66746233045477602735254045 25029837392054101025720267)
              ·
                refine ⟨37544756088081151538580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25029837392054101025720267 37544756088081151538580401)
                ·
                  refine ⟨28158567066060863653935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37544756088081151538580401 28158567066060863653935301)
                  ·
                    refine ⟨5279731324886411935112869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28158567066060863653935301 5279731324886411935112869)
                    ·
                      refine ⟨989949623416202237833663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5279731324886411935112869 989949623416202237833663)
                      ·
                        rfl

theorem cell23_1927920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1927920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927920 prefixEnd_1927920 := by exact prefixLift 1927920
  have htrace : WordTrace (prefixWord ++ tailWord_1927920) baseStart_1927920 baseEnd_1927920 := by
    simpa [prefixWord, tailWord_1927920, baseEnd_1927920] using wordTrace_append hprefix tailTrace_1927920
  have hstable : (prefixWord ++ tailWord_1927920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927920).length < 2 ^ (prefixWord ++ tailWord_1927920).sum := by decide
  have hdescent : baseEnd_1927920 < baseStart_1927920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927925 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 5]
def baseStart_1927925 : Nat := 118140960795 + 1927925 * 2 ^ 59
def prefixEnd_1927925 : Nat := 4983230072969 + 3 ^ 40 * 1927925 * 2
def baseEnd_1927925 : Nat := 109994687868830524252349

theorem tailTrace_1927925 : CollatzResearch.WordTrace tailWord_1927925 prefixEnd_1927925 109994687868830524252349 := by
  unfold tailWord_1927925
  simp only [CollatzResearch.WordTrace]
  refine ⟨70317201540464463221113229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46878134360309642147408819 70317201540464463221113229)
  ·
    refine ⟨26368950577674173707917461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70317201540464463221113229 26368950577674173707917461)
    ·
      refine ⟨1236044558328476892558631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26368950577674173707917461 1236044558328476892558631)
      ·
        refine ⟨1854066837492715338837947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236044558328476892558631 1854066837492715338837947)
        ·
          refine ⟨2781100256239073008256921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854066837492715338837947 2781100256239073008256921)
          ·
            refine ⟨2085825192179304756192691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781100256239073008256921 2085825192179304756192691)
            ·
              refine ⟨3128737788268957134289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085825192179304756192691 3128737788268957134289037)
              ·
                refine ⟨1173276670600858925358389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3128737788268957134289037 1173276670600858925358389)
                ·
                  refine ⟨109994687868830524252349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173276670600858925358389 109994687868830524252349)
                  ·
                    rfl

theorem cell23_1927925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_1927925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927925 prefixEnd_1927925 := by exact prefixLift 1927925
  have htrace : WordTrace (prefixWord ++ tailWord_1927925) baseStart_1927925 baseEnd_1927925 := by
    simpa [prefixWord, tailWord_1927925, baseEnd_1927925] using wordTrace_append hprefix tailTrace_1927925
  have hstable : (prefixWord ++ tailWord_1927925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927925).length < 2 ^ (prefixWord ++ tailWord_1927925).sum := by decide
  have hdescent : baseEnd_1927925 < baseStart_1927925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927927 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1927927 : Nat := 118140960795 + 1927927 * 2 ^ 59
def prefixEnd_1927927 : Nat := 4983230072969 + 3 ^ 40 * 1927927 * 2
def baseEnd_1927927 : Nat := 989953217780783710446131

theorem tailTrace_1927927 : CollatzResearch.WordTrace tailWord_1927927 prefixEnd_1927927 989953217780783710446131 := by
  unfold tailWord_1927927
  simp only [CollatzResearch.WordTrace]
  refine ⟨70317274486457217562686035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46878182990971478375124023 70317274486457217562686035)
  ·
    refine ⟨105475911729685826344029053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70317274486457217562686035 105475911729685826344029053)
    ·
      refine ⟨39553466898632184879010895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105475911729685826344029053 39553466898632184879010895)
      ·
        refine ⟨59330200347948277318516343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39553466898632184879010895 59330200347948277318516343)
        ·
          refine ⟨88995300521922415977774515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59330200347948277318516343 88995300521922415977774515)
          ·
            refine ⟨133492950782883623966661773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88995300521922415977774515 133492950782883623966661773)
            ·
              refine ⟨50059856543581358987498165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133492950782883623966661773 50059856543581358987498165)
              ·
                refine ⟨4693111550960752405077953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50059856543581358987498165 4693111550960752405077953)
                ·
                  refine ⟨3519833663220564303808465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693111550960752405077953 3519833663220564303808465)
                  ·
                    refine ⟨2639875247415423227856349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519833663220564303808465 2639875247415423227856349)
                    ·
                      refine ⟨989953217780783710446131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639875247415423227856349 989953217780783710446131)
                      ·
                        rfl

theorem cell23_1927927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1927927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927927 prefixEnd_1927927 := by exact prefixLift 1927927
  have htrace : WordTrace (prefixWord ++ tailWord_1927927) baseStart_1927927 baseEnd_1927927 := by
    simpa [prefixWord, tailWord_1927927, baseEnd_1927927] using wordTrace_append hprefix tailTrace_1927927
  have hstable : (prefixWord ++ tailWord_1927927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927927).length < 2 ^ (prefixWord ++ tailWord_1927927).sum := by decide
  have hdescent : baseEnd_1927927 < baseStart_1927927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927930 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_1927930 : Nat := 118140960795 + 1927930 * 2 ^ 59
def prefixEnd_1927930 : Nat := 4983230072969 + 3 ^ 40 * 1927930 * 2
def baseEnd_1927930 : Nat := 109994973135860799856513

theorem tailTrace_1927930 : CollatzResearch.WordTrace tailWord_1927930 prefixEnd_1927930 109994973135860799856513 := by
  unfold tailWord_1927930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579345976361587268761311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46878255936964232716696829 17579345976361587268761311)
  ·
    refine ⟨26369018964542380903141967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579345976361587268761311 26369018964542380903141967)
    ·
      refine ⟨39553528446813571354712951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26369018964542380903141967 39553528446813571354712951)
      ·
        refine ⟨59330292670220357032069427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39553528446813571354712951 59330292670220357032069427)
        ·
          refine ⟨88995439005330535548104141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59330292670220357032069427 88995439005330535548104141)
          ·
            refine ⟨33373289626998950830539053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88995439005330535548104141 33373289626998950830539053)
            ·
              refine ⟨12514983610124606561452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33373289626998950830539053 12514983610124606561452145)
              ·
                refine ⟨9386237707593454921089109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12514983610124606561452145 9386237707593454921089109)
                ·
                  refine ⟨109994973135860799856513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9386237707593454921089109 109994973135860799856513)
                  ·
                    rfl

theorem cell23_1927930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_1927930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927930 prefixEnd_1927930 := by exact prefixLift 1927930
  have htrace : WordTrace (prefixWord ++ tailWord_1927930) baseStart_1927930 baseEnd_1927930 := by
    simpa [prefixWord, tailWord_1927930, baseEnd_1927930] using wordTrace_append hprefix tailTrace_1927930
  have hstable : (prefixWord ++ tailWord_1927930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927930).length < 2 ^ (prefixWord ++ tailWord_1927930).sum := by decide
  have hdescent : baseEnd_1927930 < baseStart_1927930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927944 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1927944 : Nat := 118140960795 + 1927944 * 2 ^ 59
def prefixEnd_1927944 : Nat := 4983230072969 + 3 ^ 40 * 1927944 * 2
def baseEnd_1927944 : Nat := 989961946951910143933553

theorem tailTrace_1927944 : CollatzResearch.WordTrace tailWord_1927944 prefixEnd_1927944 989961946951910143933553 := by
  unfold tailWord_1927944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158947263697814733027443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46878596351597086310703257 35158947263697814733027443)
  ·
    refine ⟨52738420895546722099541165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35158947263697814733027443 52738420895546722099541165)
    ·
      refine ⟨19776907835830020787327937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52738420895546722099541165 19776907835830020787327937)
      ·
        refine ⟨14832680876872515590495953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19776907835830020787327937 14832680876872515590495953)
        ·
          refine ⟨11124510657654386692871965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14832680876872515590495953 11124510657654386692871965)
          ·
            refine ⟨4171691496620395009826987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11124510657654386692871965 4171691496620395009826987)
            ·
              refine ⟨6257537244930592514740481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171691496620395009826987 6257537244930592514740481)
              ·
                refine ⟨4693152933697944386055361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257537244930592514740481 4693152933697944386055361)
                ·
                  refine ⟨3519864700273458289541521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693152933697944386055361 3519864700273458289541521)
                  ·
                    refine ⟨2639898525205093717156141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519864700273458289541521 2639898525205093717156141)
                    ·
                      refine ⟨989961946951910143933553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639898525205093717156141 989961946951910143933553)
                      ·
                        rfl

theorem cell23_1927944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1927944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927944 prefixEnd_1927944 := by exact prefixLift 1927944
  have htrace : WordTrace (prefixWord ++ tailWord_1927944) baseStart_1927944 baseEnd_1927944 := by
    simpa [prefixWord, tailWord_1927944, baseEnd_1927944] using wordTrace_append hprefix tailTrace_1927944
  have hstable : (prefixWord ++ tailWord_1927944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927944).length < 2 ^ (prefixWord ++ tailWord_1927944).sum := by decide
  have hdescent : baseEnd_1927944 < baseStart_1927944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927951 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 1, 4]
def baseStart_1927951 : Nat := 118140960795 + 1927951 * 2 ^ 59
def prefixEnd_1927951 : Nat := 4983230072969 + 3 ^ 40 * 1927951 * 2
def baseEnd_1927951 : Nat := 329988513772163872182007

theorem tailTrace_1927951 : CollatzResearch.WordTrace tailWord_1927951 prefixEnd_1927951 329988513772163872182007 := by
  unfold tailWord_1927951
  simp only [CollatzResearch.WordTrace]
  refine ⟨70318149838370269661559707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46878766558913513107706471 70318149838370269661559707)
  ·
    refine ⟨105477224757555404492339561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70318149838370269661559707 105477224757555404492339561)
    ·
      refine ⟨79107918568166553369254671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105477224757555404492339561 79107918568166553369254671)
      ·
        refine ⟨118661877852249830053882007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79107918568166553369254671 118661877852249830053882007)
        ·
          refine ⟨177992816778374745080823011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118661877852249830053882007 177992816778374745080823011)
          ·
            refine ⟨266989225167562117621234517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177992816778374745080823011 266989225167562117621234517)
            ·
              refine ⟨1564389991216184282936921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 266989225167562117621234517 1564389991216184282936921)
              ·
                refine ⟨1173292493412138212202691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564389991216184282936921 1173292493412138212202691)
                ·
                  refine ⟨1759938740118207318304037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173292493412138212202691 1759938740118207318304037)
                  ·
                    refine ⟨329988513772163872182007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759938740118207318304037 329988513772163872182007)
                    ·
                      rfl

theorem cell23_1927951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_1927951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927951 prefixEnd_1927951 := by exact prefixLift 1927951
  have htrace : WordTrace (prefixWord ++ tailWord_1927951) baseStart_1927951 baseEnd_1927951 := by
    simpa [prefixWord, tailWord_1927951, baseEnd_1927951] using wordTrace_append hprefix tailTrace_1927951
  have hstable : (prefixWord ++ tailWord_1927951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927951).length < 2 ^ (prefixWord ++ tailWord_1927951).sum := by decide
  have hdescent : baseEnd_1927951 < baseStart_1927951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927960 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1927960 : Nat := 118140960795 + 1927960 * 2 ^ 59
def prefixEnd_1927960 : Nat := 4983230072969 + 3 ^ 40 * 1927960 * 2
def baseEnd_1927960 : Nat := 329990054214127360444493

theorem tailTrace_1927960 : CollatzResearch.WordTrace tailWord_1927960 prefixEnd_1927960 329990054214127360444493 := by
  unfold tailWord_1927960
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159239047668832099318667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46878985396891776132424889 35159239047668832099318667)
  ·
    refine ⟨52738858571503248148978001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35159239047668832099318667 52738858571503248148978001)
    ·
      refine ⟨39554143928627436111733501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52738858571503248148978001 39554143928627436111733501)
      ·
        refine ⟨14832803973235288541900063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39554143928627436111733501 14832803973235288541900063)
        ·
          refine ⟨22249205959852932812850095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832803973235288541900063 22249205959852932812850095)
          ·
            refine ⟨33373808939779399219275143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22249205959852932812850095 33373808939779399219275143)
            ·
              refine ⟨50060713409669098828912715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33373808939779399219275143 50060713409669098828912715)
              ·
                refine ⟨75091070114503648243369073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50060713409669098828912715 75091070114503648243369073)
                ·
                  refine ⟨56318302585877736182526805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75091070114503648243369073 56318302585877736182526805)
                  ·
                    refine ⟨329990054214127360444493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56318302585877736182526805 329990054214127360444493)
                    ·
                      rfl

theorem cell23_1927960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1927960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927960 prefixEnd_1927960 := by exact prefixLift 1927960
  have htrace : WordTrace (prefixWord ++ tailWord_1927960) baseStart_1927960 baseEnd_1927960 := by
    simpa [prefixWord, tailWord_1927960, baseEnd_1927960] using wordTrace_append hprefix tailTrace_1927960
  have hstable : (prefixWord ++ tailWord_1927960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927960).length < 2 ^ (prefixWord ++ tailWord_1927960).sum := by decide
  have hdescent : baseEnd_1927960 < baseStart_1927960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927964 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 6]
def baseStart_1927964 : Nat := 118140960795 + 1927964 * 2 ^ 59
def prefixEnd_1927964 : Nat := 4983230072969 + 3 ^ 40 * 1927964 * 2
def baseEnd_1927964 : Nat := 109996912951666673964829

theorem tailTrace_1927964 : CollatzResearch.WordTrace tailWord_1927964 prefixEnd_1927964 109996912951666673964829 := by
  unfold tailWord_1927964
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159311993661586440891473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46879082658215448587855297 35159311993661586440891473)
  ·
    refine ⟨26369483995246189830668605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35159311993661586440891473 26369483995246189830668605)
    ·
      refine ⟨9888556498217321186500727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26369483995246189830668605 9888556498217321186500727)
      ·
        refine ⟨14832834747325981779751091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9888556498217321186500727 14832834747325981779751091)
        ·
          refine ⟨22249252120988972669626637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832834747325981779751091 22249252120988972669626637)
          ·
            refine ⟨8343469545370864751109989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22249252120988972669626637 8343469545370864751109989)
            ·
              refine ⟨1564400539757037140833123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8343469545370864751109989 1564400539757037140833123)
              ·
                refine ⟨2346600809635555711249685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564400539757037140833123 2346600809635555711249685)
                ·
                  refine ⟨109996912951666673964829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2346600809635555711249685 109996912951666673964829)
                  ·
                    rfl

theorem cell23_1927964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_1927964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927964 prefixEnd_1927964 := by exact prefixLift 1927964
  have htrace : WordTrace (prefixWord ++ tailWord_1927964) baseStart_1927964 baseEnd_1927964 := by
    simpa [prefixWord, tailWord_1927964, baseEnd_1927964] using wordTrace_append hprefix tailTrace_1927964
  have hstable : (prefixWord ++ tailWord_1927964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927964).length < 2 ^ (prefixWord ++ tailWord_1927964).sum := by decide
  have hdescent : baseEnd_1927964 < baseStart_1927964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927978 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1927978 : Nat := 118140960795 + 1927978 * 2 ^ 59
def prefixEnd_1927978 : Nat := 4983230072969 + 3 ^ 40 * 1927978 * 2
def baseEnd_1927978 : Nat := 989979405294163010908397

theorem tailTrace_1927978 : CollatzResearch.WordTrace tailWord_1927978 prefixEnd_1927978 989979405294163010908397 := by
  unfold tailWord_1927978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579783652318113318198147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46879423072848302181861725 17579783652318113318198147)
  ·
    refine ⟨26369675478477169977297221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579783652318113318198147 26369675478477169977297221)
    ·
      refine ⟨4944314152214469370743229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26369675478477169977297221 4944314152214469370743229)
      ·
        refine ⟨1854117807080426014028711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944314152214469370743229 1854117807080426014028711)
        ·
          refine ⟨2781176710620639021043067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854117807080426014028711 2781176710620639021043067)
          ·
            refine ⟨4171765065930958531564601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781176710620639021043067 4171765065930958531564601)
            ·
              refine ⟨3128823799448218898673451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171765065930958531564601 3128823799448218898673451)
              ·
                refine ⟨4693235699172328348010177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128823799448218898673451 4693235699172328348010177)
                ·
                  refine ⟨3519926774379246261007633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693235699172328348010177 3519926774379246261007633)
                  ·
                    refine ⟨2639945080784434695755725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519926774379246261007633 2639945080784434695755725)
                    ·
                      refine ⟨989979405294163010908397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639945080784434695755725 989979405294163010908397)
                      ·
                        rfl

theorem cell23_1927978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1927978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927978 prefixEnd_1927978 := by exact prefixLift 1927978
  have htrace : WordTrace (prefixWord ++ tailWord_1927978) baseStart_1927978 baseEnd_1927978 := by
    simpa [prefixWord, tailWord_1927978, baseEnd_1927978] using wordTrace_append hprefix tailTrace_1927978
  have hstable : (prefixWord ++ tailWord_1927978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927978).length < 2 ^ (prefixWord ++ tailWord_1927978).sum := by decide
  have hdescent : baseEnd_1927978 < baseStart_1927978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927991 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_1927991 : Nat := 118140960795 + 1927991 * 2 ^ 59
def prefixEnd_1927991 : Nat := 4983230072969 + 3 ^ 40 * 1927991 * 2
def baseEnd_1927991 : Nat := 989986080542671460045837

theorem tailTrace_1927991 : CollatzResearch.WordTrace tailWord_1927991 prefixEnd_1927991 989986080542671460045837 := by
  unfold tailWord_1927991
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319608758225356493015827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46879739172150237662010551 70319608758225356493015827)
  ·
    refine ⟨105479413137338034739523741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70319608758225356493015827 105479413137338034739523741)
    ·
      refine ⟨39554779926501763027321403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105479413137338034739523741 39554779926501763027321403)
      ·
        refine ⟨59332169889752644540982105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39554779926501763027321403 59332169889752644540982105)
        ·
          refine ⟨44499127417314483405736579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59332169889752644540982105 44499127417314483405736579)
          ·
            refine ⟨66748691125971725108604869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44499127417314483405736579 66748691125971725108604869)
            ·
              refine ⟨12515379586119698457863413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66748691125971725108604869 12515379586119698457863413)
              ·
                refine ⟨1173316836198721730424695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12515379586119698457863413 1173316836198721730424695)
                ·
                  refine ⟨1759975254298082595637043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173316836198721730424695 1759975254298082595637043)
                  ·
                    refine ⟨2639962881447123893455565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1759975254298082595637043 2639962881447123893455565)
                    ·
                      refine ⟨989986080542671460045837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2639962881447123893455565 989986080542671460045837)
                      ·
                        rfl

theorem cell23_1927991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_1927991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927991 prefixEnd_1927991 := by exact prefixLift 1927991
  have htrace : WordTrace (prefixWord ++ tailWord_1927991) baseStart_1927991 baseEnd_1927991 := by
    simpa [prefixWord, tailWord_1927991, baseEnd_1927991] using wordTrace_append hprefix tailTrace_1927991
  have hstable : (prefixWord ++ tailWord_1927991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927991).length < 2 ^ (prefixWord ++ tailWord_1927991).sum := by decide
  have hdescent : baseEnd_1927991 < baseStart_1927991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928031 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 3, 2, 2]
def baseStart_1928031 : Nat := 118140960795 + 1928031 * 2 ^ 59
def prefixEnd_1928031 : Nat := 4983230072969 + 3 ^ 40 * 1928031 * 2
def baseEnd_1928031 : Nat := 990006619768851303545653

theorem tailTrace_1928031 : CollatzResearch.WordTrace tailWord_1928031 prefixEnd_1928031 990006619768851303545653 := by
  unfold tailWord_1928031
  simp only [CollatzResearch.WordTrace]
  refine ⟨70321067678080443324471947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46880711785386962216314631 70321067678080443324471947)
  ·
    refine ⟨105481601517120664986707921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70321067678080443324471947 105481601517120664986707921)
    ·
      refine ⟨79111201137840498740030941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105481601517120664986707921 79111201137840498740030941)
      ·
        refine ⟨29666700426690187027511603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79111201137840498740030941 29666700426690187027511603)
        ·
          refine ⟨44500050640035280541267405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29666700426690187027511603 44500050640035280541267405)
          ·
            refine ⟨16687518990013230202975277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44500050640035280541267405 16687518990013230202975277)
            ·
              refine ⟨6257819621254961326115729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16687518990013230202975277 6257819621254961326115729)
              ·
                refine ⟨4693364715941220994586797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257819621254961326115729 4693364715941220994586797)
                ·
                  refine ⟨1760011768477957872970049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4693364715941220994586797 1760011768477957872970049)
                  ·
                    refine ⟨1320008826358468404727537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760011768477957872970049 1320008826358468404727537)
                    ·
                      refine ⟨990006619768851303545653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320008826358468404727537 990006619768851303545653)
                      ·
                        rfl

theorem cell23_1928031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_1928031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928031 prefixEnd_1928031 := by exact prefixLift 1928031
  have htrace : WordTrace (prefixWord ++ tailWord_1928031) baseStart_1928031 baseEnd_1928031 := by
    simpa [prefixWord, tailWord_1928031, baseEnd_1928031] using wordTrace_append hprefix tailTrace_1928031
  have hstable : (prefixWord ++ tailWord_1928031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928031).length < 2 ^ (prefixWord ++ tailWord_1928031).sum := by decide
  have hdescent : baseEnd_1928031 < baseStart_1928031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928048 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 1, 2, 2]
def baseStart_1928048 : Nat := 118140960795 + 1928048 * 2 ^ 59
def prefixEnd_1928048 : Nat := 4983230072969 + 3 ^ 40 * 1928048 * 2
def baseEnd_1928048 : Nat := 990015348939977737033075

theorem tailTrace_1928048 : CollatzResearch.WordTrace tailWord_1928048 prefixEnd_1928048 990015348939977737033075 := by
  unfold tailWord_1928048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160843859509427613920399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46881125146012570151893865 35160843859509427613920399)
  ·
    refine ⟨52741265789264141420880599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35160843859509427613920399 52741265789264141420880599)
    ·
      refine ⟨79111898683896212131320899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52741265789264141420880599 79111898683896212131320899)
      ·
        refine ⟨118667848025844318196981349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79111898683896212131320899 118667848025844318196981349)
        ·
          refine ⟨22250221504845809661934003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118667848025844318196981349 22250221504845809661934003)
          ·
            refine ⟨33375332257268714492901005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22250221504845809661934003 33375332257268714492901005)
            ·
              refine ⟨12515749596475767934837877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33375332257268714492901005 12515749596475767934837877)
              ·
                refine ⟨1173351524669603243891051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12515749596475767934837877 1173351524669603243891051)
                ·
                  refine ⟨1760027287004404865836577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173351524669603243891051 1760027287004404865836577)
                  ·
                    refine ⟨1320020465253303649377433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760027287004404865836577 1320020465253303649377433)
                    ·
                      refine ⟨990015348939977737033075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320020465253303649377433 990015348939977737033075)
                      ·
                        rfl

theorem cell23_1928048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 2, 2].length) (baseStart_1928048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928048 prefixEnd_1928048 := by exact prefixLift 1928048
  have htrace : WordTrace (prefixWord ++ tailWord_1928048) baseStart_1928048 baseEnd_1928048 := by
    simpa [prefixWord, tailWord_1928048, baseEnd_1928048] using wordTrace_append hprefix tailTrace_1928048
  have hstable : (prefixWord ++ tailWord_1928048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928048).length < 2 ^ (prefixWord ++ tailWord_1928048).sum := by decide
  have hdescent : baseEnd_1928048 < baseStart_1928048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928051 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 1, 2, 3]
def baseStart_1928051 : Nat := 118140960795 + 1928051 * 2 ^ 59
def prefixEnd_1928051 : Nat := 4983230072969 + 3 ^ 40 * 1928051 * 2
def baseEnd_1928051 : Nat := 990016889381941225295561

theorem tailTrace_1928051 : CollatzResearch.WordTrace tailWord_1928051 prefixEnd_1928051 990016889381941225295561 := by
  unfold tailWord_1928051
  simp only [CollatzResearch.WordTrace]
  refine ⟨70321797138007986740200007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46881198092005324493466671 70321797138007986740200007)
  ·
    refine ⟨105482695707011980110300011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70321797138007986740200007 105482695707011980110300011)
    ·
      refine ⟨158224043560517970165450017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105482695707011980110300011 158224043560517970165450017)
      ·
        refine ⟨118668032670388477624087513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158224043560517970165450017 118668032670388477624087513)
        ·
          refine ⟨89001024502791358218065635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118668032670388477624087513 89001024502791358218065635)
          ·
            refine ⟨133501536754187037327098453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89001024502791358218065635 133501536754187037327098453)
            ·
              refine ⟨1564471133838129343676935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 133501536754187037327098453 1564471133838129343676935)
              ·
                refine ⟨2346706700757194015515403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564471133838129343676935 2346706700757194015515403)
                ·
                  refine ⟨3520060051135791023273105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346706700757194015515403 3520060051135791023273105)
                  ·
                    refine ⟨2640045038351843267454829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520060051135791023273105 2640045038351843267454829)
                    ·
                      refine ⟨990016889381941225295561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2640045038351843267454829 990016889381941225295561)
                      ·
                        rfl

theorem cell23_1928051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 2, 3].length) (baseStart_1928051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928051 prefixEnd_1928051 := by exact prefixLift 1928051
  have htrace : WordTrace (prefixWord ++ tailWord_1928051) baseStart_1928051 baseEnd_1928051 := by
    simpa [prefixWord, tailWord_1928051, baseEnd_1928051] using wordTrace_append hprefix tailTrace_1928051
  have hstable : (prefixWord ++ tailWord_1928051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928051).length < 2 ^ (prefixWord ++ tailWord_1928051).sum := by decide
  have hdescent : baseEnd_1928051 < baseStart_1928051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928054 : List Nat := [5, 1, 1, 3, 1, 2, 10]
def baseStart_1928054 : Nat := 118140960795 + 1928054 * 2 ^ 59
def prefixEnd_1928054 : Nat := 4983230072969 + 3 ^ 40 * 1928054 * 2
def baseEnd_1928054 : Nat := 12222449750912403871087

theorem tailTrace_1928054 : CollatzResearch.WordTrace tailWord_1928054 prefixEnd_1928054 12222449750912403871087 := by
  unfold tailWord_1928054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395119159812319890784951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46881271037998078835039477 4395119159812319890784951)
  ·
    refine ⟨6592678739718479836177427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395119159812319890784951 6592678739718479836177427)
    ·
      refine ⟨9889018109577719754266141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6592678739718479836177427 9889018109577719754266141)
      ·
        refine ⟨3708381791091644907849803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9889018109577719754266141 3708381791091644907849803)
        ·
          refine ⟨5562572686637467361774705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708381791091644907849803 5562572686637467361774705)
          ·
            refine ⟨4171929514978100521331029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562572686637467361774705 4171929514978100521331029)
            ·
              refine ⟨12222449750912403871087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4171929514978100521331029 12222449750912403871087)
              ·
                rfl

theorem cell23_1928054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 10].length) (baseStart_1928054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928054 prefixEnd_1928054 := by exact prefixLift 1928054
  have htrace : WordTrace (prefixWord ++ tailWord_1928054) baseStart_1928054 baseEnd_1928054 := by
    simpa [prefixWord, tailWord_1928054, baseEnd_1928054] using wordTrace_append hprefix tailTrace_1928054
  have hstable : (prefixWord ++ tailWord_1928054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928054).length < 2 ^ (prefixWord ++ tailWord_1928054).sum := by decide
  have hdescent : baseEnd_1928054 < baseStart_1928054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928107 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_1928107 : Nat := 118140960795 + 1928107 * 2 ^ 59
def prefixEnd_1928107 : Nat := 4983230072969 + 3 ^ 40 * 1928107 * 2
def baseEnd_1928107 : Nat := 990045644298593006195303

theorem tailTrace_1928107 : CollatzResearch.WordTrace tailWord_1928107 prefixEnd_1928107 990045644298593006195303 := by
  unfold tailWord_1928107
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323839625805108304238575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46882559750536738869492383 70323839625805108304238575)
  ·
    refine ⟨105485759438707662456357863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70323839625805108304238575 105485759438707662456357863)
    ·
      refine ⟨158228639158061493684536795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105485759438707662456357863 158228639158061493684536795)
      ·
        refine ⟨237342958737092240526805193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158228639158061493684536795 237342958737092240526805193)
        ·
          refine ⟨178007219052819180395103895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237342958737092240526805193 178007219052819180395103895)
          ·
            refine ⟨267010828579228770592655843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178007219052819180395103895 267010828579228770592655843)
            ·
              refine ⟨400516242868843155888983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267010828579228770592655843 400516242868843155888983765)
              ·
                refine ⟨9387099442238511466148057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 400516242868843155888983765 9387099442238511466148057)
                ·
                  refine ⟨7040324581678883599611043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387099442238511466148057 7040324581678883599611043)
                  ·
                    refine ⟨10560486872518325399416565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040324581678883599611043 10560486872518325399416565)
                    ·
                      refine ⟨990045644298593006195303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10560486872518325399416565 990045644298593006195303)
                      ·
                        rfl

theorem cell23_1928107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_1928107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928107 prefixEnd_1928107 := by exact prefixLift 1928107
  have htrace : WordTrace (prefixWord ++ tailWord_1928107) baseStart_1928107 baseEnd_1928107 := by
    simpa [prefixWord, tailWord_1928107, baseEnd_1928107] using wordTrace_append hprefix tailTrace_1928107
  have hstable : (prefixWord ++ tailWord_1928107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928107).length < 2 ^ (prefixWord ++ tailWord_1928107).sum := by decide
  have hdescent : baseEnd_1928107 < baseStart_1928107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928127 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 7]
def baseStart_1928127 : Nat := 118140960795 + 1928127 * 2 ^ 59
def prefixEnd_1928127 : Nat := 4983230072969 + 3 ^ 40 * 1928127 * 2
def baseEnd_1928127 : Nat := 110006212656853658660579

theorem tailTrace_1928127 : CollatzResearch.WordTrace tailWord_1928127 prefixEnd_1928127 110006212656853658660579 := by
  unfold tailWord_1928127
  simp only [CollatzResearch.WordTrace]
  refine ⟨70324569085732651719966635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46883046057155101146644423 70324569085732651719966635)
  ·
    refine ⟨105486853628598977579949953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70324569085732651719966635 105486853628598977579949953)
    ·
      refine ⟨79115140221449233184962465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105486853628598977579949953 79115140221449233184962465)
      ·
        refine ⟨59336355166086924888721849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79115140221449233184962465 59336355166086924888721849)
        ·
          refine ⟨44502266374565193666541387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59336355166086924888721849 44502266374565193666541387)
          ·
            refine ⟨66753399561847790499812081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44502266374565193666541387 66753399561847790499812081)
            ·
              refine ⟨50065049671385842874859061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66753399561847790499812081 50065049671385842874859061)
              ·
                refine ⟨4693598406692422769518037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50065049671385842874859061 4693598406692422769518037)
                ·
                  refine ⟨110006212656853658660579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4693598406692422769518037 110006212656853658660579)
                  ·
                    rfl

theorem cell23_1928127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 7].length) (baseStart_1928127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928127 prefixEnd_1928127 := by exact prefixLift 1928127
  have htrace : WordTrace (prefixWord ++ tailWord_1928127) baseStart_1928127 baseEnd_1928127 := by
    simpa [prefixWord, tailWord_1928127, baseEnd_1928127] using wordTrace_append hprefix tailTrace_1928127
  have hstable : (prefixWord ++ tailWord_1928127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928127).length < 2 ^ (prefixWord ++ tailWord_1928127).sum := by decide
  have hdescent : baseEnd_1928127 < baseStart_1928127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928187 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 8]
def baseStart_1928187 : Nat := 118140960795 + 1928187 * 2 ^ 59
def prefixEnd_1928187 : Nat := 4983230072969 + 3 ^ 40 * 1928187 * 2
def baseEnd_1928187 : Nat := 330028907583650897731645

theorem tailTrace_1928187 : CollatzResearch.WordTrace tailWord_1928187 prefixEnd_1928187 330028907583650897731645 := by
  unfold tailWord_1928187
  simp only [CollatzResearch.WordTrace]
  refine ⟨70326757465515281967150815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46884504977010187978100543 70326757465515281967150815)
  ·
    refine ⟨105490136198272922950726223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70326757465515281967150815 105490136198272922950726223)
    ·
      refine ⟨158235204297409384426089335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105490136198272922950726223 158235204297409384426089335)
      ·
        refine ⟨237352806446114076639134003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158235204297409384426089335 237352806446114076639134003)
        ·
          refine ⟨356029209669171114958701005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237352806446114076639134003 356029209669171114958701005)
          ·
            refine ⟨133510953625939168109512877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356029209669171114958701005 133510953625939168109512877)
            ·
              refine ⟨50066607609727188041067329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133510953625939168109512877 50066607609727188041067329)
              ·
                refine ⟨37549955707295391030800497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50066607609727188041067329 37549955707295391030800497)
                ·
                  refine ⟨28162466780471543273100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37549955707295391030800497 28162466780471543273100373)
                  ·
                    refine ⟨330028907583650897731645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28162466780471543273100373 330028907583650897731645)
                    ·
                      rfl

theorem cell23_1928187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_1928187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928187 prefixEnd_1928187 := by exact prefixLift 1928187
  have htrace : WordTrace (prefixWord ++ tailWord_1928187) baseStart_1928187 baseEnd_1928187 := by
    simpa [prefixWord, tailWord_1928187, baseEnd_1928187] using wordTrace_append hprefix tailTrace_1928187
  have hstable : (prefixWord ++ tailWord_1928187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928187).length < 2 ^ (prefixWord ++ tailWord_1928187).sum := by decide
  have hdescent : baseEnd_1928187 < baseStart_1928187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928228 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1928228 : Nat := 118140960795 + 1928228 * 2 ^ 59
def prefixEnd_1928228 : Nat := 4983230072969 + 3 ^ 40 * 1928228 * 2
def baseEnd_1928228 : Nat := 990107775457787032782247

theorem tailTrace_1928228 : CollatzResearch.WordTrace tailWord_1928228 prefixEnd_1928228 990107775457787032782247 := by
  unfold tailWord_1928228
  simp only [CollatzResearch.WordTrace]
  refine ⟨35164126429183372984696669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46885501905577830646262225 35164126429183372984696669)
  ·
    refine ⟨13186547410943764869261251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35164126429183372984696669 13186547410943764869261251)
    ·
      refine ⟨19779821116415647303891877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13186547410943764869261251 19779821116415647303891877)
      ·
        refine ⟨3708716459327933869479727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19779821116415647303891877 3708716459327933869479727)
        ·
          refine ⟨5563074688991900804219591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708716459327933869479727 5563074688991900804219591)
          ·
            refine ⟨8344612033487851206329387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563074688991900804219591 8344612033487851206329387)
            ·
              refine ⟨12516918050231776809494081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344612033487851206329387 12516918050231776809494081)
              ·
                refine ⟨9387688537673832607120561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516918050231776809494081 9387688537673832607120561)
                ·
                  refine ⟨7040766403255374455340421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387688537673832607120561 7040766403255374455340421)
                  ·
                    refine ⟨1320143700610382710376329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040766403255374455340421 1320143700610382710376329)
                    ·
                      refine ⟨990107775457787032782247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320143700610382710376329 990107775457787032782247)
                      ·
                        rfl

theorem cell23_1928228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1928228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928228 prefixEnd_1928228 := by exact prefixLift 1928228
  have htrace : WordTrace (prefixWord ++ tailWord_1928228) baseStart_1928228 baseEnd_1928228 := by
    simpa [prefixWord, tailWord_1928228, baseEnd_1928228] using wordTrace_append hprefix tailTrace_1928228
  have hstable : (prefixWord ++ tailWord_1928228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928228).length < 2 ^ (prefixWord ++ tailWord_1928228).sum := by decide
  have hdescent : baseEnd_1928228 < baseStart_1928228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928238 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1928238 : Nat := 118140960795 + 1928238 * 2 ^ 59
def prefixEnd_1928238 : Nat := 4983230072969 + 3 ^ 40 * 1928238 * 2
def baseEnd_1928238 : Nat := 330037636754777331219067

theorem tailTrace_1928238 : CollatzResearch.WordTrace tailWord_1928238 prefixEnd_1928238 330037636754777331219067 := by
  unfold tailWord_1928238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791077198541314709657171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46885745058887011784838245 8791077198541314709657171)
  ·
    refine ⟨13186615797811972064485757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8791077198541314709657171 13186615797811972064485757)
    ·
      refine ⟨4944980924179489524182159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13186615797811972064485757 4944980924179489524182159)
      ·
        refine ⟨7417471386269234286273239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944980924179489524182159 7417471386269234286273239)
        ·
          refine ⟨11126207079403851429409859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417471386269234286273239 11126207079403851429409859)
          ·
            refine ⟨16689310619105777144114789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126207079403851429409859 16689310619105777144114789)
            ·
              refine ⟨3129245741082333214521523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16689310619105777144114789 3129245741082333214521523)
              ·
                refine ⟨4693868611623499821782285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129245741082333214521523 4693868611623499821782285)
                ·
                  refine ⟨1760200729358812433168357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4693868611623499821782285 1760200729358812433168357)
                  ·
                    refine ⟨330037636754777331219067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760200729358812433168357 330037636754777331219067)
                    ·
                      rfl

theorem cell23_1928238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1928238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928238 prefixEnd_1928238 := by exact prefixLift 1928238
  have htrace : WordTrace (prefixWord ++ tailWord_1928238) baseStart_1928238 baseEnd_1928238 := by
    simpa [prefixWord, tailWord_1928238, baseEnd_1928238] using wordTrace_append hprefix tailTrace_1928238
  have hstable : (prefixWord ++ tailWord_1928238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928238).length < 2 ^ (prefixWord ++ tailWord_1928238).sum := by decide
  have hdescent : baseEnd_1928238 < baseStart_1928238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928288 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2]
def baseStart_1928288 : Nat := 118140960795 + 1928288 * 2 ^ 59
def prefixEnd_1928288 : Nat := 4983230072969 + 3 ^ 40 * 1928288 * 2
def baseEnd_1928288 : Nat := 990138584297056798031971

theorem tailTrace_1928288 : CollatzResearch.WordTrace tailWord_1928288 prefixEnd_1928288 990138584297056798031971 := by
  unfold tailWord_1928288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165220619074688108288759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46886960825432917477718345 35165220619074688108288759)
  ·
    refine ⟨52747830928612032162433139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35165220619074688108288759 52747830928612032162433139)
    ·
      refine ⟨79121746392918048243649709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52747830928612032162433139 79121746392918048243649709)
      ·
        refine ⟨29670654897344268091368641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79121746392918048243649709 29670654897344268091368641)
        ·
          refine ⟨22252991173008201068526481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29670654897344268091368641 22252991173008201068526481)
          ·
            refine ⟨16689743379756150801394861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22252991173008201068526481 16689743379756150801394861)
            ·
              refine ⟨6258653767408556550523073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16689743379756150801394861 6258653767408556550523073)
              ·
                refine ⟨4693990325556417412892305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258653767408556550523073 4693990325556417412892305)
                ·
                  refine ⟨3520492744167313059669229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693990325556417412892305 3520492744167313059669229)
                  ·
                    refine ⟨1320184779062742397375961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3520492744167313059669229 1320184779062742397375961)
                    ·
                      refine ⟨990138584297056798031971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320184779062742397375961 990138584297056798031971)
                      ·
                        rfl

theorem cell23_1928288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_1928288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928288 prefixEnd_1928288 := by exact prefixLift 1928288
  have htrace : WordTrace (prefixWord ++ tailWord_1928288) baseStart_1928288 baseEnd_1928288 := by
    simpa [prefixWord, tailWord_1928288, baseEnd_1928288] using wordTrace_append hprefix tailTrace_1928288
  have hstable : (prefixWord ++ tailWord_1928288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928288).length < 2 ^ (prefixWord ++ tailWord_1928288).sum := by decide
  have hdescent : baseEnd_1928288 < baseStart_1928288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928295 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1928295 : Nat := 118140960795 + 1928295 * 2 ^ 59
def prefixEnd_1928295 : Nat := 4983230072969 + 3 ^ 40 * 1928295 * 2
def baseEnd_1928295 : Nat := 990142178661638270644439

theorem tailTrace_1928295 : CollatzResearch.WordTrace tailWord_1928295 prefixEnd_1928295 990142178661638270644439 := by
  unfold tailWord_1928295
  simp only [CollatzResearch.WordTrace]
  refine ⟨70330696549124016412082339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46887131032749344274721559 70330696549124016412082339)
  ·
    refine ⟨105496044823686024618123509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70330696549124016412082339 105496044823686024618123509)
    ·
      refine ⟨9890254202220564807949079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105496044823686024618123509 9890254202220564807949079)
      ·
        refine ⟨14835381303330847211923619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890254202220564807949079 14835381303330847211923619)
        ·
          refine ⟨22253071954996270817885429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835381303330847211923619 22253071954996270817885429)
          ·
            refine ⟨2086225495780900389176759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22253071954996270817885429 2086225495780900389176759)
            ·
              refine ⟨3129338243671350583765139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086225495780900389176759 3129338243671350583765139)
              ·
                refine ⟨4694007365507025875647709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129338243671350583765139 4694007365507025875647709)
                ·
                  refine ⟨1760252762065134703367891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4694007365507025875647709 1760252762065134703367891)
                  ·
                    refine ⟨2640379143097702055051837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760252762065134703367891 2640379143097702055051837)
                    ·
                      refine ⟨990142178661638270644439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2640379143097702055051837 990142178661638270644439)
                      ·
                        rfl

theorem cell23_1928295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1928295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928295 prefixEnd_1928295 := by exact prefixLift 1928295
  have htrace : WordTrace (prefixWord ++ tailWord_1928295) baseStart_1928295 baseEnd_1928295 := by
    simpa [prefixWord, tailWord_1928295, baseEnd_1928295] using wordTrace_append hprefix tailTrace_1928295
  have hstable : (prefixWord ++ tailWord_1928295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928295).length < 2 ^ (prefixWord ++ tailWord_1928295).sum := by decide
  have hdescent : baseEnd_1928295 < baseStart_1928295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928328 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1928328 : Nat := 118140960795 + 1928328 * 2 ^ 59
def prefixEnd_1928328 : Nat := 4983230072969 + 3 ^ 40 * 1928328 * 2
def baseEnd_1928328 : Nat := 330053041174412213843929

theorem tailTrace_1928328 : CollatzResearch.WordTrace tailWord_1928328 prefixEnd_1928328 330053041174412213843929 := by
  unfold tailWord_1928328
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165950079002231524016819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46887933438669642032022425 35165950079002231524016819)
  ·
    refine ⟨52748925118503347286025229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35165950079002231524016819 52748925118503347286025229)
    ·
      refine ⟨19780846919438755232259461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52748925118503347286025229 19780846919438755232259461)
      ·
        refine ⟨3708908797394766606048649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19780846919438755232259461 3708908797394766606048649)
        ·
          refine ⟨2781681598046074954536487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708908797394766606048649 2781681598046074954536487)
          ·
            refine ⟨4172522397069112431804731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781681598046074954536487 4172522397069112431804731)
            ·
              refine ⟨6258783595603668647707097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172522397069112431804731 6258783595603668647707097)
              ·
                refine ⟨4694087696702751485780323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258783595603668647707097 4694087696702751485780323)
                ·
                  refine ⟨7041131545054127228670485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694087696702751485780323 7041131545054127228670485)
                  ·
                    refine ⟨330053041174412213843929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7041131545054127228670485 330053041174412213843929)
                    ·
                      rfl

theorem cell23_1928328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1928328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928328 prefixEnd_1928328 := by exact prefixLift 1928328
  have htrace : WordTrace (prefixWord ++ tailWord_1928328) baseStart_1928328 baseEnd_1928328 := by
    simpa [prefixWord, tailWord_1928328, baseEnd_1928328] using wordTrace_append hprefix tailTrace_1928328
  have hstable : (prefixWord ++ tailWord_1928328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928328).length < 2 ^ (prefixWord ++ tailWord_1928328).sum := by decide
  have hdescent : baseEnd_1928328 < baseStart_1928328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928338 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1928338 : Nat := 118140960795 + 1928338 * 2 ^ 59
def prefixEnd_1928338 : Nat := 4983230072969 + 3 ^ 40 * 1928338 * 2
def baseEnd_1928338 : Nat := 990164258329781602406741

theorem tailTrace_1928338 : CollatzResearch.WordTrace tailWord_1928338 prefixEnd_1928338 990164258329781602406741 := by
  unfold tailWord_1928338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583066221992058688974417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46888176591978823170598445 17583066221992058688974417)
  ·
    refine ⟨13187299666494044016730813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17583066221992058688974417 13187299666494044016730813)
    ·
      refine ⟨4945237374935266506274055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13187299666494044016730813 4945237374935266506274055)
      ·
        refine ⟨7417856062402899759411083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945237374935266506274055 7417856062402899759411083)
        ·
          refine ⟨11126784093604349639116625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417856062402899759411083 11126784093604349639116625)
          ·
            refine ⟨8345088070203262229337469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11126784093604349639116625 8345088070203262229337469)
            ·
              refine ⟨3129408026326223336001551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8345088070203262229337469 3129408026326223336001551)
              ·
                refine ⟨4694112039489335004002327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129408026326223336001551 4694112039489335004002327)
                ·
                  refine ⟨7041168059234002506003491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694112039489335004002327 7041168059234002506003491)
                  ·
                    refine ⟨10561752088851003759005237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041168059234002506003491 10561752088851003759005237)
                    ·
                      refine ⟨990164258329781602406741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10561752088851003759005237 990164258329781602406741)
                      ·
                        rfl

theorem cell23_1928338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1928338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928338 prefixEnd_1928338 := by exact prefixLift 1928338
  have htrace : WordTrace (prefixWord ++ tailWord_1928338) baseStart_1928338 baseEnd_1928338 := by
    simpa [prefixWord, tailWord_1928338, baseEnd_1928338] using wordTrace_append hprefix tailTrace_1928338
  have hstable : (prefixWord ++ tailWord_1928338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928338).length < 2 ^ (prefixWord ++ tailWord_1928338).sum := by decide
  have hdescent : baseEnd_1928338 < baseStart_1928338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928352 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 1, 2, 2]
def baseStart_1928352 : Nat := 118140960795 + 1928352 * 2 ^ 59
def prefixEnd_1928352 : Nat := 4983230072969 + 3 ^ 40 * 1928352 * 2
def baseEnd_1928352 : Nat := 990171447058944547631677

theorem tailTrace_1928352 : CollatzResearch.WordTrace tailWord_1928352 prefixEnd_1928352 990171447058944547631677 := by
  unfold tailWord_1928352
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166387754958757573453655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46888517006611676764604873 35166387754958757573453655)
  ·
    refine ⟨52749581632438136360180483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35166387754958757573453655 52749581632438136360180483)
    ·
      refine ⟨79124372448657204540270725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52749581632438136360180483 79124372448657204540270725)
      ·
        refine ⟨14835819834123225851300761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79124372448657204540270725 14835819834123225851300761)
        ·
          refine ⟨11126864875592419388475571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14835819834123225851300761 11126864875592419388475571)
          ·
            refine ⟨16690297313388629082713357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126864875592419388475571 16690297313388629082713357)
            ·
              refine ⟨6258861492520735906017509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16690297313388629082713357 6258861492520735906017509)
              ·
                refine ⟨1173536529847637982378283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6258861492520735906017509 1173536529847637982378283)
                ·
                  refine ⟨1760304794771456973567425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173536529847637982378283 1760304794771456973567425)
                  ·
                    refine ⟨1320228596078592730175569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760304794771456973567425 1320228596078592730175569)
                    ·
                      refine ⟨990171447058944547631677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320228596078592730175569 990171447058944547631677)
                      ·
                        rfl

theorem cell23_1928352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_1928352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928352 prefixEnd_1928352 := by exact prefixLift 1928352
  have htrace : WordTrace (prefixWord ++ tailWord_1928352) baseStart_1928352 baseEnd_1928352 := by
    simpa [prefixWord, tailWord_1928352, baseEnd_1928352] using wordTrace_append hprefix tailTrace_1928352
  have hstable : (prefixWord ++ tailWord_1928352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928352).length < 2 ^ (prefixWord ++ tailWord_1928352).sum := by decide
  have hdescent : baseEnd_1928352 < baseStart_1928352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928365 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1928365 : Nat := 118140960795 + 1928365 * 2 ^ 59
def prefixEnd_1928365 : Nat := 4983230072969 + 3 ^ 40 * 1928365 * 2
def baseEnd_1928365 : Nat := 990178122307452996769117

theorem tailTrace_1928365 : CollatzResearch.WordTrace tailWord_1928365 prefixEnd_1928365 990178122307452996769117 := by
  unfold tailWord_1928365
  simp only [CollatzResearch.WordTrace]
  refine ⟨70333249658870418367130549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46888833105913612244753699 70333249658870418367130549)
  ·
    refine ⟨6593742155519101721918489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70333249658870418367130549 6593742155519101721918489)
    ·
      refine ⟨4945306616639326291438867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6593742155519101721918489 4945306616639326291438867)
      ·
        refine ⟨7417959924958989437158301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945306616639326291438867 7417959924958989437158301)
        ·
          refine ⟨2781734971859621038934363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7417959924958989437158301 2781734971859621038934363)
          ·
            refine ⟨4172602457789431558401545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781734971859621038934363 4172602457789431558401545)
            ·
              refine ⟨3129451843342073668801159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172602457789431558401545 3129451843342073668801159)
              ·
                refine ⟨4694177765013110503201739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129451843342073668801159 4694177765013110503201739)
                ·
                  refine ⟨7041266647519665754802609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694177765013110503201739 7041266647519665754802609)
                  ·
                    refine ⟨5280949985639749316101957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041266647519665754802609 5280949985639749316101957)
                    ·
                      refine ⟨990178122307452996769117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5280949985639749316101957 990178122307452996769117)
                      ·
                        rfl

theorem cell23_1928365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1928365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928365 prefixEnd_1928365 := by exact prefixLift 1928365
  have htrace : WordTrace (prefixWord ++ tailWord_1928365) baseStart_1928365 baseEnd_1928365 := by
    simpa [prefixWord, tailWord_1928365, baseEnd_1928365] using wordTrace_append hprefix tailTrace_1928365
  have hstable : (prefixWord ++ tailWord_1928365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928365).length < 2 ^ (prefixWord ++ tailWord_1928365).sum := by decide
  have hdescent : baseEnd_1928365 < baseStart_1928365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928385 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1928385 : Nat := 118140960795 + 1928385 * 2 ^ 59
def prefixEnd_1928385 : Nat := 4983230072969 + 3 ^ 40 * 1928385 * 2
def baseEnd_1928385 : Nat := 990188391920542918519025

theorem tailTrace_1928385 : CollatzResearch.WordTrace tailWord_1928385 prefixEnd_1928385 990188391920542918519025 := by
  unfold tailWord_1928385
  simp only [CollatzResearch.WordTrace]
  refine ⟨70333979118797961782858609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46889319412531974521905739 70333979118797961782858609)
  ·
    refine ⟨52750484339098471337143957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70333979118797961782858609 52750484339098471337143957)
    ·
      refine ⟨2472678953395240843928623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52750484339098471337143957 2472678953395240843928623)
      ·
        refine ⟨3709018430092861265892935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472678953395240843928623 3709018430092861265892935)
        ·
          refine ⟨5563527645139291898839403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709018430092861265892935 5563527645139291898839403)
          ·
            refine ⟨8345291467708937848259105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563527645139291898839403 8345291467708937848259105)
            ·
              refine ⟨6258968600781703386194329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345291467708937848259105 6258968600781703386194329)
              ·
                refine ⟨4694226450586277539645747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258968600781703386194329 4694226450586277539645747)
                ·
                  refine ⟨7041339675879416309468621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694226450586277539645747 7041339675879416309468621)
                  ·
                    refine ⟨2640502378454781116050733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7041339675879416309468621 2640502378454781116050733)
                    ·
                      refine ⟨990188391920542918519025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2640502378454781116050733 990188391920542918519025)
                      ·
                        rfl

theorem cell23_1928385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1928385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928385 prefixEnd_1928385 := by exact prefixLift 1928385
  have htrace : WordTrace (prefixWord ++ tailWord_1928385) baseStart_1928385 baseEnd_1928385 := by
    simpa [prefixWord, tailWord_1928385, baseEnd_1928385] using wordTrace_append hprefix tailTrace_1928385
  have hstable : (prefixWord ++ tailWord_1928385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928385).length < 2 ^ (prefixWord ++ tailWord_1928385).sum := by decide
  have hdescent : baseEnd_1928385 < baseStart_1928385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928386 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1928386 : Nat := 118140960795 + 1928386 * 2 ^ 59
def prefixEnd_1928386 : Nat := 4983230072969 + 3 ^ 40 * 1928386 * 2
def baseEnd_1928386 : Nat := 990188905401197414606521

theorem tailTrace_1928386 : CollatzResearch.WordTrace tailWord_1928386 prefixEnd_1928386 990188905401197414606521 := by
  unfold tailWord_1928386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583503897948584738411253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46889343727862892635763341 17583503897948584738411253)
  ·
    refine ⟨1648453490432679819226055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17583503897948584738411253 1648453490432679819226055)
    ·
      refine ⟨2472680235649019728839083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648453490432679819226055 2472680235649019728839083)
      ·
        refine ⟨3709020353473529593258625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472680235649019728839083 3709020353473529593258625)
        ·
          refine ⟨2781765265105147194943969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709020353473529593258625 2781765265105147194943969)
          ·
            refine ⟨2086323948828860396207977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781765265105147194943969 2086323948828860396207977)
            ·
              refine ⟨1564742961621645297155983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086323948828860396207977 1564742961621645297155983)
              ·
                refine ⟨2347114442432467945733975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564742961621645297155983 2347114442432467945733975)
                ·
                  refine ⟨3520671663648701918600963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347114442432467945733975 3520671663648701918600963)
                  ·
                    refine ⟨5281007495473052877901445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3520671663648701918600963 5281007495473052877901445)
                    ·
                      refine ⟨990188905401197414606521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5281007495473052877901445 990188905401197414606521)
                      ·
                        rfl

theorem cell23_1928386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1928386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928386 prefixEnd_1928386 := by exact prefixLift 1928386
  have htrace : WordTrace (prefixWord ++ tailWord_1928386) baseStart_1928386 baseEnd_1928386 := by
    simpa [prefixWord, tailWord_1928386, baseEnd_1928386] using wordTrace_append hprefix tailTrace_1928386
  have hstable : (prefixWord ++ tailWord_1928386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928386).length < 2 ^ (prefixWord ++ tailWord_1928386).sum := by decide
  have hdescent : baseEnd_1928386 < baseStart_1928386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928465 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 5]
def baseStart_1928465 : Nat := 118140960795 + 1928465 * 2 ^ 59
def prefixEnd_1928465 : Nat := 4983230072969 + 3 ^ 40 * 1928465 * 2
def baseEnd_1928465 : Nat := 110025496708100289502073

theorem tailTrace_1928465 : CollatzResearch.WordTrace tailWord_1928465 prefixEnd_1928465 110025496708100289502073 := by
  unfold tailWord_1928465
  simp only [CollatzResearch.WordTrace]
  refine ⟨70336896958508135445770849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46891264639005423630513899 70336896958508135445770849)
  ·
    refine ⟨52752672718881101584328137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70336896958508135445770849 52752672718881101584328137)
    ·
      refine ⟨39564504539160826188246103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52752672718881101584328137 39564504539160826188246103)
      ·
        refine ⟨59346756808741239282369155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39564504539160826188246103 59346756808741239282369155)
        ·
          refine ⟨89020135213111858923553733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59346756808741239282369155 89020135213111858923553733)
          ·
            refine ⟨16691275352458473548166325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89020135213111858923553733 16691275352458473548166325)
            ·
              refine ⟨1564807064292981895140593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16691275352458473548166325 1564807064292981895140593)
              ·
                refine ⟨1173605298219736421355445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564807064292981895140593 1173605298219736421355445)
                ·
                  refine ⟨110025496708100289502073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173605298219736421355445 110025496708100289502073)
                  ·
                    rfl

theorem cell23_1928465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 5].length) (baseStart_1928465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928465 prefixEnd_1928465 := by exact prefixLift 1928465
  have htrace : WordTrace (prefixWord ++ tailWord_1928465) baseStart_1928465 baseEnd_1928465 := by
    simpa [prefixWord, tailWord_1928465, baseEnd_1928465] using wordTrace_append hprefix tailTrace_1928465
  have hstable : (prefixWord ++ tailWord_1928465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928465).length < 2 ^ (prefixWord ++ tailWord_1928465).sum := by decide
  have hdescent : baseEnd_1928465 < baseStart_1928465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928521 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 8]
def baseStart_1928521 : Nat := 118140960795 + 1928521 * 2 ^ 59
def prefixEnd_1928521 : Nat := 4983230072969 + 3 ^ 40 * 1928521 * 2
def baseEnd_1928521 : Nat := 110028691698839376268711

theorem tailTrace_1928521 : CollatzResearch.WordTrace tailWord_1928521 prefixEnd_1928521 110028691698839376268711 := by
  unfold tailWord_1928521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70338939446305257009809417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46892626297536838006539611 70338939446305257009809417)
  ·
    refine ⟨52754204584728942757357063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70338939446305257009809417 52754204584728942757357063)
    ·
      refine ⟨79131306877093414136035595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52754204584728942757357063 79131306877093414136035595)
      ·
        refine ⟨118696960315640121204053393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79131306877093414136035595 118696960315640121204053393)
        ·
          refine ⟨89022720236730090903040045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118696960315640121204053393 89022720236730090903040045)
          ·
            refine ⟨33383520088773784088640017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89022720236730090903040045 33383520088773784088640017)
            ·
              refine ⟨25037640066580338066480013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33383520088773784088640017 25037640066580338066480013)
              ·
                refine ⟨9389115024967626774930005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25037640066580338066480013 9389115024967626774930005)
                ·
                  refine ⟨110028691698839376268711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9389115024967626774930005 110028691698839376268711)
                  ·
                    rfl

theorem cell23_1928521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_1928521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928521 prefixEnd_1928521 := by exact prefixLift 1928521
  have htrace : WordTrace (prefixWord ++ tailWord_1928521) baseStart_1928521 baseEnd_1928521 := by
    simpa [prefixWord, tailWord_1928521, baseEnd_1928521] using wordTrace_append hprefix tailTrace_1928521
  have hstable : (prefixWord ++ tailWord_1928521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928521).length < 2 ^ (prefixWord ++ tailWord_1928521).sum := by decide
  have hdescent : baseEnd_1928521 < baseStart_1928521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928538 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_1928538 : Nat := 118140960795 + 1928538 * 2 ^ 59
def prefixEnd_1928538 : Nat := 4983230072969 + 3 ^ 40 * 1928538 * 2
def baseEnd_1928538 : Nat := 110029661606742313322869

theorem tailTrace_1928538 : CollatzResearch.WordTrace tailWord_1928538 prefixEnd_1928538 110029661606742313322869 := by
  unfold tailWord_1928538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584889871810917228294567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46893039658162445942118845 17584889871810917228294567)
  ·
    refine ⟨26377334807716375842441851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17584889871810917228294567 26377334807716375842441851)
    ·
      refine ⟨39566002211574563763662777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26377334807716375842441851 39566002211574563763662777)
      ·
        refine ⟨29674501658680922822747083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39566002211574563763662777 29674501658680922822747083)
        ·
          refine ⟨44511752488021384234120625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29674501658680922822747083 44511752488021384234120625)
          ·
            refine ⟨33383814366016038175590469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44511752488021384234120625 33383814366016038175590469)
            ·
              refine ⟨6259465193628007157923213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33383814366016038175590469 6259465193628007157923213)
              ·
                refine ⟨2347299447610502684221205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6259465193628007157923213 2347299447610502684221205)
                ·
                  refine ⟨110029661606742313322869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2347299447610502684221205 110029661606742313322869)
                  ·
                    rfl

theorem cell23_1928538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_1928538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928538 prefixEnd_1928538 := by exact prefixLift 1928538
  have htrace : WordTrace (prefixWord ++ tailWord_1928538) baseStart_1928538 baseEnd_1928538 := by
    simpa [prefixWord, tailWord_1928538, baseEnd_1928538] using wordTrace_append hprefix tailTrace_1928538
  have hstable : (prefixWord ++ tailWord_1928538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928538).length < 2 ^ (prefixWord ++ tailWord_1928538).sum := by decide
  have hdescent : baseEnd_1928538 < baseStart_1928538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928608 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1928608 : Nat := 118140960795 + 1928608 * 2 ^ 59
def prefixEnd_1928608 : Nat := 4983230072969 + 3 ^ 40 * 1928608 * 2
def baseEnd_1928608 : Nat := 990302898106495546030499

theorem tailTrace_1928608 : CollatzResearch.WordTrace tailWord_1928608 prefixEnd_1928608 990302898106495546030499 := by
  unfold tailWord_1928608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171056298495035434113239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46894741731326713912150985 35171056298495035434113239)
  ·
    refine ⟨52756584447742553151169859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171056298495035434113239 52756584447742553151169859)
    ·
      refine ⟨79134876671613829726754789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52756584447742553151169859 79134876671613829726754789)
      ·
        refine ⟨14837789375927593073766523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79134876671613829726754789 14837789375927593073766523)
        ·
          refine ⟨22256684063891389610649785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837789375927593073766523 22256684063891389610649785)
          ·
            refine ⟨16692513047918542207987339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22256684063891389610649785 16692513047918542207987339)
            ·
              refine ⟨25038769571877813311981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692513047918542207987339 25038769571877813311981009)
              ·
                refine ⟨18779077178908359983985757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25038769571877813311981009 18779077178908359983985757)
                ·
                  refine ⟨7042153942090634993994659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18779077178908359983985757 7042153942090634993994659)
                  ·
                    refine ⟨10563230913135952490991989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042153942090634993994659 10563230913135952490991989)
                    ·
                      refine ⟨990302898106495546030499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10563230913135952490991989 990302898106495546030499)
                      ·
                        rfl

theorem cell23_1928608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1928608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928608 prefixEnd_1928608 := by exact prefixLift 1928608
  have htrace : WordTrace (prefixWord ++ tailWord_1928608) baseStart_1928608 baseEnd_1928608 := by
    simpa [prefixWord, tailWord_1928608, baseEnd_1928608] using wordTrace_append hprefix tailTrace_1928608
  have hstable : (prefixWord ++ tailWord_1928608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928608).length < 2 ^ (prefixWord ++ tailWord_1928608).sum := by decide
  have hdescent : baseEnd_1928608 < baseStart_1928608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928615 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1928615 : Nat := 118140960795 + 1928615 * 2 ^ 59
def prefixEnd_1928615 : Nat := 4983230072969 + 3 ^ 40 * 1928615 * 2
def baseEnd_1928615 : Nat := 330102164157025672880989

theorem tailTrace_1928615 : CollatzResearch.WordTrace tailWord_1928615 prefixEnd_1928615 330102164157025672880989 := by
  unfold tailWord_1928615
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342367907964711063731299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46894911938643140709154199 70342367907964711063731299)
  ·
    refine ⟨105513551861947066595596949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70342367907964711063731299 105513551861947066595596949)
    ·
      refine ⟨4945947743528768746668607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105513551861947066595596949 4945947743528768746668607)
      ·
        refine ⟨7418921615293153120002911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945947743528768746668607 7418921615293153120002911)
        ·
          refine ⟨11128382422939729680004367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418921615293153120002911 11128382422939729680004367)
          ·
            refine ⟨16692573634409594520006551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128382422939729680004367 16692573634409594520006551)
            ·
              refine ⟨25038860451614391780009827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692573634409594520006551 25038860451614391780009827)
              ·
                refine ⟨37558290677421587670014741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25038860451614391780009827 37558290677421587670014741)
                ·
                  refine ⟨1760544875504136922031941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37558290677421587670014741 1760544875504136922031941)
                  ·
                    refine ⟨330102164157025672880989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760544875504136922031941 330102164157025672880989)
                    ·
                      rfl

theorem cell23_1928615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1928615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928615 prefixEnd_1928615 := by exact prefixLift 1928615
  have htrace : WordTrace (prefixWord ++ tailWord_1928615) baseStart_1928615 baseEnd_1928615 := by
    simpa [prefixWord, tailWord_1928615, baseEnd_1928615] using wordTrace_append hprefix tailTrace_1928615
  have hstable : (prefixWord ++ tailWord_1928615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928615).length < 2 ^ (prefixWord ++ tailWord_1928615).sum := by decide
  have hdescent : baseEnd_1928615 < baseStart_1928615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928625 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1928625 : Nat := 118140960795 + 1928625 * 2 ^ 59
def prefixEnd_1928625 : Nat := 4983230072969 + 3 ^ 40 * 1928625 * 2
def baseEnd_1928625 : Nat := 990311627277621979517921

theorem tailTrace_1928625 : CollatzResearch.WordTrace tailWord_1928625 prefixEnd_1928625 990311627277621979517921 := by
  unfold tailWord_1928625
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342732637928482771595329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46895155091952321847730219 70342732637928482771595329)
  ·
    refine ⟨52757049478446362078696497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70342732637928482771595329 52757049478446362078696497)
    ·
      refine ⟨39567787108834771559022373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52757049478446362078696497 39567787108834771559022373)
      ·
        refine ⟨7418960082906519667316695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39567787108834771559022373 7418960082906519667316695)
        ·
          refine ⟨11128440124359779500975043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418960082906519667316695 11128440124359779500975043)
          ·
            refine ⟨16692660186539669251462565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128440124359779500975043 16692660186539669251462565)
            ·
              refine ⟨3129873784976187984649231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16692660186539669251462565 3129873784976187984649231)
              ·
                refine ⟨4694810677464281976973847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129873784976187984649231 4694810677464281976973847)
                ·
                  refine ⟨7042216016196422965460771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694810677464281976973847 7042216016196422965460771)
                  ·
                    refine ⟨10563324024294634448191157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042216016196422965460771 10563324024294634448191157)
                    ·
                      refine ⟨990311627277621979517921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10563324024294634448191157 990311627277621979517921)
                      ·
                        rfl

theorem cell23_1928625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1928625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928625 prefixEnd_1928625 := by exact prefixLift 1928625
  have htrace : WordTrace (prefixWord ++ tailWord_1928625) baseStart_1928625 baseEnd_1928625 := by
    simpa [prefixWord, tailWord_1928625, baseEnd_1928625] using wordTrace_append hprefix tailTrace_1928625
  have hstable : (prefixWord ++ tailWord_1928625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928625).length < 2 ^ (prefixWord ++ tailWord_1928625).sum := by decide
  have hdescent : baseEnd_1928625 < baseStart_1928625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928639 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 1, 2, 2]
def baseStart_1928639 : Nat := 118140960795 + 1928639 * 2 ^ 59
def prefixEnd_1928639 : Nat := 4983230072969 + 3 ^ 40 * 1928639 * 2
def baseEnd_1928639 : Nat := 990318816006784924742857

theorem tailTrace_1928639 : CollatzResearch.WordTrace tailWord_1928639 prefixEnd_1928639 990318816006784924742857 := by
  unfold tailWord_1928639
  simp only [CollatzResearch.WordTrace]
  refine ⟨70343243259877763162604971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46895495506585175441736647 70343243259877763162604971)
  ·
    refine ⟨105514864889816644743907457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70343243259877763162604971 105514864889816644743907457)
    ·
      refine ⟨79136148667362483557930593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105514864889816644743907457 79136148667362483557930593)
      ·
        refine ⟨59352111500521862668447945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79136148667362483557930593 59352111500521862668447945)
        ·
          refine ⟨44514083625391397001335959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59352111500521862668447945 44514083625391397001335959)
          ·
            refine ⟨66771125438087095502003939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44514083625391397001335959 66771125438087095502003939)
            ·
              refine ⟨100156688157130643253005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66771125438087095502003939 100156688157130643253005909)
              ·
                refine ⟨1173711189341374725621163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 100156688157130643253005909 1173711189341374725621163)
                ·
                  refine ⟨1760566784012062088431745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173711189341374725621163 1760566784012062088431745)
                  ·
                    refine ⟨1320425088009046566323809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760566784012062088431745 1320425088009046566323809)
                    ·
                      refine ⟨990318816006784924742857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320425088009046566323809 990318816006784924742857)
                      ·
                        rfl

theorem cell23_1928639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_1928639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928639 prefixEnd_1928639 := by exact prefixLift 1928639
  have htrace : WordTrace (prefixWord ++ tailWord_1928639) baseStart_1928639 baseEnd_1928639 := by
    simpa [prefixWord, tailWord_1928639, baseEnd_1928639] using wordTrace_append hprefix tailTrace_1928639
  have hstable : (prefixWord ++ tailWord_1928639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928639).length < 2 ^ (prefixWord ++ tailWord_1928639).sum := by decide
  have hdescent : baseEnd_1928639 < baseStart_1928639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928648 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1928648 : Nat := 118140960795 + 1928648 * 2 ^ 59
def prefixEnd_1928648 : Nat := 4983230072969 + 3 ^ 40 * 1928648 * 2
def baseEnd_1928648 : Nat := 990323437332675389530315

theorem tailTrace_1928648 : CollatzResearch.WordTrace tailWord_1928648 prefixEnd_1928648 990323437332675389530315 := by
  unfold tailWord_1928648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171785758422578849841299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46895714344563438466455065 35171785758422578849841299)
  ·
    refine ⟨52757678637633868274761949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171785758422578849841299 52757678637633868274761949)
    ·
      refine ⟨19784129489112700603035731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52757678637633868274761949 19784129489112700603035731)
      ·
        refine ⟨29676194233669050904553597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19784129489112700603035731 29676194233669050904553597)
        ·
          refine ⟨11128572837625894089207599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29676194233669050904553597 11128572837625894089207599)
          ·
            refine ⟨16692859256438841133811399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128572837625894089207599 16692859256438841133811399)
            ·
              refine ⟨25039288884658261700717099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692859256438841133811399 25039288884658261700717099)
              ·
                refine ⟨37558933326987392551075649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25039288884658261700717099 37558933326987392551075649)
                ·
                  refine ⟨28169199995240544413306737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37558933326987392551075649 28169199995240544413306737)
                  ·
                    refine ⟨21126899996430408309980053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28169199995240544413306737 21126899996430408309980053)
                    ·
                      refine ⟨990323437332675389530315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21126899996430408309980053 990323437332675389530315)
                      ·
                        rfl

theorem cell23_1928648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1928648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928648 prefixEnd_1928648 := by exact prefixLift 1928648
  have htrace : WordTrace (prefixWord ++ tailWord_1928648) baseStart_1928648 baseEnd_1928648 := by
    simpa [prefixWord, tailWord_1928648, baseEnd_1928648] using wordTrace_append hprefix tailTrace_1928648
  have hstable : (prefixWord ++ tailWord_1928648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928648).length < 2 ^ (prefixWord ++ tailWord_1928648).sum := by decide
  have hdescent : baseEnd_1928648 < baseStart_1928648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928689 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_1928689 : Nat := 118140960795 + 1928689 * 2 ^ 59
def prefixEnd_1928689 : Nat := 4983230072969 + 3 ^ 40 * 1928689 * 2
def baseEnd_1928689 : Nat := 990344490039509729117627

theorem tailTrace_1928689 : CollatzResearch.WordTrace tailWord_1928689 prefixEnd_1928689 990344490039509729117627 := by
  unfold tailWord_1928689
  simp only [CollatzResearch.WordTrace]
  refine ⟨70345066909696621701925121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46896711273131081134616747 70345066909696621701925121)
  ·
    refine ⟨52758800182272466276443841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70345066909696621701925121 52758800182272466276443841)
    ·
      refine ⟨39569100136704349707332881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52758800182272466276443841 39569100136704349707332881)
      ·
        refine ⟨29676825102528262280499661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39569100136704349707332881 29676825102528262280499661)
        ·
          refine ⟨11128809413448098355187373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29676825102528262280499661 11128809413448098355187373)
          ·
            refine ⟨4173303530043036883195265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11128809413448098355187373 4173303530043036883195265)
            ·
              refine ⟨3129977647532277662396449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173303530043036883195265 3129977647532277662396449)
              ·
                refine ⟨2347483235649208246797337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3129977647532277662396449 2347483235649208246797337)
                ·
                  refine ⟨1760612426736906185098003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347483235649208246797337 1760612426736906185098003)
                  ·
                    refine ⟨2640918640105359277647005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760612426736906185098003 2640918640105359277647005)
                    ·
                      refine ⟨990344490039509729117627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2640918640105359277647005 990344490039509729117627)
                      ·
                        rfl

theorem cell23_1928689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_1928689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928689 prefixEnd_1928689 := by exact prefixLift 1928689
  have htrace : WordTrace (prefixWord ++ tailWord_1928689) baseStart_1928689 baseEnd_1928689 := by
    simpa [prefixWord, tailWord_1928689, baseEnd_1928689] using wordTrace_append hprefix tailTrace_1928689
  have hstable : (prefixWord ++ tailWord_1928689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928689).length < 2 ^ (prefixWord ++ tailWord_1928689).sum := by decide
  have hdescent : baseEnd_1928689 < baseStart_1928689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928690 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1928690 : Nat := 118140960795 + 1928690 * 2 ^ 59
def prefixEnd_1928690 : Nat := 4983230072969 + 3 ^ 40 * 1928690 * 2
def baseEnd_1928690 : Nat := 990345003520164225205123

theorem tailTrace_1928690 : CollatzResearch.WordTrace tailWord_1928690 prefixEnd_1928690 990345003520164225205123 := by
  unfold tailWord_1928690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586275845673249718177881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46896735588461999248474349 17586275845673249718177881)
  ·
    refine ⟨13189706884254937288633411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17586275845673249718177881 13189706884254937288633411)
    ·
      refine ⟨19784560326382405932950117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189706884254937288633411 19784560326382405932950117)
      ·
        refine ⟨3709605061196701112428147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19784560326382405932950117 3709605061196701112428147)
        ·
          refine ⟨5564407591795051668642221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709605061196701112428147 5564407591795051668642221)
          ·
            refine ⟨2086652846923144375740833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5564407591795051668642221 2086652846923144375740833)
            ·
              refine ⟨1564989635192358281805625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086652846923144375740833 1564989635192358281805625)
              ·
                refine ⟨1173742226394268711354219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564989635192358281805625 1173742226394268711354219)
                ·
                  refine ⟨1760613339591403067031329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173742226394268711354219 1760613339591403067031329)
                  ·
                    refine ⟨1320460004693552300273497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760613339591403067031329 1320460004693552300273497)
                    ·
                      refine ⟨990345003520164225205123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320460004693552300273497 990345003520164225205123)
                      ·
                        rfl

theorem cell23_1928690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1928690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928690 prefixEnd_1928690 := by exact prefixLift 1928690
  have htrace : WordTrace (prefixWord ++ tailWord_1928690) baseStart_1928690 baseEnd_1928690 := by
    simpa [prefixWord, tailWord_1928690, baseEnd_1928690] using wordTrace_append hprefix tailTrace_1928690
  have hstable : (prefixWord ++ tailWord_1928690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928690).length < 2 ^ (prefixWord ++ tailWord_1928690).sum := by decide
  have hdescent : baseEnd_1928690 < baseStart_1928690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928706 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1928706 : Nat := 118140960795 + 1928706 * 2 ^ 59
def prefixEnd_1928706 : Nat := 4983230072969 + 3 ^ 40 * 1928706 * 2
def baseEnd_1928706 : Nat := 990353219210636162605049

theorem tailTrace_1928706 : CollatzResearch.WordTrace tailWord_1928706 prefixEnd_1928706 990353219210636162605049 := by
  unfold tailWord_1928706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586421737658758401323493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46897124633756689070195981 17586421737658758401323493)
  ·
    refine ⟨3297454075811017200248155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17586421737658758401323493 3297454075811017200248155)
    ·
      refine ⟨4946181113716525800372233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297454075811017200248155 4946181113716525800372233)
      ·
        refine ⟨3709635835287394350279175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946181113716525800372233 3709635835287394350279175)
        ·
          refine ⟨5564453752931091525418763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709635835287394350279175 5564453752931091525418763)
          ·
            refine ⟨8346680629396637288128145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564453752931091525418763 8346680629396637288128145)
            ·
              refine ⟨6260010472047477966096109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346680629396637288128145 6260010472047477966096109)
              ·
                refine ⟨2347503927017804237286041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6260010472047477966096109 2347503927017804237286041)
                ·
                  refine ⟨1760627945263353177964531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347503927017804237286041 1760627945263353177964531)
                  ·
                    refine ⟨2640941917895029766946797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760627945263353177964531 2640941917895029766946797)
                    ·
                      refine ⟨990353219210636162605049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2640941917895029766946797 990353219210636162605049)
                      ·
                        rfl

theorem cell23_1928706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1928706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928706 prefixEnd_1928706 := by exact prefixLift 1928706
  have htrace : WordTrace (prefixWord ++ tailWord_1928706) baseStart_1928706 baseEnd_1928706 := by
    simpa [prefixWord, tailWord_1928706, baseEnd_1928706] using wordTrace_append hprefix tailTrace_1928706
  have hstable : (prefixWord ++ tailWord_1928706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928706).length < 2 ^ (prefixWord ++ tailWord_1928706).sum := by decide
  have hdescent : baseEnd_1928706 < baseStart_1928706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928712 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_1928712 : Nat := 118140960795 + 1928712 * 2 ^ 59
def prefixEnd_1928712 : Nat := 4983230072969 + 3 ^ 40 * 1928712 * 2
def baseEnd_1928712 : Nat := 990356300094563139130021

theorem tailTrace_1928712 : CollatzResearch.WordTrace tailWord_1928712 prefixEnd_1928712 990356300094563139130021 := by
  unfold tailWord_1928712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172952894306648315006195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46897270525742197753341593 35172952894306648315006195)
  ·
    refine ⟨52759429341459972472509293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35172952894306648315006195 52759429341459972472509293)
    ·
      refine ⟨19784786003047489677190985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52759429341459972472509293 19784786003047489677190985)
      ·
        refine ⟨14838589502285617257893239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19784786003047489677190985 14838589502285617257893239)
        ·
          refine ⟨22257884253428425886839859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14838589502285617257893239 22257884253428425886839859)
          ·
            refine ⟨33386826380142638830259789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22257884253428425886839859 33386826380142638830259789)
            ·
              refine ⟨12520059892553489561347421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33386826380142638830259789 12520059892553489561347421)
              ·
                refine ⟨4695022459707558585505283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12520059892553489561347421 4695022459707558585505283)
                ·
                  refine ⟨7042533689561337878257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695022459707558585505283 7042533689561337878257925)
                  ·
                    refine ⟨1320475066792750852173361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042533689561337878257925 1320475066792750852173361)
                    ·
                      refine ⟨990356300094563139130021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320475066792750852173361 990356300094563139130021)
                      ·
                        rfl

theorem cell23_1928712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_1928712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928712 prefixEnd_1928712 := by exact prefixLift 1928712
  have htrace : WordTrace (prefixWord ++ tailWord_1928712) baseStart_1928712 baseEnd_1928712 := by
    simpa [prefixWord, tailWord_1928712, baseEnd_1928712] using wordTrace_append hprefix tailTrace_1928712
  have hstable : (prefixWord ++ tailWord_1928712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928712).length < 2 ^ (prefixWord ++ tailWord_1928712).sum := by decide
  have hdescent : baseEnd_1928712 < baseStart_1928712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928785 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1928785 : Nat := 118140960795 + 1928785 * 2 ^ 59
def prefixEnd_1928785 : Nat := 4983230072969 + 3 ^ 40 * 1928785 * 2
def baseEnd_1928785 : Nat := 990393784182341353517185

theorem tailTrace_1928785 : CollatzResearch.WordTrace tailWord_1928785 prefixEnd_1928785 990393784182341353517185 := by
  unfold tailWord_1928785
  simp only [CollatzResearch.WordTrace]
  refine ⟨70348568317348830097419809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46899045544899220064946539 70348568317348830097419809)
  ·
    refine ⟨52761426238011622573064857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70348568317348830097419809 52761426238011622573064857)
    ·
      refine ⟨39571069678508716929798643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52761426238011622573064857 39571069678508716929798643)
      ·
        refine ⟨59356604517763075394697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39571069678508716929798643 59356604517763075394697965)
        ·
          refine ⟨22258726694161153273011737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59356604517763075394697965 22258726694161153273011737)
          ·
            refine ⟨16694045020620864954758803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22258726694161153273011737 16694045020620864954758803)
            ·
              refine ⟨25041067530931297432138205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16694045020620864954758803 25041067530931297432138205)
              ·
                refine ⟨9390400324099236537051827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25041067530931297432138205 9390400324099236537051827)
                ·
                  refine ⟨14085600486148854805577741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390400324099236537051827 14085600486148854805577741)
                  ·
                    refine ⟨5282100182305820552091653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14085600486148854805577741 5282100182305820552091653)
                    ·
                      refine ⟨990393784182341353517185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5282100182305820552091653 990393784182341353517185)
                      ·
                        rfl

theorem cell23_1928785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1928785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928785 prefixEnd_1928785 := by exact prefixLift 1928785
  have htrace : WordTrace (prefixWord ++ tailWord_1928785) baseStart_1928785 baseEnd_1928785 := by
    simpa [prefixWord, tailWord_1928785, baseEnd_1928785] using wordTrace_append hprefix tailTrace_1928785
  have hstable : (prefixWord ++ tailWord_1928785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928785).length < 2 ^ (prefixWord ++ tailWord_1928785).sum := by decide
  have hdescent : baseEnd_1928785 < baseStart_1928785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928839 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1928839 : Nat := 118140960795 + 1928839 * 2 ^ 59
def prefixEnd_1928839 : Nat := 4983230072969 + 3 ^ 40 * 1928839 * 2
def baseEnd_1928839 : Nat := 990421512137684142241937

theorem tailTrace_1928839 : CollatzResearch.WordTrace tailWord_1928839 prefixEnd_1928839 990421512137684142241937 := by
  unfold tailWord_1928839
  simp only [CollatzResearch.WordTrace]
  refine ⟨70350537859153197319885571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46900358572768798213257047 70350537859153197319885571)
  ·
    refine ⟨105525806788729795979828357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70350537859153197319885571 105525806788729795979828357)
    ·
      refine ⟨19786088772886836746217817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105525806788729795979828357 19786088772886836746217817)
      ·
        refine ⟨14839566579665127559663363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19786088772886836746217817 14839566579665127559663363)
        ·
          refine ⟨22259349869497691339495045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14839566579665127559663363 22259349869497691339495045)
          ·
            refine ⟨4173628100530817126155321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22259349869497691339495045 4173628100530817126155321)
            ·
              refine ⟨3130221075398112844616491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173628100530817126155321 3130221075398112844616491)
              ·
                refine ⟨4695331613097169266924737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130221075398112844616491 4695331613097169266924737)
                ·
                  refine ⟨3521498709822876950193553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695331613097169266924737 3521498709822876950193553)
                  ·
                    refine ⟨2641124032367157712645165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3521498709822876950193553 2641124032367157712645165)
                    ·
                      refine ⟨990421512137684142241937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641124032367157712645165 990421512137684142241937)
                      ·
                        rfl

theorem cell23_1928839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1928839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928839 prefixEnd_1928839 := by exact prefixLift 1928839
  have htrace : WordTrace (prefixWord ++ tailWord_1928839) baseStart_1928839 baseEnd_1928839 := by
    simpa [prefixWord, tailWord_1928839, baseEnd_1928839] using wordTrace_append hprefix tailTrace_1928839
  have hstable : (prefixWord ++ tailWord_1928839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928839).length < 2 ^ (prefixWord ++ tailWord_1928839).sum := by decide
  have hdescent : baseEnd_1928839 < baseStart_1928839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928863 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 1, 4]
def baseStart_1928863 : Nat := 118140960795 + 1928863 * 2 ^ 59
def prefixEnd_1928863 : Nat := 4983230072969 + 3 ^ 40 * 1928863 * 2
def baseEnd_1928863 : Nat := 330144611891130682780609

theorem tailTrace_1928863 : CollatzResearch.WordTrace tailWord_1928863 prefixEnd_1928863 330144611891130682780609 := by
  unfold tailWord_1928863
  simp only [CollatzResearch.WordTrace]
  refine ⟨70351413211066249418759243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46900942140710832945839495 70351413211066249418759243)
  ·
    refine ⟨105527119816599374128138865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70351413211066249418759243 105527119816599374128138865)
    ·
      refine ⟨79145339862449530596104149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105527119816599374128138865 79145339862449530596104149)
      ·
        refine ⟨1854968903026160873346191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79145339862449530596104149 1854968903026160873346191)
        ·
          refine ⟨2782453354539241310019287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854968903026160873346191 2782453354539241310019287)
          ·
            refine ⟨4173680031808861965028931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782453354539241310019287 4173680031808861965028931)
            ·
              refine ⟨6260520047713292947543397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173680031808861965028931 6260520047713292947543397)
              ·
                refine ⟨1173847508946242427664387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6260520047713292947543397 1173847508946242427664387)
                ·
                  refine ⟨1760771263419363641496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173847508946242427664387 1760771263419363641496581)
                  ·
                    refine ⟨330144611891130682780609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760771263419363641496581 330144611891130682780609)
                    ·
                      rfl

theorem cell23_1928863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_1928863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928863 prefixEnd_1928863 := by exact prefixLift 1928863
  have htrace : WordTrace (prefixWord ++ tailWord_1928863) baseStart_1928863 baseEnd_1928863 := by
    simpa [prefixWord, tailWord_1928863, baseEnd_1928863] using wordTrace_append hprefix tailTrace_1928863
  have hstable : (prefixWord ++ tailWord_1928863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928863).length < 2 ^ (prefixWord ++ tailWord_1928863).sum := by decide
  have hdescent : baseEnd_1928863 < baseStart_1928863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928912 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_1928912 : Nat := 118140960795 + 1928912 * 2 ^ 59
def prefixEnd_1928912 : Nat := 4983230072969 + 3 ^ 40 * 1928912 * 2
def baseEnd_1928912 : Nat := 990458996225462356629101

theorem tailTrace_1928912 : CollatzResearch.WordTrace tailWord_1928912 prefixEnd_1928912 990458996225462356629101 := by
  unfold tailWord_1928912
  simp only [CollatzResearch.WordTrace]
  refine ⟨35176600193944365393646495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46902133591925820524861993 35176600193944365393646495)
  ·
    refine ⟨52764900290916548090469743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35176600193944365393646495 52764900290916548090469743)
    ·
      refine ⟨79147350436374822135704615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52764900290916548090469743 79147350436374822135704615)
      ·
        refine ⟨118721025654562233203556923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79147350436374822135704615 118721025654562233203556923)
        ·
          refine ⟨178081538481843349805335385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118721025654562233203556923 178081538481843349805335385)
          ·
            refine ⟨133561153861382512354001539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178081538481843349805335385 133561153861382512354001539)
            ·
              refine ⟨200341730792073768531002309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133561153861382512354001539 200341730792073768531002309)
              ·
                refine ⟨37564074523513831599562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200341730792073768531002309 37564074523513831599562933)
                ·
                  refine ⟨3521631986579421712459025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37564074523513831599562933 3521631986579421712459025)
                  ·
                    refine ⟨2641223989934566284344269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3521631986579421712459025 2641223989934566284344269)
                    ·
                      refine ⟨990458996225462356629101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641223989934566284344269 990458996225462356629101)
                      ·
                        rfl

theorem cell23_1928912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_1928912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928912 prefixEnd_1928912 := by exact prefixLift 1928912
  have htrace : WordTrace (prefixWord ++ tailWord_1928912) baseStart_1928912 baseEnd_1928912 := by
    simpa [prefixWord, tailWord_1928912, baseEnd_1928912] using wordTrace_append hprefix tailTrace_1928912
  have hstable : (prefixWord ++ tailWord_1928912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928912).length < 2 ^ (prefixWord ++ tailWord_1928912).sum := by decide
  have hdescent : baseEnd_1928912 < baseStart_1928912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928929 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1928929 : Nat := 118140960795 + 1928929 * 2 ^ 59
def prefixEnd_1928929 : Nat := 4983230072969 + 3 ^ 40 * 1928929 * 2
def baseEnd_1928929 : Nat := 990467725396588790116523

theorem tailTrace_1928929 : CollatzResearch.WordTrace tailWord_1928929 prefixEnd_1928929 990467725396588790116523 := by
  unfold tailWord_1928929
  simp only [CollatzResearch.WordTrace]
  refine ⟨70353820428827142690661841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46902546952551428460441227 70353820428827142690661841)
  ·
    refine ⟨52765365321620357017996381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70353820428827142690661841 52765365321620357017996381)
    ·
      refine ⟨19787011995607633881748643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52765365321620357017996381 19787011995607633881748643)
      ·
        refine ⟨29680517993411450822622965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787011995607633881748643 29680517993411450822622965)
        ·
          refine ⟨2782548561882323514620903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29680517993411450822622965 2782548561882323514620903)
          ·
            refine ⟨4173822842823485271931355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782548561882323514620903 4173822842823485271931355)
            ·
              refine ⟨6260734264235227907897033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173822842823485271931355 6260734264235227907897033)
              ·
                refine ⟨4695550698176420930922775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6260734264235227907897033 4695550698176420930922775)
                ·
                  refine ⟨7043326047264631396384163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695550698176420930922775 7043326047264631396384163)
                  ·
                    refine ⟨10564989070896947094576245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043326047264631396384163 10564989070896947094576245)
                    ·
                      refine ⟨990467725396588790116523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10564989070896947094576245 990467725396588790116523)
                      ·
                        rfl

theorem cell23_1928929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1928929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928929 prefixEnd_1928929 := by exact prefixLift 1928929
  have htrace : WordTrace (prefixWord ++ tailWord_1928929) baseStart_1928929 baseEnd_1928929 := by
    simpa [prefixWord, tailWord_1928929, baseEnd_1928929] using wordTrace_append hprefix tailTrace_1928929
  have hstable : (prefixWord ++ tailWord_1928929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928929).length < 2 ^ (prefixWord ++ tailWord_1928929).sum := by decide
  have hdescent : baseEnd_1928929 < baseStart_1928929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928946 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1928946 : Nat := 118140960795 + 1928946 * 2 ^ 59
def prefixEnd_1928946 : Nat := 4983230072969 + 3 ^ 40 * 1928946 * 2
def baseEnd_1928946 : Nat := 990476454567715223603945

theorem tailTrace_1928946 : CollatzResearch.WordTrace tailWord_1928946 prefixEnd_1928946 990476454567715223603945 := by
  unfold tailWord_1928946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17588610117441388648507673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46902960313177036396020461 17588610117441388648507673)
  ·
    refine ⟨13191457588081041486380755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17588610117441388648507673 13191457588081041486380755)
    ·
      refine ⟨19787186382121562229571133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191457588081041486380755 19787186382121562229571133)
      ·
        refine ⟨7420194893295585836089175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19787186382121562229571133 7420194893295585836089175)
        ·
          refine ⟨11130292339943378754133763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420194893295585836089175 11130292339943378754133763)
          ·
            refine ⟨16695438509915068131200645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130292339943378754133763 16695438509915068131200645)
            ·
              refine ⟨3130394720609075274600121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16695438509915068131200645 3130394720609075274600121)
              ·
                refine ⟨2347796040456806455950091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130394720609075274600121 2347796040456806455950091)
                ·
                  refine ⟨3521694060685209683925137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347796040456806455950091 3521694060685209683925137)
                  ·
                    refine ⟨2641270545513907262943853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3521694060685209683925137 2641270545513907262943853)
                    ·
                      refine ⟨990476454567715223603945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641270545513907262943853 990476454567715223603945)
                      ·
                        rfl

theorem cell23_1928946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1928946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928946 prefixEnd_1928946 := by exact prefixLift 1928946
  have htrace : WordTrace (prefixWord ++ tailWord_1928946) baseStart_1928946 baseEnd_1928946 := by
    simpa [prefixWord, tailWord_1928946, baseEnd_1928946] using wordTrace_append hprefix tailTrace_1928946
  have hstable : (prefixWord ++ tailWord_1928946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928946).length < 2 ^ (prefixWord ++ tailWord_1928946).sum := by decide
  have hdescent : baseEnd_1928946 < baseStart_1928946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928959 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_1928959 : Nat := 118140960795 + 1928959 * 2 ^ 59
def prefixEnd_1928959 : Nat := 4983230072969 + 3 ^ 40 * 1928959 * 2
def baseEnd_1928959 : Nat := 990483129816223672741385

theorem tailTrace_1928959 : CollatzResearch.WordTrace tailWord_1928959 prefixEnd_1928959 990483129816223672741385 := by
  unfold tailWord_1928959
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354914618718457814253931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46903276412478971876169287 70354914618718457814253931)
  ·
    refine ⟨105532371928077686721380897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354914618718457814253931 105532371928077686721380897)
    ·
      refine ⟨79149278946058265041035673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105532371928077686721380897 79149278946058265041035673)
      ·
        refine ⟨59361959209543698780776755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79149278946058265041035673 59361959209543698780776755)
        ·
          refine ⟨89042938814315548171165133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59361959209543698780776755 89042938814315548171165133)
          ·
            refine ⟨33391102055368330564186925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89042938814315548171165133 33391102055368330564186925)
            ·
              refine ⟨12521663270763123961570097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33391102055368330564186925 12521663270763123961570097)
              ·
                refine ⟨9391247453072342971177573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12521663270763123961570097 9391247453072342971177573)
                ·
                  refine ⟨1760858897451064307095795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9391247453072342971177573 1760858897451064307095795)
                  ·
                    refine ⟨2641288346176596460643693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760858897451064307095795 2641288346176596460643693)
                    ·
                      refine ⟨990483129816223672741385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641288346176596460643693 990483129816223672741385)
                      ·
                        rfl

theorem cell23_1928959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_1928959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928959 prefixEnd_1928959 := by exact prefixLift 1928959
  have htrace : WordTrace (prefixWord ++ tailWord_1928959) baseStart_1928959 baseEnd_1928959 := by
    simpa [prefixWord, tailWord_1928959, baseEnd_1928959] using wordTrace_append hprefix tailTrace_1928959
  have hstable : (prefixWord ++ tailWord_1928959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928959).length < 2 ^ (prefixWord ++ tailWord_1928959).sum := by decide
  have hdescent : baseEnd_1928959 < baseStart_1928959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928969 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 5, 3, 2]
def baseStart_1928969 : Nat := 118140960795 + 1928969 * 2 ^ 59
def prefixEnd_1928969 : Nat := 4983230072969 + 3 ^ 40 * 1928969 * 2
def baseEnd_1928969 : Nat := 990488264622768633616339

theorem tailTrace_1928969 : CollatzResearch.WordTrace tailWord_1928969 prefixEnd_1928969 990488264622768633616339 := by
  unfold tailWord_1928969
  simp only [CollatzResearch.WordTrace]
  refine ⟨70355279348682229522117961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46903519565788153014745307 70355279348682229522117961)
  ·
    refine ⟨52766459511511672141588471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70355279348682229522117961 52766459511511672141588471)
    ·
      refine ⟨79149689267267508212382707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52766459511511672141588471 79149689267267508212382707)
      ·
        refine ⟨118724533900901262318574061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79149689267267508212382707 118724533900901262318574061)
        ·
          refine ⟨44521700212837973369465273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118724533900901262318574061 44521700212837973369465273)
          ·
            refine ⟨33391275159628480027098955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44521700212837973369465273 33391275159628480027098955)
            ·
              refine ⟨50086912739442720040648433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33391275159628480027098955 50086912739442720040648433)
              ·
                refine ⟨37565184554582040030486325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50086912739442720040648433 37565184554582040030486325)
                ·
                  refine ⟨3521736051992066252858093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37565184554582040030486325 3521736051992066252858093)
                  ·
                    refine ⟨1320651019497024844821785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521736051992066252858093 1320651019497024844821785)
                    ·
                      refine ⟨990488264622768633616339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320651019497024844821785 990488264622768633616339)
                      ·
                        rfl

theorem cell23_1928969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3, 2].length) (baseStart_1928969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928969 prefixEnd_1928969 := by exact prefixLift 1928969
  have htrace : WordTrace (prefixWord ++ tailWord_1928969) baseStart_1928969 baseEnd_1928969 := by
    simpa [prefixWord, tailWord_1928969, baseEnd_1928969] using wordTrace_append hprefix tailTrace_1928969
  have hstable : (prefixWord ++ tailWord_1928969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928969).length < 2 ^ (prefixWord ++ tailWord_1928969).sum := by decide
  have hdescent : baseEnd_1928969 < baseStart_1928969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928992 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_1928992 : Nat := 118140960795 + 1928992 * 2 ^ 59
def prefixEnd_1928992 : Nat := 4983230072969 + 3 ^ 40 * 1928992 * 2
def baseEnd_1928992 : Nat := 330166691559274014542911

theorem tailTrace_1928992 : CollatzResearch.WordTrace tailWord_1928992 prefixEnd_1928992 330166691559274014542911 := by
  unfold tailWord_1928992
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178059113799452225102615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46904078818399269633470153 35178059113799452225102615)
  ·
    refine ⟨52767088670699178337653923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35178059113799452225102615 52767088670699178337653923)
    ·
      refine ⟨79150633006048767506480885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52767088670699178337653923 79150633006048767506480885)
      ·
        refine ⟨7420371844317071953732583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79150633006048767506480885 7420371844317071953732583)
        ·
          refine ⟨11130557766475607930598875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420371844317071953732583 11130557766475607930598875)
          ·
            refine ⟨16695836649713411895898313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130557766475607930598875 16695836649713411895898313)
            ·
              refine ⟨12521877487285058921923735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16695836649713411895898313 12521877487285058921923735)
              ·
                refine ⟨18782816230927588382885603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12521877487285058921923735 18782816230927588382885603)
                ·
                  refine ⟨28174224346391382574328405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18782816230927588382885603 28174224346391382574328405)
                  ·
                    refine ⟨330166691559274014542911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28174224346391382574328405 330166691559274014542911)
                    ·
                      rfl

theorem cell23_1928992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_1928992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928992 prefixEnd_1928992 := by exact prefixLift 1928992
  have htrace : WordTrace (prefixWord ++ tailWord_1928992) baseStart_1928992 baseEnd_1928992 := by
    simpa [prefixWord, tailWord_1928992, baseEnd_1928992] using wordTrace_append hprefix tailTrace_1928992
  have hstable : (prefixWord ++ tailWord_1928992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928992).length < 2 ^ (prefixWord ++ tailWord_1928992).sum := by decide
  have hdescent : baseEnd_1928992 < baseStart_1928992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928993 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1928993 : Nat := 118140960795 + 1928993 * 2 ^ 59
def prefixEnd_1928993 : Nat := 4983230072969 + 3 ^ 40 * 1928993 * 2
def baseEnd_1928993 : Nat := 990500588158476539716229

theorem tailTrace_1928993 : CollatzResearch.WordTrace tailWord_1928993 prefixEnd_1928993 990500588158476539716229 := by
  unfold tailWord_1928993
  simp only [CollatzResearch.WordTrace]
  refine ⟨70356154700595281620991633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46904103133730187747327755 70356154700595281620991633)
  ·
    refine ⟨52767116025446461215743725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70356154700595281620991633 52767116025446461215743725)
    ·
      refine ⟨19787668509542422955903897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52767116025446461215743725 19787668509542422955903897)
      ·
        refine ⟨14840751382156817216927923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19787668509542422955903897 14840751382156817216927923)
        ·
          refine ⟨22261127073235225825391885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840751382156817216927923 22261127073235225825391885)
          ·
            refine ⟨8347922652463209684521957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22261127073235225825391885 8347922652463209684521957)
            ·
              refine ⟨1565235497336851815847867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8347922652463209684521957 1565235497336851815847867)
              ·
                refine ⟨2347853246005277723771801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565235497336851815847867 2347853246005277723771801)
                ·
                  refine ⟨1760889934503958292828851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347853246005277723771801 1760889934503958292828851)
                  ·
                    refine ⟨2641334901755937439243277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760889934503958292828851 2641334901755937439243277)
                    ·
                      refine ⟨990500588158476539716229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641334901755937439243277 990500588158476539716229)
                      ·
                        rfl

theorem cell23_1928993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1928993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1928993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1928993 prefixEnd_1928993 := by exact prefixLift 1928993
  have htrace : WordTrace (prefixWord ++ tailWord_1928993) baseStart_1928993 baseEnd_1928993 := by
    simpa [prefixWord, tailWord_1928993, baseEnd_1928993] using wordTrace_append hprefix tailTrace_1928993
  have hstable : (prefixWord ++ tailWord_1928993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928993).length < 2 ^ (prefixWord ++ tailWord_1928993).sum := by decide
  have hdescent : baseEnd_1928993 < baseStart_1928993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929016 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_1929016 : Nat := 118140960795 + 1929016 * 2 ^ 59
def prefixEnd_1929016 : Nat := 4983230072969 + 3 ^ 40 * 1929016 * 2
def baseEnd_1929016 : Nat := 990512398213529949728623

theorem tailTrace_1929016 : CollatzResearch.WordTrace tailWord_1929016 prefixEnd_1929016 990512398213529949728623 := by
  unfold tailWord_1929016
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178496789755978274539451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46904662386341304366052601 35178496789755978274539451)
  ·
    refine ⟨52767745184633967411809177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35178496789755978274539451 52767745184633967411809177)
    ·
      refine ⟨39575808888475475558856883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52767745184633967411809177 39575808888475475558856883)
      ·
        refine ⟨59363713332713213338285325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39575808888475475558856883 59363713332713213338285325)
        ·
          refine ⟨22261392499767455001856997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59363713332713213338285325 22261392499767455001856997)
          ·
            refine ⟨4174011093706397812848187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22261392499767455001856997 4174011093706397812848187)
            ·
              refine ⟨6261016640559596719272281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174011093706397812848187 6261016640559596719272281)
              ·
                refine ⟨4695762480419697539454211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261016640559596719272281 4695762480419697539454211)
                ·
                  refine ⟨7043643720629546309181317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695762480419697539454211 7043643720629546309181317)
                  ·
                    refine ⟨1320683197618039932971497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043643720629546309181317 1320683197618039932971497)
                    ·
                      refine ⟨990512398213529949728623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320683197618039932971497 990512398213529949728623)
                      ·
                        rfl

theorem cell23_1929016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_1929016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929016 prefixEnd_1929016 := by exact prefixLift 1929016
  have htrace : WordTrace (prefixWord ++ tailWord_1929016) baseStart_1929016 baseEnd_1929016 := by
    simpa [prefixWord, tailWord_1929016, baseEnd_1929016] using wordTrace_append hprefix tailTrace_1929016
  have hstable : (prefixWord ++ tailWord_1929016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929016).length < 2 ^ (prefixWord ++ tailWord_1929016).sum := by decide
  have hdescent : baseEnd_1929016 < baseStart_1929016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929033 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 2, 2, 2]
def baseStart_1929033 : Nat := 118140960795 + 1929033 * 2 ^ 59
def prefixEnd_1929033 : Nat := 4983230072969 + 3 ^ 40 * 1929033 * 2
def baseEnd_1929033 : Nat := 990521127384656383216045

theorem tailTrace_1929033 : CollatzResearch.WordTrace tailWord_1929033 prefixEnd_1929033 990521127384656383216045 := by
  unfold tailWord_1929033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70357613620450368452447753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46905075746966912301631835 70357613620450368452447753)
  ·
    refine ⟨52768210215337776339335815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70357613620450368452447753 52768210215337776339335815)
    ·
      refine ⟨79152315323006664509003723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52768210215337776339335815 79152315323006664509003723)
      ·
        refine ⟨118728472984509996763505585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79152315323006664509003723 118728472984509996763505585)
        ·
          refine ⟨89046354738382497572629189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118728472984509996763505585 89046354738382497572629189)
          ·
            refine ⟨16696191513446718294867973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89046354738382497572629189 16696191513446718294867973)
            ·
              refine ⟨3130535908771259680287745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16696191513446718294867973 3130535908771259680287745)
              ·
                refine ⟨2347901931578444760215809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130535908771259680287745 2347901931578444760215809)
                ·
                  refine ⟨1760926448683833570161857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347901931578444760215809 1760926448683833570161857)
                  ·
                    refine ⟨1320694836512875177621393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760926448683833570161857 1320694836512875177621393)
                    ·
                      refine ⟨990521127384656383216045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320694836512875177621393 990521127384656383216045)
                      ·
                        rfl

theorem cell23_1929033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2, 2].length) (baseStart_1929033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929033 prefixEnd_1929033 := by exact prefixLift 1929033
  have htrace : WordTrace (prefixWord ++ tailWord_1929033) baseStart_1929033 baseEnd_1929033 := by
    simpa [prefixWord, tailWord_1929033, baseEnd_1929033] using wordTrace_append hprefix tailTrace_1929033
  have hstable : (prefixWord ++ tailWord_1929033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929033).length < 2 ^ (prefixWord ++ tailWord_1929033).sum := by decide
  have hdescent : baseEnd_1929033 < baseStart_1929033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929049 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1929049 : Nat := 118140960795 + 1929049 * 2 ^ 59
def prefixEnd_1929049 : Nat := 4983230072969 + 3 ^ 40 * 1929049 * 2
def baseEnd_1929049 : Nat := 990529343075128320615971

theorem tailTrace_1929049 : CollatzResearch.WordTrace tailWord_1929049 prefixEnd_1929049 990529343075128320615971 := by
  unfold tailWord_1929049
  simp only [CollatzResearch.WordTrace]
  refine ⟨70358197188392403185030201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46905464792261602123353467 70358197188392403185030201)
  ·
    refine ⟨52768647891294302388772651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70358197188392403185030201 52768647891294302388772651)
    ·
      refine ⟨79152971836941453583158977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52768647891294302388772651 79152971836941453583158977)
      ·
        refine ⟨59364728877706090187369233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79152971836941453583158977 59364728877706090187369233)
        ·
          refine ⟨44523546658279567640526925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59364728877706090187369233 44523546658279567640526925)
          ·
            refine ⟨16696329996854837865197597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44523546658279567640526925 16696329996854837865197597)
            ·
              refine ⟨6261123748820564199449099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16696329996854837865197597 6261123748820564199449099)
              ·
                refine ⟨9391685623230846299173649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261123748820564199449099 9391685623230846299173649)
                ·
                  refine ⟨7043764217423134724380237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9391685623230846299173649 7043764217423134724380237)
                  ·
                    refine ⟨2641411581533675521642589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7043764217423134724380237 2641411581533675521642589)
                    ·
                      refine ⟨990529343075128320615971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641411581533675521642589 990529343075128320615971)
                      ·
                        rfl

theorem cell23_1929049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1929049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929049 prefixEnd_1929049 := by exact prefixLift 1929049
  have htrace : WordTrace (prefixWord ++ tailWord_1929049) baseStart_1929049 baseEnd_1929049 := by
    simpa [prefixWord, tailWord_1929049, baseEnd_1929049] using wordTrace_append hprefix tailTrace_1929049
  have hstable : (prefixWord ++ tailWord_1929049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929049).length < 2 ^ (prefixWord ++ tailWord_1929049).sum := by decide
  have hdescent : baseEnd_1929049 < baseStart_1929049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929106 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1929106 : Nat := 118140960795 + 1929106 * 2 ^ 59
def prefixEnd_1929106 : Nat := 4983230072969 + 3 ^ 40 * 1929106 * 2
def baseEnd_1929106 : Nat := 990558611472434597603209

theorem tailTrace_1929106 : CollatzResearch.WordTrace tailWord_1929106 prefixEnd_1929106 990558611472434597603209 := by
  unfold tailWord_1929106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590069037296475479963793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46906850766123934613236781 17590069037296475479963793)
  ·
    refine ⟨13192551777972356609972845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17590069037296475479963793 13192551777972356609972845)
    ·
      refine ⟨4947206916739633728739817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13192551777972356609972845 4947206916739633728739817)
      ·
        refine ⟨3710405187554725296554863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947206916739633728739817 3710405187554725296554863)
        ·
          refine ⟨5565607781332087944832295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710405187554725296554863 5565607781332087944832295)
          ·
            refine ⟨8348411671998131917248443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565607781332087944832295 8348411671998131917248443)
            ·
              refine ⟨12522617507997197875872665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348411671998131917248443 12522617507997197875872665)
              ·
                refine ⟨9391963130997898406904499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522617507997197875872665 9391963130997898406904499)
                ·
                  refine ⟨14087944696496847610356749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391963130997898406904499 14087944696496847610356749)
                  ·
                    refine ⟨5282979261186317853883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14087944696496847610356749 5282979261186317853883781)
                    ·
                      refine ⟨990558611472434597603209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5282979261186317853883781 990558611472434597603209)
                      ·
                        rfl

theorem cell23_1929106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1929106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929106 prefixEnd_1929106 := by exact prefixLift 1929106
  have htrace : WordTrace (prefixWord ++ tailWord_1929106) baseStart_1929106 baseEnd_1929106 := by
    simpa [prefixWord, tailWord_1929106, baseEnd_1929106] using wordTrace_append hprefix tailTrace_1929106
  have hstable : (prefixWord ++ tailWord_1929106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929106).length < 2 ^ (prefixWord ++ tailWord_1929106).sum := by decide
  have hdescent : baseEnd_1929106 < baseStart_1929106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929109 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1929109 : Nat := 118140960795 + 1929109 * 2 ^ 59
def prefixEnd_1929109 : Nat := 4983230072969 + 3 ^ 40 * 1929109 * 2
def baseEnd_1929109 : Nat := 990560151914398085865695

theorem tailTrace_1929109 : CollatzResearch.WordTrace tailWord_1929109 prefixEnd_1929109 990560151914398085865695 := by
  unfold tailWord_1929109
  simp only [CollatzResearch.WordTrace]
  refine ⟨70360385568175033432214381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46906923712116688954809587 70360385568175033432214381)
  ·
    refine ⟨26385144588065637537080393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70360385568175033432214381 26385144588065637537080393)
    ·
      refine ⟨19788858441049228152810295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26385144588065637537080393 19788858441049228152810295)
      ·
        refine ⟨29683287661573842229215443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788858441049228152810295 29683287661573842229215443)
        ·
          refine ⟨44524931492360763343823165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29683287661573842229215443 44524931492360763343823165)
          ·
            refine ⟨16696849309635286253933687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44524931492360763343823165 16696849309635286253933687)
            ·
              refine ⟨25045273964452929380900531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16696849309635286253933687 25045273964452929380900531)
              ·
                refine ⟨37567910946679394071350797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25045273964452929380900531 37567910946679394071350797)
                ·
                  refine ⟨14087966605004772776756549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37567910946679394071350797 14087966605004772776756549)
                  ·
                    refine ⟨2641493738438394895641853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14087966605004772776756549 2641493738438394895641853)
                    ·
                      refine ⟨990560151914398085865695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641493738438394895641853 990560151914398085865695)
                      ·
                        rfl

theorem cell23_1929109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1929109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929109 prefixEnd_1929109 := by exact prefixLift 1929109
  have htrace : WordTrace (prefixWord ++ tailWord_1929109) baseStart_1929109 baseEnd_1929109 := by
    simpa [prefixWord, tailWord_1929109, baseEnd_1929109] using wordTrace_append hprefix tailTrace_1929109
  have hstable : (prefixWord ++ tailWord_1929109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929109).length < 2 ^ (prefixWord ++ tailWord_1929109).sum := by decide
  have hdescent : baseEnd_1929109 < baseStart_1929109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929140 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1929140 : Nat := 118140960795 + 1929140 * 2 ^ 59
def prefixEnd_1929140 : Nat := 4983230072969 + 3 ^ 40 * 1929140 * 2
def baseEnd_1929140 : Nat := 990576069814687464578053

theorem tailTrace_1929140 : CollatzResearch.WordTrace tailWord_1929140 prefixEnd_1929140 990576069814687464578053 := by
  unfold tailWord_1929140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35180758115531362863296437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46907677487375150484395249 35180758115531362863296437)
  ·
    refine ⟨3298196073331065268434041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35180758115531362863296437 3298196073331065268434041)
    ·
      refine ⟨2473647054998298951325531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3298196073331065268434041 2473647054998298951325531)
      ·
        refine ⟨3710470582497448426988297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473647054998298951325531 3710470582497448426988297)
        ·
          refine ⟨2782852936873086320241223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3710470582497448426988297 2782852936873086320241223)
          ·
            refine ⟨4174279405309629480361835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782852936873086320241223 4174279405309629480361835)
            ·
              refine ⟨6261419107964444220542753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174279405309629480361835 6261419107964444220542753)
              ·
                refine ⟨4696064330973333165407065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261419107964444220542753 4696064330973333165407065)
                ·
                  refine ⟨3522048248229999874055299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696064330973333165407065 3522048248229999874055299)
                  ·
                    refine ⟨5283072372344999811082949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522048248229999874055299 5283072372344999811082949)
                    ·
                      refine ⟨990576069814687464578053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5283072372344999811082949 990576069814687464578053)
                      ·
                        rfl

theorem cell23_1929140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1929140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929140 prefixEnd_1929140 := by exact prefixLift 1929140
  have htrace : WordTrace (prefixWord ++ tailWord_1929140) baseStart_1929140 baseEnd_1929140 := by
    simpa [prefixWord, tailWord_1929140, baseEnd_1929140] using wordTrace_append hprefix tailTrace_1929140
  have hstable : (prefixWord ++ tailWord_1929140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929140).length < 2 ^ (prefixWord ++ tailWord_1929140).sum := by decide
  have hdescent : baseEnd_1929140 < baseStart_1929140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929159 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1929159 : Nat := 118140960795 + 1929159 * 2 ^ 59
def prefixEnd_1929159 : Nat := 4983230072969 + 3 ^ 40 * 1929159 * 2
def baseEnd_1929159 : Nat := 330195275315707630080155

theorem tailTrace_1929159 : CollatzResearch.WordTrace tailWord_1929159 prefixEnd_1929159 330195275315707630080155 := by
  unfold tailWord_1929159
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362209217993891971534531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46908139478662594647689687 70362209217993891971534531)
  ·
    refine ⟨105543313826990837957301797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70362209217993891971534531 105543313826990837957301797)
    ·
      refine ⟨19789371342560782116994087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105543313826990837957301797 19789371342560782116994087)
      ·
        refine ⟨29684057013841173175491131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789371342560782116994087 29684057013841173175491131)
        ·
          refine ⟨44526085520761759763236697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684057013841173175491131 44526085520761759763236697)
          ·
            refine ⟨33394564140571319822427523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44526085520761759763236697 33394564140571319822427523)
            ·
              refine ⟨50091846210856979733641285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33394564140571319822427523 50091846210856979733641285)
              ·
                refine ⟨9392221164535683700057741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50091846210856979733641285 9392221164535683700057741)
                ·
                  refine ⟨3522082936700881387521653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392221164535683700057741 3522082936700881387521653)
                  ·
                    refine ⟨330195275315707630080155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3522082936700881387521653 330195275315707630080155)
                    ·
                      rfl

theorem cell23_1929159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1929159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929159 prefixEnd_1929159 := by exact prefixLift 1929159
  have htrace : WordTrace (prefixWord ++ tailWord_1929159) baseStart_1929159 baseEnd_1929159 := by
    simpa [prefixWord, tailWord_1929159, baseEnd_1929159] using wordTrace_append hprefix tailTrace_1929159
  have hstable : (prefixWord ++ tailWord_1929159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929159).length < 2 ^ (prefixWord ++ tailWord_1929159).sum := by decide
  have hdescent : baseEnd_1929159 < baseStart_1929159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929183 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 2, 3, 2]
def baseStart_1929183 : Nat := 118140960795 + 1929183 * 2 ^ 59
def prefixEnd_1929183 : Nat := 4983230072969 + 3 ^ 40 * 1929183 * 2
def baseEnd_1929183 : Nat := 990598149482830796340355

theorem tailTrace_1929183 : CollatzResearch.WordTrace tailWord_1929183 prefixEnd_1929183 990598149482830796340355 := by
  unfold tailWord_1929183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70363084569906944070408203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46908723046604629380272135 70363084569906944070408203)
  ·
    refine ⟨105544626854860416105612305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70363084569906944070408203 105544626854860416105612305)
    ·
      refine ⟨79158470141145312079209229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105544626854860416105612305 79158470141145312079209229)
      ·
        refine ⟨29684426302929492029703461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79158470141145312079209229 29684426302929492029703461)
        ·
          refine ⟨5565829931799279755569399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29684426302929492029703461 5565829931799279755569399)
          ·
            refine ⟨8348744897698919633354099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565829931799279755569399 8348744897698919633354099)
            ·
              refine ⟨12523117346548379450031149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348744897698919633354099 12523117346548379450031149)
              ·
                refine ⟨4696169004955642293761681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12523117346548379450031149 4696169004955642293761681)
                ·
                  refine ⟨3522126753716731720321261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696169004955642293761681 3522126753716731720321261)
                  ·
                    refine ⟨1320797532643774395120473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522126753716731720321261 1320797532643774395120473)
                    ·
                      refine ⟨990598149482830796340355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320797532643774395120473 990598149482830796340355)
                      ·
                        rfl

theorem cell23_1929183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_1929183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929183 prefixEnd_1929183 := by exact prefixLift 1929183
  have htrace : WordTrace (prefixWord ++ tailWord_1929183) baseStart_1929183 baseEnd_1929183 := by
    simpa [prefixWord, tailWord_1929183, baseEnd_1929183] using wordTrace_append hprefix tailTrace_1929183
  have hstable : (prefixWord ++ tailWord_1929183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929183).length < 2 ^ (prefixWord ++ tailWord_1929183).sum := by decide
  have hdescent : baseEnd_1929183 < baseStart_1929183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929196 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_1929196 : Nat := 118140960795 + 1929196 * 2 ^ 59
def prefixEnd_1929196 : Nat := 4983230072969 + 3 ^ 40 * 1929196 * 2
def baseEnd_1929196 : Nat := 990604824731339245477795

theorem tailTrace_1929196 : CollatzResearch.WordTrace tailWord_1929196 prefixEnd_1929196 990604824731339245477795 := by
  unfold tailWord_1929196
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181779359429923645315721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46909039145906564860420961 35181779359429923645315721)
  ·
    refine ⟨26386334519572442733986791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35181779359429923645315721 26386334519572442733986791)
    ·
      refine ⟨39579501779358664100980187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26386334519572442733986791 39579501779358664100980187)
      ·
        refine ⟨59369252669037996151470281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39579501779358664100980187 59369252669037996151470281)
        ·
          refine ⟨44526939501778497113602711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59369252669037996151470281 44526939501778497113602711)
          ·
            refine ⟨66790409252667745670404067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44526939501778497113602711 66790409252667745670404067)
            ·
              refine ⟨100185613879001618505606101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66790409252667745670404067 100185613879001618505606101)
              ·
                refine ⟨2348100325289100433725143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100185613879001618505606101 2348100325289100433725143)
                ·
                  refine ⟨3522150487933650650587715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348100325289100433725143 3522150487933650650587715)
                  ·
                    refine ⟨5283225731900475975881573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522150487933650650587715 5283225731900475975881573)
                    ·
                      refine ⟨990604824731339245477795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5283225731900475975881573 990604824731339245477795)
                      ·
                        rfl

theorem cell23_1929196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_1929196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929196 prefixEnd_1929196 := by exact prefixLift 1929196
  have htrace : WordTrace (prefixWord ++ tailWord_1929196) baseStart_1929196 baseEnd_1929196 := by
    simpa [prefixWord, tailWord_1929196, baseEnd_1929196] using wordTrace_append hprefix tailTrace_1929196
  have hstable : (prefixWord ++ tailWord_1929196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929196).length < 2 ^ (prefixWord ++ tailWord_1929196).sum := by decide
  have hdescent : baseEnd_1929196 < baseStart_1929196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929223 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1929223 : Nat := 118140960795 + 1929223 * 2 ^ 59
def prefixEnd_1929223 : Nat := 4983230072969 + 3 ^ 40 * 1929223 * 2
def baseEnd_1929223 : Nat := 330206229569670213280057

theorem tailTrace_1929223 : CollatzResearch.WordTrace tailWord_1929223 prefixEnd_1929223 330206229569670213280057 := by
  unfold tailWord_1929223
  simp only [CollatzResearch.WordTrace]
  refine ⟨70364543489762030901864323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46909695659841353934576215 70364543489762030901864323)
  ·
    refine ⟨105546815234643046352796485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70364543489762030901864323 105546815234643046352796485)
    ·
      refine ⟨19790027856495571191149341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105546815234643046352796485 19790027856495571191149341)
      ·
        refine ⟨7421260446185839196681003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19790027856495571191149341 7421260446185839196681003)
        ·
          refine ⟨11131890669278758795021505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421260446185839196681003 11131890669278758795021505)
          ·
            refine ⟨8348918001959069096266129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11131890669278758795021505 8348918001959069096266129)
            ·
              refine ⟨6261688501469301822199597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8348918001959069096266129 6261688501469301822199597)
              ·
                refine ⟨2348133188050988183324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6261688501469301822199597 2348133188050988183324849)
                ·
                  refine ⟨1761099891038241137493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348133188050988183324849 1761099891038241137493637)
                  ·
                    refine ⟨330206229569670213280057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1761099891038241137493637 330206229569670213280057)
                    ·
                      rfl

theorem cell23_1929223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1929223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929223 prefixEnd_1929223 := by exact prefixLift 1929223
  have htrace : WordTrace (prefixWord ++ tailWord_1929223) baseStart_1929223 baseEnd_1929223 := by
    simpa [prefixWord, tailWord_1929223, baseEnd_1929223] using wordTrace_append hprefix tailTrace_1929223
  have hstable : (prefixWord ++ tailWord_1929223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929223).length < 2 ^ (prefixWord ++ tailWord_1929223).sum := by decide
  have hdescent : baseEnd_1929223 < baseStart_1929223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929230 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1929230 : Nat := 118140960795 + 1929230 * 2 ^ 59
def prefixEnd_1929230 : Nat := 4983230072969 + 3 ^ 40 * 1929230 * 2
def baseEnd_1929230 : Nat := 990622283073592112452639

theorem tailTrace_1929230 : CollatzResearch.WordTrace tailWord_1929230 prefixEnd_1929230 990622283073592112452639 := by
  unfold tailWord_1929230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795599850092083887171143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46909865867157780731579429 8795599850092083887171143)
  ·
    refine ⟨13193399775138125830756715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795599850092083887171143 13193399775138125830756715)
    ·
      refine ⟨19790099662707188746135073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13193399775138125830756715 19790099662707188746135073)
      ·
        refine ⟨14842574747030391559601305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19790099662707188746135073 14842574747030391559601305)
        ·
          refine ⟨11131931060272793669700979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14842574747030391559601305 11131931060272793669700979)
          ·
            refine ⟨16697896590409190504551469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131931060272793669700979 16697896590409190504551469)
            ·
              refine ⟨6261711221403446439206801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16697896590409190504551469 6261711221403446439206801)
              ·
                refine ⟨4696283416052584829405101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261711221403446439206801 4696283416052584829405101)
                ·
                  refine ⟨1761106281019719311026913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4696283416052584829405101 1761106281019719311026913)
                  ·
                    refine ⟨1320829710764789483270185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761106281019719311026913 1320829710764789483270185)
                    ·
                      refine ⟨990622283073592112452639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320829710764789483270185 990622283073592112452639)
                      ·
                        rfl

theorem cell23_1929230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1929230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929230 prefixEnd_1929230 := by exact prefixLift 1929230
  have htrace : WordTrace (prefixWord ++ tailWord_1929230) baseStart_1929230 baseEnd_1929230 := by
    simpa [prefixWord, tailWord_1929230, baseEnd_1929230] using wordTrace_append hprefix tailTrace_1929230
  have hstable : (prefixWord ++ tailWord_1929230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929230).length < 2 ^ (prefixWord ++ tailWord_1929230).sum := by decide
  have hdescent : baseEnd_1929230 < baseStart_1929230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929247 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 1, 2, 2]
def baseStart_1929247 : Nat := 118140960795 + 1929247 * 2 ^ 59
def prefixEnd_1929247 : Nat := 4983230072969 + 3 ^ 40 * 1929247 * 2
def baseEnd_1929247 : Nat := 990631012244718545940061

theorem tailTrace_1929247 : CollatzResearch.WordTrace tailWord_1929247 prefixEnd_1929247 990631012244718545940061 := by
  unfold tailWord_1929247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70365418841675083000737995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46910279227783388667158663 70365418841675083000737995)
  ·
    refine ⟨105548128262512624501106993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70365418841675083000737995 105548128262512624501106993)
    ·
      refine ⟨79161096196884468375830245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105548128262512624501106993 79161096196884468375830245)
      ·
        refine ⟨14842705536915837820468171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79161096196884468375830245 14842705536915837820468171)
        ·
          refine ⟨22264058305373756730702257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14842705536915837820468171 22264058305373756730702257)
          ·
            refine ⟨16698043729030317548026693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22264058305373756730702257 16698043729030317548026693)
            ·
              refine ⟨3130883199193184540255005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16698043729030317548026693 3130883199193184540255005)
              ·
                refine ⟨1174081199697444202595627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3130883199193184540255005 1174081199697444202595627)
                ·
                  refine ⟨1761121799546166303893441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174081199697444202595627 1761121799546166303893441)
                  ·
                    refine ⟨1320841349659624727920081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761121799546166303893441 1320841349659624727920081)
                    ·
                      refine ⟨990631012244718545940061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320841349659624727920081 990631012244718545940061)
                      ·
                        rfl

theorem cell23_1929247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_1929247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929247 prefixEnd_1929247 := by exact prefixLift 1929247
  have htrace : WordTrace (prefixWord ++ tailWord_1929247) baseStart_1929247 baseEnd_1929247 := by
    simpa [prefixWord, tailWord_1929247, baseEnd_1929247] using wordTrace_append hprefix tailTrace_1929247
  have hstable : (prefixWord ++ tailWord_1929247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929247).length < 2 ^ (prefixWord ++ tailWord_1929247).sum := by decide
  have hdescent : baseEnd_1929247 < baseStart_1929247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929259 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_1929259 : Nat := 118140960795 + 1929259 * 2 ^ 59
def prefixEnd_1929259 : Nat := 4983230072969 + 3 ^ 40 * 1929259 * 2
def baseEnd_1929259 : Nat := 990637174012572498990005

theorem tailTrace_1929259 : CollatzResearch.WordTrace tailWord_1929259 prefixEnd_1929259 990637174012572498990005 := by
  unfold tailWord_1929259
  simp only [CollatzResearch.WordTrace]
  refine ⟨70365856517631609050174831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46910571011754406033449887 70365856517631609050174831)
  ·
    refine ⟨105548784776447413575262247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70365856517631609050174831 105548784776447413575262247)
    ·
      refine ⟨158323177164671120362893371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105548784776447413575262247 158323177164671120362893371)
      ·
        refine ⟨237484765747006680544340057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158323177164671120362893371 237484765747006680544340057)
        ·
          refine ⟨178113574310255010408255043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237484765747006680544340057 178113574310255010408255043)
          ·
            refine ⟨267170361465382515612382565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178113574310255010408255043 267170361465382515612382565)
            ·
              refine ⟨50094442774759221677321731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267170361465382515612382565 50094442774759221677321731)
              ·
                refine ⟨75141664162138832515982597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50094442774759221677321731 75141664162138832515982597)
                ·
                  refine ⟨14089062030401031096746737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75141664162138832515982597 14089062030401031096746737)
                  ·
                    refine ⟨10566796522800773322560053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14089062030401031096746737 10566796522800773322560053)
                    ·
                      refine ⟨990637174012572498990005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10566796522800773322560053 990637174012572498990005)
                      ·
                        rfl

theorem cell23_1929259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_1929259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929259 prefixEnd_1929259 := by exact prefixLift 1929259
  have htrace : WordTrace (prefixWord ++ tailWord_1929259) baseStart_1929259 baseEnd_1929259 := by
    simpa [prefixWord, tailWord_1929259, baseEnd_1929259] using wordTrace_append hprefix tailTrace_1929259
  have hstable : (prefixWord ++ tailWord_1929259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929259).length < 2 ^ (prefixWord ++ tailWord_1929259).sum := by decide
  have hdescent : baseEnd_1929259 < baseStart_1929259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929263 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_1929263 : Nat := 118140960795 + 1929263 * 2 ^ 59
def prefixEnd_1929263 : Nat := 4983230072969 + 3 ^ 40 * 1929263 * 2
def baseEnd_1929263 : Nat := 990639227935190483339987

theorem tailTrace_1929263 : CollatzResearch.WordTrace tailWord_1929263 prefixEnd_1929263 990639227935190483339987 := by
  unfold tailWord_1929263
  simp only [CollatzResearch.WordTrace]
  refine ⟨70366002409617117733320443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46910668273078078488880295 70366002409617117733320443)
  ·
    refine ⟨105549003614425676599980665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70366002409617117733320443 105549003614425676599980665)
    ·
      refine ⟨79161752710819257449985499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105549003614425676599980665 79161752710819257449985499)
      ·
        refine ⟨118742629066228886174978249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79161752710819257449985499 118742629066228886174978249)
        ·
          refine ⟨89056971799671664631233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118742629066228886174978249 89056971799671664631233687)
          ·
            refine ⟨133585457699507496946850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89056971799671664631233687 133585457699507496946850531)
            ·
              refine ⟨200378186549261245420275797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133585457699507496946850531 200378186549261245420275797)
              ·
                refine ⟨2348181873624155219768857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 200378186549261245420275797 2348181873624155219768857)
                ·
                  refine ⟨1761136405218116414826643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348181873624155219768857 1761136405218116414826643)
                  ·
                    refine ⟨2641704607827174622239965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761136405218116414826643 2641704607827174622239965)
                    ·
                      refine ⟨990639227935190483339987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641704607827174622239965 990639227935190483339987)
                      ·
                        rfl

theorem cell23_1929263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_1929263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929263 prefixEnd_1929263 := by exact prefixLift 1929263
  have htrace : WordTrace (prefixWord ++ tailWord_1929263) baseStart_1929263 baseEnd_1929263 := by
    simpa [prefixWord, tailWord_1929263, baseEnd_1929263] using wordTrace_append hprefix tailTrace_1929263
  have hstable : (prefixWord ++ tailWord_1929263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929263).length < 2 ^ (prefixWord ++ tailWord_1929263).sum := by decide
  have hdescent : baseEnd_1929263 < baseStart_1929263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929299 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1929299 : Nat := 118140960795 + 1929299 * 2 ^ 59
def prefixEnd_1929299 : Nat := 4983230072969 + 3 ^ 40 * 1929299 * 2
def baseEnd_1929299 : Nat := 990657713238752342489821

theorem tailTrace_1929299 : CollatzResearch.WordTrace tailWord_1929299 prefixEnd_1929299 990657713238752342489821 := by
  unfold tailWord_1929299
  simp only [CollatzResearch.WordTrace]
  refine ⟨70367315437486695881630951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46911543624991130587753967 70367315437486695881630951)
  ·
    refine ⟨105550973156230043822446427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70367315437486695881630951 105550973156230043822446427)
    ·
      refine ⟨158326459734345065733669641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105550973156230043822446427 158326459734345065733669641)
      ·
        refine ⟨118744844800758799300252231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158326459734345065733669641 118744844800758799300252231)
        ·
          refine ⟨178117267201138198950378347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118744844800758799300252231 178117267201138198950378347)
          ·
            refine ⟨267175900801707298425567521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178117267201138198950378347 267175900801707298425567521)
            ·
              refine ⟨200381925601280473819175641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267175900801707298425567521 200381925601280473819175641)
              ·
                refine ⟨150286444200960355364381731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200381925601280473819175641 150286444200960355364381731)
                ·
                  refine ⟨225429666301440533046572597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150286444200960355364381731 225429666301440533046572597)
                  ·
                    refine ⟨21134031215760049973116181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225429666301440533046572597 21134031215760049973116181)
                    ·
                      refine ⟨990657713238752342489821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21134031215760049973116181 990657713238752342489821)
                      ·
                        rfl

theorem cell23_1929299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1929299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929299 prefixEnd_1929299 := by exact prefixLift 1929299
  have htrace : WordTrace (prefixWord ++ tailWord_1929299) baseStart_1929299 baseEnd_1929299 := by
    simpa [prefixWord, tailWord_1929299, baseEnd_1929299] using wordTrace_append hprefix tailTrace_1929299
  have hstable : (prefixWord ++ tailWord_1929299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929299).length < 2 ^ (prefixWord ++ tailWord_1929299).sum := by decide
  have hdescent : baseEnd_1929299 < baseStart_1929299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929303 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_1929303 : Nat := 118140960795 + 1929303 * 2 ^ 59
def prefixEnd_1929303 : Nat := 4983230072969 + 3 ^ 40 * 1929303 * 2
def baseEnd_1929303 : Nat := 990659767161370326839803

theorem tailTrace_1929303 : CollatzResearch.WordTrace tailWord_1929303 prefixEnd_1929303 990659767161370326839803 := by
  unfold tailWord_1929303
  simp only [CollatzResearch.WordTrace]
  refine ⟨70367461329472204564776563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46911640886314803043184375 70367461329472204564776563)
  ·
    refine ⟨105551191994208306847164845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70367461329472204564776563 105551191994208306847164845)
    ·
      refine ⟨39581696997828115067686817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105551191994208306847164845 39581696997828115067686817)
      ·
        refine ⟨29686272748371086300765113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39581696997828115067686817 29686272748371086300765113)
        ·
          refine ⟨22264704561278314725573835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29686272748371086300765113 22264704561278314725573835)
          ·
            refine ⟨33397056841917472088360753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22264704561278314725573835 33397056841917472088360753)
            ·
              refine ⟨25047792631438104066270565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33397056841917472088360753 25047792631438104066270565)
              ·
                refine ⟨4696461118394644512425731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25047792631438104066270565 4696461118394644512425731)
                ·
                  refine ⟨7044691677591966768638597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696461118394644512425731 7044691677591966768638597)
                  ·
                    refine ⟨1320879689548493769119737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044691677591966768638597 1320879689548493769119737)
                    ·
                      refine ⟨990659767161370326839803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320879689548493769119737 990659767161370326839803)
                      ·
                        rfl

theorem cell23_1929303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_1929303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929303 prefixEnd_1929303 := by exact prefixLift 1929303
  have htrace : WordTrace (prefixWord ++ tailWord_1929303) baseStart_1929303 baseEnd_1929303 := by
    simpa [prefixWord, tailWord_1929303, baseEnd_1929303] using wordTrace_append hprefix tailTrace_1929303
  have hstable : (prefixWord ++ tailWord_1929303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929303).length < 2 ^ (prefixWord ++ tailWord_1929303).sum := by decide
  have hdescent : baseEnd_1929303 < baseStart_1929303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929306 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1929306 : Nat := 118140960795 + 1929306 * 2 ^ 59
def prefixEnd_1929306 : Nat := 4983230072969 + 3 ^ 40 * 1929306 * 2
def baseEnd_1929306 : Nat := 990661307603333815102289

theorem tailTrace_1929306 : CollatzResearch.WordTrace tailWord_1929306 prefixEnd_1929306 990661307603333815102289 := by
  unfold tailWord_1929306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17591892687115334019283943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46911713832307557384757181 17591892687115334019283943)
  ·
    refine ⟨26387839030673001028925915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17591892687115334019283943 26387839030673001028925915)
    ·
      refine ⟨39581758546009501543388873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26387839030673001028925915 39581758546009501543388873)
      ·
        refine ⟨29686318909507126157541655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39581758546009501543388873 29686318909507126157541655)
        ·
          refine ⟨44529478364260689236312483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29686318909507126157541655 44529478364260689236312483)
          ·
            refine ⟨66794217546391033854468725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44529478364260689236312483 66794217546391033854468725)
            ·
              refine ⟨6261957894974159423856443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66794217546391033854468725 6261957894974159423856443)
              ·
                refine ⟨9392936842461239135784665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261957894974159423856443 9392936842461239135784665)
                ·
                  refine ⟨7044702631845929351838499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9392936842461239135784665 7044702631845929351838499)
                  ·
                    refine ⟨10567053947768894027757749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044702631845929351838499 10567053947768894027757749)
                    ·
                      refine ⟨990661307603333815102289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10567053947768894027757749 990661307603333815102289)
                      ·
                        rfl

theorem cell23_1929306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1929306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929306 prefixEnd_1929306 := by exact prefixLift 1929306
  have htrace : WordTrace (prefixWord ++ tailWord_1929306) baseStart_1929306 baseEnd_1929306 := by
    simpa [prefixWord, tailWord_1929306, baseEnd_1929306] using wordTrace_append hprefix tailTrace_1929306
  have hstable : (prefixWord ++ tailWord_1929306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929306).length < 2 ^ (prefixWord ++ tailWord_1929306).sum := by decide
  have hdescent : baseEnd_1929306 < baseStart_1929306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929316 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1929316 : Nat := 118140960795 + 1929316 * 2 ^ 59
def prefixEnd_1929316 : Nat := 4983230072969 + 3 ^ 40 * 1929316 * 2
def baseEnd_1929316 : Nat := 990666442409878775977243

theorem tailTrace_1929316 : CollatzResearch.WordTrace tailWord_1929316 prefixEnd_1929316 990666442409878775977243 := by
  unfold tailWord_1929316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35183967739212553892499901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46911956985616738523333201 35183967739212553892499901)
  ·
    refine ⟨13193987902204707709687463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35183967739212553892499901 13193987902204707709687463)
    ·
      refine ⟨19790981853307061564531195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13193987902204707709687463 19790981853307061564531195)
      ·
        refine ⟨29686472779960592346796793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19790981853307061564531195 29686472779960592346796793)
        ·
          refine ⟨22264854584970444260097595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29686472779960592346796793 22264854584970444260097595)
          ·
            refine ⟨33397281877455666390146393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22264854584970444260097595 33397281877455666390146393)
            ·
              refine ⟨25047961408091749792609795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33397281877455666390146393 25047961408091749792609795)
              ·
                refine ⟨37571942112137624688914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25047961408091749792609795 37571942112137624688914693)
                ·
                  refine ⟨7044739146025804629171505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37571942112137624688914693 7044739146025804629171505)
                  ·
                    refine ⟨5283554359519353471878629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7044739146025804629171505 5283554359519353471878629)
                    ·
                      refine ⟨990666442409878775977243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5283554359519353471878629 990666442409878775977243)
                      ·
                        rfl

theorem cell23_1929316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1929316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929316 prefixEnd_1929316 := by exact prefixLift 1929316
  have htrace : WordTrace (prefixWord ++ tailWord_1929316) baseStart_1929316 baseEnd_1929316 := by
    simpa [prefixWord, tailWord_1929316, baseEnd_1929316] using wordTrace_append hprefix tailTrace_1929316
  have hstable : (prefixWord ++ tailWord_1929316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929316).length < 2 ^ (prefixWord ++ tailWord_1929316).sum := by decide
  have hdescent : baseEnd_1929316 < baseStart_1929316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929336 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1929336 : Nat := 118140960795 + 1929336 * 2 ^ 59
def prefixEnd_1929336 : Nat := 4983230072969 + 3 ^ 40 * 1929336 * 2
def baseEnd_1929336 : Nat := 990676712022968697727151

theorem tailTrace_1929336 : CollatzResearch.WordTrace tailWord_1929336 prefixEnd_1929336 990676712022968697727151 := by
  unfold tailWord_1929336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35184332469176325600363931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46912443292235100800485241 35184332469176325600363931)
  ·
    refine ⟨52776498703764488400545897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35184332469176325600363931 52776498703764488400545897)
    ·
      refine ⟨39582374027823366300409423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52776498703764488400545897 39582374027823366300409423)
      ·
        refine ⟨59373561041735049450614135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39582374027823366300409423 59373561041735049450614135)
        ·
          refine ⟨89060341562602574175921203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59373561041735049450614135 89060341562602574175921203)
          ·
            refine ⟨133590512343903861263881805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89060341562602574175921203 133590512343903861263881805)
            ·
              refine ⟨50096442128963947973955677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133590512343903861263881805 50096442128963947973955677)
              ·
                refine ⟨18786165798361480490233379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50096442128963947973955677 18786165798361480490233379)
                ·
                  refine ⟨28179248697542220735350069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18786165798361480490233379 28179248697542220735350069)
                  ·
                    refine ⟨2641804565394583193939069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28179248697542220735350069 2641804565394583193939069)
                    ·
                      refine ⟨990676712022968697727151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641804565394583193939069 990676712022968697727151)
                      ·
                        rfl

theorem cell23_1929336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1929336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929336 prefixEnd_1929336 := by exact prefixLift 1929336
  have htrace : WordTrace (prefixWord ++ tailWord_1929336) baseStart_1929336 baseEnd_1929336 := by
    simpa [prefixWord, tailWord_1929336, baseEnd_1929336] using wordTrace_append hprefix tailTrace_1929336
  have hstable : (prefixWord ++ tailWord_1929336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929336).length < 2 ^ (prefixWord ++ tailWord_1929336).sum := by decide
  have hdescent : baseEnd_1929336 < baseStart_1929336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929337 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 2, 2, 2]
def baseStart_1929337 : Nat := 118140960795 + 1929337 * 2 ^ 59
def prefixEnd_1929337 : Nat := 4983230072969 + 3 ^ 40 * 1929337 * 2
def baseEnd_1929337 : Nat := 990677225503623193814647

theorem tailTrace_1929337 : CollatzResearch.WordTrace tailWord_1929337 prefixEnd_1929337 990677225503623193814647 := by
  unfold tailWord_1929337
  simp only [CollatzResearch.WordTrace]
  refine ⟨70368701411349028371514265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46912467607566018914342843 70368701411349028371514265)
  ·
    refine ⟨52776526058511771278635699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70368701411349028371514265 52776526058511771278635699)
    ·
      refine ⟨79164789087767656917953549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52776526058511771278635699 79164789087767656917953549)
      ·
        refine ⟨29686795907912871344232581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79164789087767656917953549 29686795907912871344232581)
        ·
          refine ⟨5566274232733663377043609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29686795907912871344232581 5566274232733663377043609)
          ·
            refine ⟨4174705674550247532782707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566274232733663377043609 4174705674550247532782707)
            ·
              refine ⟨6262058511825371299174061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174705674550247532782707 6262058511825371299174061)
              ·
                refine ⟨2348271941934514237190273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6262058511825371299174061 2348271941934514237190273)
                ·
                  refine ⟨1761203956450885677892705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348271941934514237190273 1761203956450885677892705)
                  ·
                    refine ⟨1320902967338164258419529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761203956450885677892705 1320902967338164258419529)
                    ·
                      refine ⟨990677225503623193814647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1320902967338164258419529 990677225503623193814647)
                      ·
                        rfl

theorem cell23_1929337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_1929337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929337 prefixEnd_1929337 := by exact prefixLift 1929337
  have htrace : WordTrace (prefixWord ++ tailWord_1929337) baseStart_1929337 baseEnd_1929337 := by
    simpa [prefixWord, tailWord_1929337, baseEnd_1929337] using wordTrace_append hprefix tailTrace_1929337
  have hstable : (prefixWord ++ tailWord_1929337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929337).length < 2 ^ (prefixWord ++ tailWord_1929337).sum := by decide
  have hdescent : baseEnd_1929337 < baseStart_1929337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929373 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1929373 : Nat := 118140960795 + 1929373 * 2 ^ 59
def prefixEnd_1929373 : Nat := 4983230072969 + 3 ^ 40 * 1929373 * 2
def baseEnd_1929373 : Nat := 330231903602395017654827

theorem tailTrace_1929373 : CollatzResearch.WordTrace tailWord_1929373 prefixEnd_1929373 330231903602395017654827 := by
  unfold tailWord_1929373
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370014439218606519824773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46913342959479071013216515 70370014439218606519824773)
  ·
    refine ⟨13194377707353488722467145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70370014439218606519824773 13194377707353488722467145)
    ·
      refine ⟨9895783280515116541850359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13194377707353488722467145 9895783280515116541850359)
      ·
        refine ⟨14843674920772674812775539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895783280515116541850359 14843674920772674812775539)
        ·
          refine ⟨22265512381159012219163309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843674920772674812775539 22265512381159012219163309)
          ·
            refine ⟨8349567142934629582186241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22265512381159012219163309 8349567142934629582186241)
            ·
              refine ⟨6262175357200972186639681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8349567142934629582186241 6262175357200972186639681)
              ·
                refine ⟨4696631517900729139979761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262175357200972186639681 4696631517900729139979761)
                ·
                  refine ⟨3522473638425546854984821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696631517900729139979761 3522473638425546854984821)
                  ·
                    refine ⟨330231903602395017654827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3522473638425546854984821 330231903602395017654827)
                    ·
                      rfl

theorem cell23_1929373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1929373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929373 prefixEnd_1929373 := by exact prefixLift 1929373
  have htrace : WordTrace (prefixWord ++ tailWord_1929373) baseStart_1929373 baseEnd_1929373 := by
    simpa [prefixWord, tailWord_1929373, baseEnd_1929373] using wordTrace_append hprefix tailTrace_1929373
  have hstable : (prefixWord ++ tailWord_1929373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929373).length < 2 ^ (prefixWord ++ tailWord_1929373).sum := by decide
  have hdescent : baseEnd_1929373 < baseStart_1929373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929377 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 5]
def baseStart_1929377 : Nat := 118140960795 + 1929377 * 2 ^ 59
def prefixEnd_1929377 : Nat := 4983230072969 + 3 ^ 40 * 1929377 * 2
def baseEnd_1929377 : Nat := 110077529414422559701607

theorem tailTrace_1929377 : CollatzResearch.WordTrace tailWord_1929377 prefixEnd_1929377 110077529414422559701607 := by
  unfold tailWord_1929377
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370160331204115202970385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46913440220802743468646923 70370160331204115202970385)
  ·
    refine ⟨52777620248403086402227789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70370160331204115202970385 52777620248403086402227789)
    ·
      refine ⟨19791607593151157400835421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52777620248403086402227789 19791607593151157400835421)
      ·
        refine ⟨7421852847431684025313283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19791607593151157400835421 7421852847431684025313283)
        ·
          refine ⟨11132779271147526037969925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421852847431684025313283 11132779271147526037969925)
          ·
            refine ⟨2087396113340161132119361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11132779271147526037969925 2087396113340161132119361)
            ·
              refine ⟨1565547085005120849089521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087396113340161132119361 1565547085005120849089521)
              ·
                refine ⟨1174160313753840636817141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565547085005120849089521 1174160313753840636817141)
                ·
                  refine ⟨110077529414422559701607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174160313753840636817141 110077529414422559701607)
                  ·
                    rfl

theorem cell23_1929377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 5].length) (baseStart_1929377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929377 prefixEnd_1929377 := by exact prefixLift 1929377
  have htrace : WordTrace (prefixWord ++ tailWord_1929377) baseStart_1929377 baseEnd_1929377 := by
    simpa [prefixWord, tailWord_1929377, baseEnd_1929377] using wordTrace_append hprefix tailTrace_1929377
  have hstable : (prefixWord ++ tailWord_1929377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929377).length < 2 ^ (prefixWord ++ tailWord_1929377).sum := by decide
  have hdescent : baseEnd_1929377 < baseStart_1929377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929403 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 3, 4]
def baseStart_1929403 : Nat := 118140960795 + 1929403 * 2 ^ 59
def prefixEnd_1929403 : Nat := 4983230072969 + 3 ^ 40 * 1929403 * 2
def baseEnd_1929403 : Nat := 330237038408939978529781

theorem tailTrace_1929403 : CollatzResearch.WordTrace tailWord_1929403 prefixEnd_1929403 330237038408939978529781 := by
  unfold tailWord_1929403
  simp only [CollatzResearch.WordTrace]
  refine ⟨70371108629109921643416863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914072419406614428944575 70371108629109921643416863)
  ·
    refine ⟨105556662943664882465125295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70371108629109921643416863 105556662943664882465125295)
    ·
      refine ⟨158334994415497323697687943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105556662943664882465125295 158334994415497323697687943)
      ·
        refine ⟨237502491623245985546531915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158334994415497323697687943 237502491623245985546531915)
        ·
          refine ⟨356253737434868978319797873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237502491623245985546531915 356253737434868978319797873)
          ·
            refine ⟨267190303076151733739848405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356253737434868978319797873 267190303076151733739848405)
            ·
              refine ⟨6262272728347306259527697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267190303076151733739848405 6262272728347306259527697)
              ·
                refine ⟨4696704546260479694645773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262272728347306259527697 4696704546260479694645773)
                ·
                  refine ⟨1761264204847679885492165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4696704546260479694645773 1761264204847679885492165)
                  ·
                    refine ⟨330237038408939978529781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1761264204847679885492165 330237038408939978529781)
                    ·
                      rfl

theorem cell23_1929403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 4].length) (baseStart_1929403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929403 prefixEnd_1929403 := by exact prefixLift 1929403
  have htrace : WordTrace (prefixWord ++ tailWord_1929403) baseStart_1929403 baseEnd_1929403 := by
    simpa [prefixWord, tailWord_1929403, baseEnd_1929403] using wordTrace_append hprefix tailTrace_1929403
  have hstable : (prefixWord ++ tailWord_1929403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929403).length < 2 ^ (prefixWord ++ tailWord_1929403).sum := by decide
  have hdescent : baseEnd_1929403 < baseStart_1929403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929416 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 8]
def baseStart_1929416 : Nat := 118140960795 + 1929416 * 2 ^ 59
def prefixEnd_1929416 : Nat := 4983230072969 + 3 ^ 40 * 1929416 * 2
def baseEnd_1929416 : Nat := 110079754497258709414087

theorem tailTrace_1929416 : CollatzResearch.WordTrace tailWord_1929416 prefixEnd_1929416 110079754497258709414087 := by
  unfold tailWord_1929416
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185791389031412431820051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46914388518708549909093401 35185791389031412431820051)
  ·
    refine ⟨52778687083547118647730077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185791389031412431820051 52778687083547118647730077)
    ·
      refine ⟨19792007656330169492898779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52778687083547118647730077 19792007656330169492898779)
      ·
        refine ⟨29688011484495254239348169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19792007656330169492898779 29688011484495254239348169)
        ·
          refine ⟨22266008613371440679511127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29688011484495254239348169 22266008613371440679511127)
          ·
            refine ⟨33399012920057161019266691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22266008613371440679511127 33399012920057161019266691)
            ·
              refine ⟨50098519380085741528900037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33399012920057161019266691 50098519380085741528900037)
              ·
                refine ⟨9393472383766076536668757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50098519380085741528900037 9393472383766076536668757)
                ·
                  refine ⟨110079754497258709414087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9393472383766076536668757 110079754497258709414087)
                  ·
                    rfl

theorem cell23_1929416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_1929416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929416 prefixEnd_1929416 := by exact prefixLift 1929416
  have htrace : WordTrace (prefixWord ++ tailWord_1929416) baseStart_1929416 baseEnd_1929416 := by
    simpa [prefixWord, tailWord_1929416, baseEnd_1929416] using wordTrace_append hprefix tailTrace_1929416
  have hstable : (prefixWord ++ tailWord_1929416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929416).length < 2 ^ (prefixWord ++ tailWord_1929416).sum := by decide
  have hdescent : baseEnd_1929416 < baseStart_1929416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929433 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 6]
def baseStart_1929433 : Nat := 118140960795 + 1929433 * 2 ^ 59
def prefixEnd_1929433 : Nat := 4983230072969 + 3 ^ 40 * 1929433 * 2
def baseEnd_1929433 : Nat := 110080724405161646468245

theorem tailTrace_1929433 : CollatzResearch.WordTrace tailWord_1929433 prefixEnd_1929433 110080724405161646468245 := by
  unfold tailWord_1929433
  simp only [CollatzResearch.WordTrace]
  refine ⟨70372202819001236767008953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914801879334157844672635 70372202819001236767008953)
  ·
    refine ⟨52779152114250927575256715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70372202819001236767008953 52779152114250927575256715)
    ·
      refine ⟨79168728171376391362885073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52779152114250927575256715 79168728171376391362885073)
      ·
        refine ⟨59376546128532293522163805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79168728171376391362885073 59376546128532293522163805)
        ·
          refine ⟨22266204798199610070811427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59376546128532293522163805 22266204798199610070811427)
          ·
            refine ⟨33399307197299415106217141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22266204798199610070811427 33399307197299415106217141)
            ·
              refine ⟨3131185049746820166207857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33399307197299415106217141 3131185049746820166207857)
              ·
                refine ⟨2348388787310115124655893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131185049746820166207857 2348388787310115124655893)
                ·
                  refine ⟨110080724405161646468245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2348388787310115124655893 110080724405161646468245)
                  ·
                    rfl

theorem cell23_1929433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_1929433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929433 prefixEnd_1929433 := by exact prefixLift 1929433
  have htrace : WordTrace (prefixWord ++ tailWord_1929433) baseStart_1929433 baseEnd_1929433 := by
    simpa [prefixWord, tailWord_1929433, baseEnd_1929433] using wordTrace_append hprefix tailTrace_1929433
  have hstable : (prefixWord ++ tailWord_1929433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929433).length < 2 ^ (prefixWord ++ tailWord_1929433).sum := by decide
  have hdescent : baseEnd_1929433 < baseStart_1929433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929437 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1929437 : Nat := 118140960795 + 1929437 * 2 ^ 59
def prefixEnd_1929437 : Nat := 4983230072969 + 3 ^ 40 * 1929437 * 2
def baseEnd_1929437 : Nat := 330242857856357600854729

theorem tailTrace_1929437 : CollatzResearch.WordTrace tailWord_1929437 prefixEnd_1929437 330242857856357600854729 := by
  unfold tailWord_1929437
  simp only [CollatzResearch.WordTrace]
  refine ⟨70372348710986745450154565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914899140657830300103043 70372348710986745450154565)
  ·
    refine ⟨13194815383310014771903981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70372348710986745450154565 13194815383310014771903981)
    ·
      refine ⟨4948055768741255539463993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13194815383310014771903981 4948055768741255539463993)
      ·
        refine ⟨3711041826555941654597995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4948055768741255539463993 3711041826555941654597995)
        ·
          refine ⟨5566562739833912481896993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711041826555941654597995 5566562739833912481896993)
          ·
            refine ⟨4174922054875434361422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566562739833912481896993 4174922054875434361422745)
            ·
              refine ⟨3131191541156575771067059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174922054875434361422745 3131191541156575771067059)
              ·
                refine ⟨4696787311734863656600589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131191541156575771067059 4696787311734863656600589)
                ·
                  refine ⟨1761295241900573871225221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4696787311734863656600589 1761295241900573871225221)
                  ·
                    refine ⟨330242857856357600854729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1761295241900573871225221 330242857856357600854729)
                    ·
                      rfl

theorem cell23_1929437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1929437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929437 prefixEnd_1929437 := by exact prefixLift 1929437
  have htrace : WordTrace (prefixWord ++ tailWord_1929437) baseStart_1929437 baseEnd_1929437 := by
    simpa [prefixWord, tailWord_1929437, baseEnd_1929437] using wordTrace_append hprefix tailTrace_1929437
  have hstable : (prefixWord ++ tailWord_1929437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929437).length < 2 ^ (prefixWord ++ tailWord_1929437).sum := by decide
  have hdescent : baseEnd_1929437 < baseStart_1929437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929450 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_1929450 : Nat := 118140960795 + 1929450 * 2 ^ 59
def prefixEnd_1929450 : Nat := 4983230072969 + 3 ^ 40 * 1929450 * 2
def baseEnd_1929450 : Nat := 110081694313064583522403

theorem tailTrace_1929450 : CollatzResearch.WordTrace tailWord_1929450 prefixEnd_1929450 110081694313064583522403 := by
  unfold tailWord_1929450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593205714984912167594451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46915215239959765780251869 17593205714984912167594451)
  ·
    refine ⟨26389808572477368251391677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17593205714984912167594451 26389808572477368251391677)
    ·
      refine ⟨9896178214679013094271879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26389808572477368251391677 9896178214679013094271879)
      ·
        refine ⟨14844267322018519641407819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896178214679013094271879 14844267322018519641407819)
        ·
          refine ⟨22266400983027779462111729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14844267322018519641407819 22266400983027779462111729)
          ·
            refine ⟨16699800737270834596583797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22266400983027779462111729 16699800737270834596583797)
            ·
              refine ⟨1565606319119140743429731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16699800737270834596583797 1565606319119140743429731)
              ·
                refine ⟨2348409478678711115144597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565606319119140743429731 2348409478678711115144597)
                ·
                  refine ⟨110081694313064583522403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2348409478678711115144597 110081694313064583522403)
                  ·
                    rfl

theorem cell23_1929450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_1929450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929450 prefixEnd_1929450 := by exact prefixLift 1929450
  have htrace : WordTrace (prefixWord ++ tailWord_1929450) baseStart_1929450 baseEnd_1929450 := by
    simpa [prefixWord, tailWord_1929450, baseEnd_1929450] using wordTrace_append hprefix tailTrace_1929450
  have hstable : (prefixWord ++ tailWord_1929450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929450).length < 2 ^ (prefixWord ++ tailWord_1929450).sum := by decide
  have hdescent : baseEnd_1929450 < baseStart_1929450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929456 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1929456 : Nat := 118140960795 + 1929456 * 2 ^ 59
def prefixEnd_1929456 : Nat := 4983230072969 + 3 ^ 40 * 1929456 * 2
def baseEnd_1929456 : Nat := 990738329701508228226599

theorem tailTrace_1929456 : CollatzResearch.WordTrace tailWord_1929456 prefixEnd_1929456 990738329701508228226599 := by
  unfold tailWord_1929456
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186520848958955847548111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46915361131945274463397481 35186520848958955847548111)
  ·
    refine ⟨52779781273438433771322167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35186520848958955847548111 52779781273438433771322167)
    ·
      refine ⟨79169671910157650656983251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52779781273438433771322167 79169671910157650656983251)
      ·
        refine ⟨118754507865236475985474877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79169671910157650656983251 118754507865236475985474877)
        ·
          refine ⟨44532940449463678494553079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118754507865236475985474877 44532940449463678494553079)
          ·
            refine ⟨66799410674195517741829619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44532940449463678494553079 66799410674195517741829619)
            ·
              refine ⟨100199116011293276612744429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66799410674195517741829619 100199116011293276612744429)
              ·
                refine ⟨37574668504234978729779161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100199116011293276612744429 37574668504234978729779161)
                ·
                  refine ⟨28181001378176234047334371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37574668504234978729779161 28181001378176234047334371)
                  ·
                    refine ⟨42271502067264351071001557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28181001378176234047334371 42271502067264351071001557)
                    ·
                      refine ⟨990738329701508228226599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42271502067264351071001557 990738329701508228226599)
                      ·
                        rfl

theorem cell23_1929456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1929456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929456 prefixEnd_1929456 := by exact prefixLift 1929456
  have htrace : WordTrace (prefixWord ++ tailWord_1929456) baseStart_1929456 baseEnd_1929456 := by
    simpa [prefixWord, tailWord_1929456, baseEnd_1929456] using wordTrace_append hprefix tailTrace_1929456
  have hstable : (prefixWord ++ tailWord_1929456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929456).length < 2 ^ (prefixWord ++ tailWord_1929456).sum := by decide
  have hdescent : baseEnd_1929456 < baseStart_1929456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929477 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_1929477 : Nat := 118140960795 + 1929477 * 2 ^ 59
def prefixEnd_1929477 : Nat := 4983230072969 + 3 ^ 40 * 1929477 * 2
def baseEnd_1929477 : Nat := 990749112795252646064003

theorem tailTrace_1929477 : CollatzResearch.WordTrace tailWord_1929477 prefixEnd_1929477 990749112795252646064003 := by
  unfold tailWord_1929477
  simp only [CollatzResearch.WordTrace]
  refine ⟨70373807630841832281610685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46915871753894554854407123 70373807630841832281610685)
  ·
    refine ⟨26390177861565687105604007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70373807630841832281610685 26390177861565687105604007)
    ·
      refine ⟨39585266792348530658406011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390177861565687105604007 39585266792348530658406011)
      ·
        refine ⟨59377900188522795987609017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39585266792348530658406011 59377900188522795987609017)
        ·
          refine ⟨44533425141392096990706763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59377900188522795987609017 44533425141392096990706763)
          ·
            refine ⟨66800137712088145486060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44533425141392096990706763 66800137712088145486060145)
            ·
              refine ⟨50100103284066109114545109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66800137712088145486060145 50100103284066109114545109)
              ·
                refine ⟨1174221170720299432372151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50100103284066109114545109 1174221170720299432372151)
                ·
                  refine ⟨1761331756080449148558227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174221170720299432372151 1761331756080449148558227)
                  ·
                    refine ⟨2641997634120673722837341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761331756080449148558227 2641997634120673722837341)
                    ·
                      refine ⟨990749112795252646064003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2641997634120673722837341 990749112795252646064003)
                      ·
                        rfl

theorem cell23_1929477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_1929477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929477 prefixEnd_1929477 := by exact prefixLift 1929477
  have htrace : WordTrace (prefixWord ++ tailWord_1929477) baseStart_1929477 baseEnd_1929477 := by
    simpa [prefixWord, tailWord_1929477, baseEnd_1929477] using wordTrace_append hprefix tailTrace_1929477
  have hstable : (prefixWord ++ tailWord_1929477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929477).length < 2 ^ (prefixWord ++ tailWord_1929477).sum := by decide
  have hdescent : baseEnd_1929477 < baseStart_1929477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929480 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1929480 : Nat := 118140960795 + 1929480 * 2 ^ 59
def prefixEnd_1929480 : Nat := 4983230072969 + 3 ^ 40 * 1929480 * 2
def baseEnd_1929480 : Nat := 330250217745738711442163

theorem tailTrace_1929480 : CollatzResearch.WordTrace tailWord_1929480 prefixEnd_1929480 330250217745738711442163 := by
  unfold tailWord_1929480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186958524915481896984947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46915944699887309195979929 35186958524915481896984947)
  ·
    refine ⟨52780437787373222845477421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35186958524915481896984947 52780437787373222845477421)
    ·
      refine ⟨19792664170264958567054033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52780437787373222845477421 19792664170264958567054033)
      ·
        refine ⟨14844498127698718925290525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19792664170264958567054033 14844498127698718925290525)
        ·
          refine ⟨5566686797887019596983947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14844498127698718925290525 5566686797887019596983947)
          ·
            refine ⟨8350030196830529395475921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566686797887019596983947 8350030196830529395475921)
            ·
              refine ⟨6262522647622897046606941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350030196830529395475921 6262522647622897046606941)
              ·
                refine ⟨2348445992858586392477603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6262522647622897046606941 2348445992858586392477603)
                ·
                  refine ⟨3522668989287879588716405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348445992858586392477603 3522668989287879588716405)
                  ·
                    refine ⟨330250217745738711442163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3522668989287879588716405 330250217745738711442163)
                    ·
                      rfl

theorem cell23_1929480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1929480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929480 prefixEnd_1929480 := by exact prefixLift 1929480
  have htrace : WordTrace (prefixWord ++ tailWord_1929480) baseStart_1929480 baseEnd_1929480 := by
    simpa [prefixWord, tailWord_1929480, baseEnd_1929480] using wordTrace_append hprefix tailTrace_1929480
  have hstable : (prefixWord ++ tailWord_1929480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929480).length < 2 ^ (prefixWord ++ tailWord_1929480).sum := by decide
  have hdescent : baseEnd_1929480 < baseStart_1929480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929514 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1929514 : Nat := 118140960795 + 1929514 * 2 ^ 59
def prefixEnd_1929514 : Nat := 4983230072969 + 3 ^ 40 * 1929514 * 2
def baseEnd_1929514 : Nat := 330256037193156333767111

theorem tailTrace_1929514 : CollatzResearch.WordTrace tailWord_1929514 prefixEnd_1929514 330256037193156333767111 := by
  unfold tailWord_1929514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593789282926946900176899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46916771421138525067138397 17593789282926946900176899)
  ·
    refine ⟨26390683924390420350265349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17593789282926946900176899 26390683924390420350265349)
    ·
      refine ⟨4948253235823203815674753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26390683924390420350265349 4948253235823203815674753)
      ·
        refine ⟨3711189926867402861756065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4948253235823203815674753 3711189926867402861756065)
        ·
          refine ⟨2783392445150552146317049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711189926867402861756065 2783392445150552146317049)
          ·
            refine ⟨2087544333862914109737787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783392445150552146317049 2087544333862914109737787)
            ·
              refine ⟨3131316500794371164606681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087544333862914109737787 3131316500794371164606681)
              ·
                refine ⟨2348487375595778373455011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131316500794371164606681 2348487375595778373455011)
                ·
                  refine ⟨3522731063393667560182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348487375595778373455011 3522731063393667560182517)
                  ·
                    refine ⟨330256037193156333767111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3522731063393667560182517 330256037193156333767111)
                    ·
                      rfl

theorem cell23_1929514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1929514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929514 prefixEnd_1929514 := by exact prefixLift 1929514
  have htrace : WordTrace (prefixWord ++ tailWord_1929514) baseStart_1929514 baseEnd_1929514 := by
    simpa [prefixWord, tailWord_1929514, baseEnd_1929514] using wordTrace_append hprefix tailTrace_1929514
  have hstable : (prefixWord ++ tailWord_1929514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929514).length < 2 ^ (prefixWord ++ tailWord_1929514).sum := by decide
  have hdescent : baseEnd_1929514 < baseStart_1929514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929520 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_1929520 : Nat := 118140960795 + 1929520 * 2 ^ 59
def prefixEnd_1929520 : Nat := 4983230072969 + 3 ^ 40 * 1929520 * 2
def baseEnd_1929520 : Nat := 990771192463395977826305

theorem tailTrace_1929520 : CollatzResearch.WordTrace tailWord_1929520 prefixEnd_1929520 990771192463395977826305 := by
  unfold tailWord_1929520
  simp only [CollatzResearch.WordTrace]
  refine ⟨35187687984843025312713007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46916917313124033750284009 35187687984843025312713007)
  ·
    refine ⟨52781531977264537969069511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35187687984843025312713007 52781531977264537969069511)
    ·
      refine ⟨79172297965896806953604267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52781531977264537969069511 79172297965896806953604267)
      ·
        refine ⟨118758446948845210430406401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79172297965896806953604267 118758446948845210430406401)
        ·
          refine ⟨89068835211633907822804801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118758446948845210430406401 89068835211633907822804801)
          ·
            refine ⟨66801626408725430867103601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89068835211633907822804801 66801626408725430867103601)
            ·
              refine ⟨50101219806544073150327701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66801626408725430867103601 50101219806544073150327701)
              ·
                refine ⟨2348494678431753428921611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50101219806544073150327701 2348494678431753428921611)
                ·
                  refine ⟨3522742017647630143382417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348494678431753428921611 3522742017647630143382417)
                  ·
                    refine ⟨2642056513235722607536813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3522742017647630143382417 2642056513235722607536813)
                    ·
                      refine ⟨990771192463395977826305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642056513235722607536813 990771192463395977826305)
                      ·
                        rfl

theorem cell23_1929520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_1929520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929520 prefixEnd_1929520 := by exact prefixLift 1929520
  have htrace : WordTrace (prefixWord ++ tailWord_1929520) baseStart_1929520 baseEnd_1929520 := by
    simpa [prefixWord, tailWord_1929520, baseEnd_1929520] using wordTrace_append hprefix tailTrace_1929520
  have hstable : (prefixWord ++ tailWord_1929520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929520).length < 2 ^ (prefixWord ++ tailWord_1929520).sum := by decide
  have hdescent : baseEnd_1929520 < baseStart_1929520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929530 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1929530 : Nat := 118140960795 + 1929530 * 2 ^ 59
def prefixEnd_1929530 : Nat := 4983230072969 + 3 ^ 40 * 1929530 * 2
def baseEnd_1929530 : Nat := 990776327269940938701259

theorem tailTrace_1929530 : CollatzResearch.WordTrace tailWord_1929530 prefixEnd_1929530 990776327269940938701259 := by
  unfold tailWord_1929530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593935174912455583322511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46917160466433214888860029 17593935174912455583322511)
  ·
    refine ⟨26390902762368683374983767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17593935174912455583322511 26390902762368683374983767)
    ·
      refine ⟨39586354143553025062475651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390902762368683374983767 39586354143553025062475651)
      ·
        refine ⟨59379531215329537593713477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39586354143553025062475651 59379531215329537593713477)
        ·
          refine ⟨11133662102874288298821277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59379531215329537593713477 11133662102874288298821277)
          ·
            refine ⟨4175123288577858112057979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11133662102874288298821277 4175123288577858112057979)
            ·
              refine ⟨6262684932866787168086969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175123288577858112057979 6262684932866787168086969)
              ·
                refine ⟨4697013699650090376065227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262684932866787168086969 4697013699650090376065227)
                ·
                  refine ⟨7045520549475135564097841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697013699650090376065227 7045520549475135564097841)
                  ·
                    refine ⟨5284140412106351673073381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7045520549475135564097841 5284140412106351673073381)
                    ·
                      refine ⟨990776327269940938701259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5284140412106351673073381 990776327269940938701259)
                      ·
                        rfl

theorem cell23_1929530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1929530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929530 prefixEnd_1929530 := by exact prefixLift 1929530
  have htrace : WordTrace (prefixWord ++ tailWord_1929530) baseStart_1929530 baseEnd_1929530 := by
    simpa [prefixWord, tailWord_1929530, baseEnd_1929530] using wordTrace_append hprefix tailTrace_1929530
  have hstable : (prefixWord ++ tailWord_1929530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929530).length < 2 ^ (prefixWord ++ tailWord_1929530).sum := by decide
  have hdescent : baseEnd_1929530 < baseStart_1929530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929534 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1929534 : Nat := 118140960795 + 1929534 * 2 ^ 59
def prefixEnd_1929534 : Nat := 4983230072969 + 3 ^ 40 * 1929534 * 2
def baseEnd_1929534 : Nat := 990778381192558923051241

theorem tailTrace_1929534 : CollatzResearch.WordTrace tailWord_1929534 prefixEnd_1929534 990778381192558923051241 := by
  unfold tailWord_1929534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796985823954416377054457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46917257727756887344290437 8796985823954416377054457)
  ·
    refine ⟨6597739367965812282790843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8796985823954416377054457 6597739367965812282790843)
    ·
      refine ⟨9896609051948718424186265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597739367965812282790843 9896609051948718424186265)
      ·
        refine ⟨7422456788961538818139699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9896609051948718424186265 7422456788961538818139699)
        ·
          refine ⟨11133685183442308227209549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422456788961538818139699 11133685183442308227209549)
          ·
            refine ⟨4175131943790865585203581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11133685183442308227209549 4175131943790865585203581)
            ·
              refine ⟨1565674478921574594451343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4175131943790865585203581 1565674478921574594451343)
              ·
                refine ⟨2348511718382361891677015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565674478921574594451343 2348511718382361891677015)
                ·
                  refine ⟨3522767577573542837515523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348511718382361891677015 3522767577573542837515523)
                  ·
                    refine ⟨5284151366360314256273285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522767577573542837515523 5284151366360314256273285)
                    ·
                      refine ⟨990778381192558923051241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5284151366360314256273285 990778381192558923051241)
                      ·
                        rfl

theorem cell23_1929534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1929534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929534 prefixEnd_1929534 := by exact prefixLift 1929534
  have htrace : WordTrace (prefixWord ++ tailWord_1929534) baseStart_1929534 baseEnd_1929534 := by
    simpa [prefixWord, tailWord_1929534, baseEnd_1929534] using wordTrace_append hprefix tailTrace_1929534
  have hstable : (prefixWord ++ tailWord_1929534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929534).length < 2 ^ (prefixWord ++ tailWord_1929534).sum := by decide
  have hdescent : baseEnd_1929534 < baseStart_1929534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929540 : List Nat := [2, 3, 4, 1, 2, 11]
def baseStart_1929540 : Nat := 118140960795 + 1929540 * 2 ^ 59
def prefixEnd_1929540 : Nat := 4983230072969 + 3 ^ 40 * 1929540 * 2
def baseEnd_1929540 : Nat := 4077289967392946088791

theorem tailTrace_1929540 : CollatzResearch.WordTrace tailWord_1929540 prefixEnd_1929540 4077289967392946088791 := by
  unfold tailWord_1929540
  simp only [CollatzResearch.WordTrace]
  refine ⟨35188052714806797020577037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46917403619742396027436049 35188052714806797020577037)
  ·
    refine ⟨13195519768052548882716389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35188052714806797020577037 13195519768052548882716389)
    ·
      refine ⟨2474159956509852915509323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13195519768052548882716389 2474159956509852915509323)
      ·
        refine ⟨3711239934764779373263985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474159956509852915509323 3711239934764779373263985)
        ·
          refine ⟨2783429951073584529947989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711239934764779373263985 2783429951073584529947989)
          ·
            refine ⟨4077289967392946088791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2783429951073584529947989 4077289967392946088791)
            ·
              rfl

theorem cell23_1929540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 11].length) (baseStart_1929540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929540 prefixEnd_1929540 := by exact prefixLift 1929540
  have htrace : WordTrace (prefixWord ++ tailWord_1929540) baseStart_1929540 baseEnd_1929540 := by
    simpa [prefixWord, tailWord_1929540, baseEnd_1929540] using wordTrace_append hprefix tailTrace_1929540
  have hstable : (prefixWord ++ tailWord_1929540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929540).length < 2 ^ (prefixWord ++ tailWord_1929540).sum := by decide
  have hdescent : baseEnd_1929540 < baseStart_1929540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929553 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_1929553 : Nat := 118140960795 + 1929553 * 2 ^ 59
def prefixEnd_1929553 : Nat := 4983230072969 + 3 ^ 40 * 1929553 * 2
def baseEnd_1929553 : Nat := 330262712441664782904551

theorem tailTrace_1929553 : CollatzResearch.WordTrace tailWord_1929553 prefixEnd_1929553 330262712441664782904551 := by
  unfold tailWord_1929553
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376579578566497261377313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46917719719044331507584875 70376579578566497261377313)
  ·
    refine ⟨52782434683924872946032985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70376579578566497261377313 52782434683924872946032985)
    ·
      refine ⟨39586826012943654709524739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52782434683924872946032985 39586826012943654709524739)
      ·
        refine ⟨59380239019415482064287109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39586826012943654709524739 59380239019415482064287109)
        ·
          refine ⟨11133794816140402887053833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59380239019415482064287109 11133794816140402887053833)
          ·
            refine ⟨8350346112105302165290375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11133794816140402887053833 8350346112105302165290375)
            ·
              refine ⟨12525519168157953247935563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350346112105302165290375 12525519168157953247935563)
              ·
                refine ⟨18788278752236929871903345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525519168157953247935563 18788278752236929871903345)
                ·
                  refine ⟨14091209064177697403927509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18788278752236929871903345 14091209064177697403927509)
                  ·
                    refine ⟨330262712441664782904551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14091209064177697403927509 330262712441664782904551)
                    ·
                      rfl

theorem cell23_1929553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_1929553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929553 prefixEnd_1929553 := by exact prefixLift 1929553
  have htrace : WordTrace (prefixWord ++ tailWord_1929553) baseStart_1929553 baseEnd_1929553 := by
    simpa [prefixWord, tailWord_1929553, baseEnd_1929553] using wordTrace_append hprefix tailTrace_1929553
  have hstable : (prefixWord ++ tailWord_1929553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929553).length < 2 ^ (prefixWord ++ tailWord_1929553).sum := by decide
  have hdescent : baseEnd_1929553 < baseStart_1929553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929557 : List Nat := [1, 3, 2, 2, 5, 1, 1, 8]
def baseStart_1929557 : Nat := 118140960795 + 1929557 * 2 ^ 59
def prefixEnd_1929557 : Nat := 4983230072969 + 3 ^ 40 * 1929557 * 2
def baseEnd_1929557 : Nat := 36695933009170827150505

theorem tailTrace_1929557 : CollatzResearch.WordTrace tailWord_1929557 prefixEnd_1929557 36695933009170827150505 := by
  unfold tailWord_1929557
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376725470552005944522925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46917816980368003963015283 70376725470552005944522925)
  ·
    refine ⟨26391272051457002229196097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70376725470552005944522925 26391272051457002229196097)
    ·
      refine ⟨19793454038592751671897073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26391272051457002229196097 19793454038592751671897073)
      ·
        refine ⟨14845090528944563753922805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19793454038592751671897073 14845090528944563753922805)
        ·
          refine ⟨1391727237088552851930263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14845090528944563753922805 1391727237088552851930263)
          ·
            refine ⟨2087590855632829277895395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391727237088552851930263 2087590855632829277895395)
            ·
              refine ⟨3131386283449243916843093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087590855632829277895395 3131386283449243916843093)
              ·
                refine ⟨36695933009170827150505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3131386283449243916843093 36695933009170827150505)
                ·
                  rfl

theorem cell23_1929557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 8].length) (baseStart_1929557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929557 prefixEnd_1929557 := by exact prefixLift 1929557
  have htrace : WordTrace (prefixWord ++ tailWord_1929557) baseStart_1929557 baseEnd_1929557 := by
    simpa [prefixWord, tailWord_1929557, baseEnd_1929557] using wordTrace_append hprefix tailTrace_1929557
  have hstable : (prefixWord ++ tailWord_1929557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929557).length < 2 ^ (prefixWord ++ tailWord_1929557).sum := by decide
  have hdescent : baseEnd_1929557 < baseStart_1929557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929564 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1929564 : Nat := 118140960795 + 1929564 * 2 ^ 59
def prefixEnd_1929564 : Nat := 4983230072969 + 3 ^ 40 * 1929564 * 2
def baseEnd_1929564 : Nat := 990793785612193805676103

theorem tailTrace_1929564 : CollatzResearch.WordTrace tailWord_1929564 prefixEnd_1929564 990793785612193805676103 := by
  unfold tailWord_1929564
  simp only [CollatzResearch.WordTrace]
  refine ⟨35188490390763323070013873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46917987187684430760018497 35188490390763323070013873)
  ·
    refine ⟨26391367793072492302510405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35188490390763323070013873 26391367793072492302510405)
    ·
      refine ⟨4948381461201092306720701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26391367793072492302510405 4948381461201092306720701)
      ·
        refine ⟨1855643047950409615020263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4948381461201092306720701 1855643047950409615020263)
        ·
          refine ⟨2783464571925614422530395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855643047950409615020263 2783464571925614422530395)
          ·
            refine ⟨4175196857888421633795593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783464571925614422530395 4175196857888421633795593)
            ·
              refine ⟨3131397643416316225346695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175196857888421633795593 3131397643416316225346695)
              ·
                refine ⟨4697096465124474338020043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131397643416316225346695 4697096465124474338020043)
                ·
                  refine ⟨7045644697686711507030065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697096465124474338020043 7045644697686711507030065)
                  ·
                    refine ⟨5284233523265033630272549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7045644697686711507030065 5284233523265033630272549)
                    ·
                      refine ⟨990793785612193805676103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5284233523265033630272549 990793785612193805676103)
                      ·
                        rfl

theorem cell23_1929564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1929564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929564 prefixEnd_1929564 := by exact prefixLift 1929564
  have htrace : WordTrace (prefixWord ++ tailWord_1929564) baseStart_1929564 baseEnd_1929564 := by
    simpa [prefixWord, tailWord_1929564, baseEnd_1929564] using wordTrace_append hprefix tailTrace_1929564
  have hstable : (prefixWord ++ tailWord_1929564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929564).length < 2 ^ (prefixWord ++ tailWord_1929564).sum := by decide
  have hdescent : baseEnd_1929564 < baseStart_1929564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929567 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_1929567 : Nat := 118140960795 + 1929567 * 2 ^ 59
def prefixEnd_1929567 : Nat := 4983230072969 + 3 ^ 40 * 1929567 * 2
def baseEnd_1929567 : Nat := 990795326054157293938589

theorem tailTrace_1929567 : CollatzResearch.WordTrace tailWord_1929567 prefixEnd_1929567 990795326054157293938589 := by
  unfold tailWord_1929567
  simp only [CollatzResearch.WordTrace]
  refine ⟨70377090200515777652386955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46918060133677185101591303 70377090200515777652386955)
  ·
    refine ⟨105565635300773666478580433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70377090200515777652386955 105565635300773666478580433)
    ·
      refine ⟨79174226475580249858935325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105565635300773666478580433 79174226475580249858935325)
      ·
        refine ⟨29690334928342593697100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79174226475580249858935325 29690334928342593697100747)
        ·
          refine ⟨44535502392513890545651121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29690334928342593697100747 44535502392513890545651121)
          ·
            refine ⟨33401626794385417909238341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44535502392513890545651121 33401626794385417909238341)
            ·
              refine ⟨6262805023947265857982189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33401626794385417909238341 6262805023947265857982189)
              ·
                refine ⟨2348551883980224696743321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6262805023947265857982189 2348551883980224696743321)
                ·
                  refine ⟨1761413912985168522557491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348551883980224696743321 1761413912985168522557491)
                  ·
                    refine ⟨2642120869477752783836237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761413912985168522557491 2642120869477752783836237)
                    ·
                      refine ⟨990795326054157293938589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642120869477752783836237 990795326054157293938589)
                      ·
                        rfl

theorem cell23_1929567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_1929567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929567 prefixEnd_1929567 := by exact prefixLift 1929567
  have htrace : WordTrace (prefixWord ++ tailWord_1929567) baseStart_1929567 baseEnd_1929567 := by
    simpa [prefixWord, tailWord_1929567, baseEnd_1929567] using wordTrace_append hprefix tailTrace_1929567
  have hstable : (prefixWord ++ tailWord_1929567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929567).length < 2 ^ (prefixWord ++ tailWord_1929567).sum := by decide
  have hdescent : baseEnd_1929567 < baseStart_1929567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929577 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 1, 3, 2]
def baseStart_1929577 : Nat := 118140960795 + 1929577 * 2 ^ 59
def prefixEnd_1929577 : Nat := 4983230072969 + 3 ^ 40 * 1929577 * 2
def baseEnd_1929577 : Nat := 990800460860702254813543

theorem tailTrace_1929577 : CollatzResearch.WordTrace tailWord_1929577 prefixEnd_1929577 990800460860702254813543 := by
  unfold tailWord_1929577
  simp only [CollatzResearch.WordTrace]
  refine ⟨70377454930479549360250985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46918303286986366240167323 70377454930479549360250985)
  ·
    refine ⟨52783091197859662020188239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70377454930479549360250985 52783091197859662020188239)
    ·
      refine ⟨79174636796789493030282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52783091197859662020188239 79174636796789493030282359)
      ·
        refine ⟨118761955195184239545423539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79174636796789493030282359 118761955195184239545423539)
        ·
          refine ⟨178142932792776359318135309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118761955195184239545423539 178142932792776359318135309)
          ·
            refine ⟨66803599797291134744300741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178142932792776359318135309 66803599797291134744300741)
            ·
              refine ⟨12525674961992087764556389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66803599797291134744300741 12525674961992087764556389)
              ·
                refine ⟨2348564055373516455854323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12525674961992087764556389 2348564055373516455854323)
                ·
                  refine ⟨3522846083060274683781485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348564055373516455854323 3522846083060274683781485)
                  ·
                    refine ⟨1321067281147603006418057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522846083060274683781485 1321067281147603006418057)
                    ·
                      refine ⟨990800460860702254813543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321067281147603006418057 990800460860702254813543)
                      ·
                        rfl

theorem cell23_1929577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3, 2].length) (baseStart_1929577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929577 prefixEnd_1929577 := by exact prefixLift 1929577
  have htrace : WordTrace (prefixWord ++ tailWord_1929577) baseStart_1929577 baseEnd_1929577 := by
    simpa [prefixWord, tailWord_1929577, baseEnd_1929577] using wordTrace_append hprefix tailTrace_1929577
  have hstable : (prefixWord ++ tailWord_1929577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929577).length < 2 ^ (prefixWord ++ tailWord_1929577).sum := by decide
  have hdescent : baseEnd_1929577 < baseStart_1929577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929593 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1929593 : Nat := 118140960795 + 1929593 * 2 ^ 59
def prefixEnd_1929593 : Nat := 4983230072969 + 3 ^ 40 * 1929593 * 2
def baseEnd_1929593 : Nat := 990808676551174192213469

theorem tailTrace_1929593 : CollatzResearch.WordTrace tailWord_1929593 prefixEnd_1929593 990808676551174192213469 := by
  unfold tailWord_1929593
  simp only [CollatzResearch.WordTrace]
  refine ⟨70378038498421584092833433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46918692332281056061888955 70378038498421584092833433)
  ·
    refine ⟨52783528873816188069625075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70378038498421584092833433 52783528873816188069625075)
    ·
      refine ⟨79175293310724282104437613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52783528873816188069625075 79175293310724282104437613)
      ·
        refine ⟨29690734991521605789164105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79175293310724282104437613 29690734991521605789164105)
        ·
          refine ⟨22268051243641204341873079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29690734991521605789164105 22268051243641204341873079)
          ·
            refine ⟨33402076865461806512809619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22268051243641204341873079 33402076865461806512809619)
            ·
              refine ⟨50103115298192709769214429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33402076865461806512809619 50103115298192709769214429)
              ·
                refine ⟨18788668236822266163455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50103115298192709769214429 18788668236822266163455411)
                ·
                  refine ⟨28183002355233399245183117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18788668236822266163455411 28183002355233399245183117)
                  ·
                    refine ⟨10568625883212524716943669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28183002355233399245183117 10568625883212524716943669)
                    ·
                      refine ⟨990808676551174192213469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10568625883212524716943669 990808676551174192213469)
                      ·
                        rfl

theorem cell23_1929593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1929593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929593 prefixEnd_1929593 := by exact prefixLift 1929593
  have htrace : WordTrace (prefixWord ++ tailWord_1929593) baseStart_1929593 baseEnd_1929593 := by
    simpa [prefixWord, tailWord_1929593, baseEnd_1929593] using wordTrace_append hprefix tailTrace_1929593
  have hstable : (prefixWord ++ tailWord_1929593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929593).length < 2 ^ (prefixWord ++ tailWord_1929593).sum := by decide
  have hdescent : baseEnd_1929593 < baseStart_1929593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929601 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1929601 : Nat := 118140960795 + 1929601 * 2 ^ 59
def prefixEnd_1929601 : Nat := 4983230072969 + 3 ^ 40 * 1929601 * 2
def baseEnd_1929601 : Nat := 990812784396410160913433

theorem tailTrace_1929601 : CollatzResearch.WordTrace tailWord_1929601 prefixEnd_1929601 990812784396410160913433 := by
  unfold tailWord_1929601
  simp only [CollatzResearch.WordTrace]
  refine ⟨70378330282392601459124657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46918886854928400972749771 70378330282392601459124657)
  ·
    refine ⟨52783747711794451094343493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70378330282392601459124657 52783747711794451094343493)
    ·
      refine ⟨9896952695961459580189405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52783747711794451094343493 9896952695961459580189405)
      ·
        refine ⟨3711357260985547342571027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9896952695961459580189405 3711357260985547342571027)
        ·
          refine ⟨5567035891478321013856541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711357260985547342571027 5567035891478321013856541)
          ·
            refine ⟨2087638459304370380196203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5567035891478321013856541 2087638459304370380196203)
            ·
              refine ⟨3131457688956555570294305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087638459304370380196203 3131457688956555570294305)
              ·
                refine ⟨2348593266717416677720729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131457688956555570294305 2348593266717416677720729)
                ·
                  refine ⟨1761444950038062508290547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348593266717416677720729 1761444950038062508290547)
                  ·
                    refine ⟨2642167425057093762435821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761444950038062508290547 2642167425057093762435821)
                    ·
                      refine ⟨990812784396410160913433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642167425057093762435821 990812784396410160913433)
                      ·
                        rfl

theorem cell23_1929601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1929601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929601 prefixEnd_1929601 := by exact prefixLift 1929601
  have htrace : WordTrace (prefixWord ++ tailWord_1929601) baseStart_1929601 baseEnd_1929601 := by
    simpa [prefixWord, tailWord_1929601, baseEnd_1929601] using wordTrace_append hprefix tailTrace_1929601
  have hstable : (prefixWord ++ tailWord_1929601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929601).length < 2 ^ (prefixWord ++ tailWord_1929601).sum := by decide
  have hdescent : baseEnd_1929601 < baseStart_1929601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929624 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1929624 : Nat := 118140960795 + 1929624 * 2 ^ 59
def prefixEnd_1929624 : Nat := 4983230072969 + 3 ^ 40 * 1929624 * 2
def baseEnd_1929624 : Nat := 990824594451463570925827

theorem tailTrace_1929624 : CollatzResearch.WordTrace tailWord_1929624 prefixEnd_1929624 990824594451463570925827 := by
  unfold tailWord_1929624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35189584580654638193605963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46919446107539517591474617 35189584580654638193605963)
  ·
    refine ⟨52784376870981957290408945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35189584580654638193605963 52784376870981957290408945)
    ·
      refine ⟨39588282653236467967806709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52784376870981957290408945 39588282653236467967806709)
      ·
        refine ⟨3711401498740918871981879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39588282653236467967806709 3711401498740918871981879)
        ·
          refine ⟨5567102248111378307972819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711401498740918871981879 5567102248111378307972819)
          ·
            refine ⟨8350653372167067461959229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567102248111378307972819 8350653372167067461959229)
            ·
              refine ⟨3131495014562650298234711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8350653372167067461959229 3131495014562650298234711)
              ·
                refine ⟨4697242521843975447352067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131495014562650298234711 4697242521843975447352067)
                ·
                  refine ⟨7045863782765963171028101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697242521843975447352067 7045863782765963171028101)
                  ·
                    refine ⟨1321099459268618094567769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045863782765963171028101 1321099459268618094567769)
                    ·
                      refine ⟨990824594451463570925827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321099459268618094567769 990824594451463570925827)
                      ·
                        rfl

theorem cell23_1929624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1929624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929624 prefixEnd_1929624 := by exact prefixLift 1929624
  have htrace : WordTrace (prefixWord ++ tailWord_1929624) baseStart_1929624 baseEnd_1929624 := by
    simpa [prefixWord, tailWord_1929624, baseEnd_1929624] using wordTrace_append hprefix tailTrace_1929624
  have hstable : (prefixWord ++ tailWord_1929624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929624).length < 2 ^ (prefixWord ++ tailWord_1929624).sum := by decide
  have hdescent : baseEnd_1929624 < baseStart_1929624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1929663 : Nat := 118140960795 + 1929663 * 2 ^ 59
def prefixEnd_1929663 : Nat := 4983230072969 + 3 ^ 40 * 1929663 * 2
def baseEnd_1929663 : Nat := 990844620196988918338147

theorem tailTrace_1929663 : CollatzResearch.WordTrace tailWord_1929663 prefixEnd_1929663 990844620196988918338147 := by
  unfold tailWord_1929663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70380591608167986047881643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46920394405445324031921095 70380591608167986047881643)
  ·
    refine ⟨105570887412251979071822465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70380591608167986047881643 105570887412251979071822465)
    ·
      refine ⟨79178165559188984303866849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105570887412251979071822465 79178165559188984303866849)
      ·
        refine ⟨59383624169391738227900137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79178165559188984303866849 59383624169391738227900137)
        ·
          refine ⟨44537718127043803670925103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59383624169391738227900137 44537718127043803670925103)
          ·
            refine ⟨66806577190565705506387655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44537718127043803670925103 66806577190565705506387655)
            ·
              refine ⟨100209865785848558259581483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66806577190565705506387655 100209865785848558259581483)
              ·
                refine ⟨150314798678772837389372225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100209865785848558259581483 150314798678772837389372225)
                ·
                  refine ⟨112736099009079628042029169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150314798678772837389372225 112736099009079628042029169)
                  ·
                    refine ⟨84552074256809721031521877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112736099009079628042029169 84552074256809721031521877)
                    ·
                      refine ⟨990844620196988918338147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84552074256809721031521877 990844620196988918338147)
                      ·
                        rfl

theorem cell23_1929663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1929663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929663 prefixEnd_1929663 := by exact prefixLift 1929663
  have htrace : WordTrace (prefixWord ++ tailWord_1929663) baseStart_1929663 baseEnd_1929663 := by
    simpa [prefixWord, tailWord_1929663, baseEnd_1929663] using wordTrace_append hprefix tailTrace_1929663
  have hstable : (prefixWord ++ tailWord_1929663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929663).length < 2 ^ (prefixWord ++ tailWord_1929663).sum := by decide
  have hdescent : baseEnd_1929663 < baseStart_1929663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929683 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1929683 : Nat := 118140960795 + 1929683 * 2 ^ 59
def prefixEnd_1929683 : Nat := 4983230072969 + 3 ^ 40 * 1929683 * 2
def baseEnd_1929683 : Nat := 990854889810078840088055

theorem tailTrace_1929683 : CollatzResearch.WordTrace tailWord_1929683 prefixEnd_1929683 990854889810078840088055 := by
  unfold tailWord_1929683
  simp only [CollatzResearch.WordTrace]
  refine ⟨70381321068095529463609703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46920880712063686309073135 70381321068095529463609703)
  ·
    refine ⟨105571981602143294195414555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70381321068095529463609703 105571981602143294195414555)
    ·
      refine ⟨158357972403214941293121833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105571981602143294195414555 158357972403214941293121833)
      ·
        refine ⟨118768479302411205969841375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158357972403214941293121833 118768479302411205969841375)
        ·
          refine ⟨178152718953616808954762063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118768479302411205969841375 178152718953616808954762063)
          ·
            refine ⟨267229078430425213432143095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178152718953616808954762063 267229078430425213432143095)
            ·
              refine ⟨400843617645637820148214643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267229078430425213432143095 400843617645637820148214643)
              ·
                refine ⟨601265426468456730222321965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400843617645637820148214643 601265426468456730222321965)
                ·
                  refine ⟨225474534925671273833370737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601265426468456730222321965 225474534925671273833370737)
                  ·
                    refine ⟨169105901194253455375028053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225474534925671273833370737 169105901194253455375028053)
                    ·
                      refine ⟨990854889810078840088055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 169105901194253455375028053 990854889810078840088055)
                      ·
                        rfl

theorem cell23_1929683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1929683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929683 prefixEnd_1929683 := by exact prefixLift 1929683
  have htrace : WordTrace (prefixWord ++ tailWord_1929683) baseStart_1929683 baseEnd_1929683 := by
    simpa [prefixWord, tailWord_1929683, baseEnd_1929683] using wordTrace_append hprefix tailTrace_1929683
  have hstable : (prefixWord ++ tailWord_1929683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929683).length < 2 ^ (prefixWord ++ tailWord_1929683).sum := by decide
  have hdescent : baseEnd_1929683 < baseStart_1929683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929697 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1929697 : Nat := 118140960795 + 1929697 * 2 ^ 59
def prefixEnd_1929697 : Nat := 4983230072969 + 3 ^ 40 * 1929697 * 2
def baseEnd_1929697 : Nat := 990862078539241785312991

theorem tailTrace_1929697 : CollatzResearch.WordTrace tailWord_1929697 prefixEnd_1929697 990862078539241785312991 := by
  unfold tailWord_1929697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70381831690044809854619345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46921221126696539903079563 70381831690044809854619345)
  ·
    refine ⟨52786373767533607390964509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70381831690044809854619345 52786373767533607390964509)
    ·
      refine ⟨19794890162825102771611691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52786373767533607390964509 19794890162825102771611691)
      ·
        refine ⟨29692335244237654157417537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19794890162825102771611691 29692335244237654157417537)
        ·
          refine ⟨22269251433178240618063153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29692335244237654157417537 22269251433178240618063153)
          ·
            refine ⟨16701938574883680463547365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22269251433178240618063153 16701938574883680463547365)
            ·
              refine ⟨3131613482790690086915131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16701938574883680463547365 3131613482790690086915131)
              ·
                refine ⟨4697420224186035130372697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131613482790690086915131 4697420224186035130372697)
                ·
                  refine ⟨3523065168139526347779523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697420224186035130372697 3523065168139526347779523)
                  ·
                    refine ⟨5284597752209289521669285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523065168139526347779523 5284597752209289521669285)
                    ·
                      refine ⟨990862078539241785312991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5284597752209289521669285 990862078539241785312991)
                      ·
                        rfl

theorem cell23_1929697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1929697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929697 prefixEnd_1929697 := by exact prefixLift 1929697
  have htrace : WordTrace (prefixWord ++ tailWord_1929697) baseStart_1929697 baseEnd_1929697 := by
    simpa [prefixWord, tailWord_1929697, baseEnd_1929697] using wordTrace_append hprefix tailTrace_1929697
  have hstable : (prefixWord ++ tailWord_1929697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929697).length < 2 ^ (prefixWord ++ tailWord_1929697).sum := by decide
  have hdescent : baseEnd_1929697 < baseStart_1929697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929741 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1929741 : Nat := 118140960795 + 1929741 * 2 ^ 59
def prefixEnd_1929741 : Nat := 4983230072969 + 3 ^ 40 * 1929741 * 2
def baseEnd_1929741 : Nat := 330294890562679871054263

theorem tailTrace_1929741 : CollatzResearch.WordTrace tailWord_1929741 prefixEnd_1929741 330294890562679871054263 := by
  unfold tailWord_1929741
  simp only [CollatzResearch.WordTrace]
  refine ⟨70383436501885405369221077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46922291001256936912814051 70383436501885405369221077)
  ·
    refine ⟨1649611793012939188341119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70383436501885405369221077 1649611793012939188341119)
    ·
      refine ⟨2474417689519408782511679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649611793012939188341119 2474417689519408782511679)
      ·
        refine ⟨3711626534279113173767519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474417689519408782511679 3711626534279113173767519)
        ·
          refine ⟨5567439801418669760651279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711626534279113173767519 5567439801418669760651279)
          ·
            refine ⟨8351159702128004640976919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567439801418669760651279 8351159702128004640976919)
            ·
              refine ⟨12526739553192006961465379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351159702128004640976919 12526739553192006961465379)
              ·
                refine ⟨18790109329788010442198069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12526739553192006961465379 18790109329788010442198069)
                ·
                  refine ⟨1761572749667625978956069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18790109329788010442198069 1761572749667625978956069)
                  ·
                    refine ⟨330294890562679871054263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1761572749667625978956069 330294890562679871054263)
                    ·
                      rfl

theorem cell23_1929741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1929741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929741 prefixEnd_1929741 := by exact prefixLift 1929741
  have htrace : WordTrace (prefixWord ++ tailWord_1929741) baseStart_1929741 baseEnd_1929741 := by
    simpa [prefixWord, tailWord_1929741, baseEnd_1929741] using wordTrace_append hprefix tailTrace_1929741
  have hstable : (prefixWord ++ tailWord_1929741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929741).length < 2 ^ (prefixWord ++ tailWord_1929741).sum := by decide
  have hdescent : baseEnd_1929741 < baseStart_1929741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929781 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_1929781 : Nat := 118140960795 + 1929781 * 2 ^ 59
def prefixEnd_1929781 : Nat := 4983230072969 + 3 ^ 40 * 1929781 * 2
def baseEnd_1929781 : Nat := 990905210914219456662605

theorem tailTrace_1929781 : CollatzResearch.WordTrace tailWord_1929781 prefixEnd_1929781 990905210914219456662605 := by
  unfold tailWord_1929781
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384895421740492200677197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46923263614493661467118131 70384895421740492200677197)
  ·
    refine ⟨26394335783152684575253949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70384895421740492200677197 26394335783152684575253949)
    ·
      refine ⟨9897875918682256715720231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26394335783152684575253949 9897875918682256715720231)
      ·
        refine ⟨14846813878023385073580347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897875918682256715720231 14846813878023385073580347)
        ·
          refine ⟨22270220817035077610370521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846813878023385073580347 22270220817035077610370521)
          ·
            refine ⟨16702665612776308207777891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22270220817035077610370521 16702665612776308207777891)
            ·
              refine ⟨25053998419164462311666837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16702665612776308207777891 25053998419164462311666837)
              ·
                refine ⟨1174406175898334170859383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25053998419164462311666837 1174406175898334170859383)
                ·
                  refine ⟨1761609263847501256289075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174406175898334170859383 1761609263847501256289075)
                  ·
                    refine ⟨2642413895771251884433613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761609263847501256289075 2642413895771251884433613)
                    ·
                      refine ⟨990905210914219456662605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642413895771251884433613 990905210914219456662605)
                      ·
                        rfl

theorem cell23_1929781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_1929781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929781 prefixEnd_1929781 := by exact prefixLift 1929781
  have htrace : WordTrace (prefixWord ++ tailWord_1929781) baseStart_1929781 baseEnd_1929781 := by
    simpa [prefixWord, tailWord_1929781, baseEnd_1929781] using wordTrace_append hprefix tailTrace_1929781
  have hstable : (prefixWord ++ tailWord_1929781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929781).length < 2 ^ (prefixWord ++ tailWord_1929781).sum := by decide
  have hdescent : baseEnd_1929781 < baseStart_1929781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929797 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_1929797 : Nat := 118140960795 + 1929797 * 2 ^ 59
def prefixEnd_1929797 : Nat := 4983230072969 + 3 ^ 40 * 1929797 * 2
def baseEnd_1929797 : Nat := 330304475534897131354177

theorem tailTrace_1929797 : CollatzResearch.WordTrace tailWord_1929797 prefixEnd_1929797 330304475534897131354177 := by
  unfold tailWord_1929797
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385478989682526933259645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46923652659788351288839763 70385478989682526933259645)
  ·
    refine ⟨26394554621130947599972367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70385478989682526933259645 26394554621130947599972367)
    ·
      refine ⟨39591831931696421399958551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394554621130947599972367 39591831931696421399958551)
      ·
        refine ⟨59387747897544632099937827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39591831931696421399958551 59387747897544632099937827)
        ·
          refine ⟨89081621846316948149906741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59387747897544632099937827 89081621846316948149906741)
          ·
            refine ⟨8351402048092213889053757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89081621846316948149906741 8351402048092213889053757)
            ·
              refine ⟨3131775768034580208395159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8351402048092213889053757 3131775768034580208395159)
              ·
                refine ⟨4697663652051870312592739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131775768034580208395159 4697663652051870312592739)
                ·
                  refine ⟨7046495478077805468889109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697663652051870312592739 7046495478077805468889109)
                  ·
                    refine ⟨330304475534897131354177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7046495478077805468889109 330304475534897131354177)
                    ·
                      rfl

theorem cell23_1929797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_1929797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929797 prefixEnd_1929797 := by exact prefixLift 1929797
  have htrace : WordTrace (prefixWord ++ tailWord_1929797) baseStart_1929797 baseEnd_1929797 := by
    simpa [prefixWord, tailWord_1929797, baseEnd_1929797] using wordTrace_append hprefix tailTrace_1929797
  have hstable : (prefixWord ++ tailWord_1929797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929797).length < 2 ^ (prefixWord ++ tailWord_1929797).sum := by decide
  have hdescent : baseEnd_1929797 < baseStart_1929797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929798 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1929798 : Nat := 118140960795 + 1929798 * 2 ^ 59
def prefixEnd_1929798 : Nat := 4983230072969 + 3 ^ 40 * 1929798 * 2
def baseEnd_1929798 : Nat := 990913940085345890150027

theorem tailTrace_1929798 : CollatzResearch.WordTrace tailWord_1929798 prefixEnd_1929798 990913940085345890150027 := by
  unfold tailWord_1929798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199547358208715753251439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46923676975119269402697365 2199547358208715753251439)
  ·
    refine ⟨3299321037313073629877159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199547358208715753251439 3299321037313073629877159)
    ·
      refine ⟨4948981555969610444815739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299321037313073629877159 4948981555969610444815739)
      ·
        refine ⟨7423472333954415667223609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948981555969610444815739 7423472333954415667223609)
        ·
          refine ⟨5567604250465811750417707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7423472333954415667223609 5567604250465811750417707)
          ·
            refine ⟨8351406375698717625626561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567604250465811750417707 8351406375698717625626561)
            ·
              refine ⟨6263554781774038219219921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351406375698717625626561 6263554781774038219219921)
              ·
                refine ⟨4697666086330528664414941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263554781774038219219921 4697666086330528664414941)
                ·
                  refine ⟨1761624782373948249155603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697666086330528664414941 1761624782373948249155603)
                  ·
                    refine ⟨2642437173560922373733405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761624782373948249155603 2642437173560922373733405)
                    ·
                      refine ⟨990913940085345890150027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642437173560922373733405 990913940085345890150027)
                      ·
                        rfl

theorem cell23_1929798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1929798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929798 prefixEnd_1929798 := by exact prefixLift 1929798
  have htrace : WordTrace (prefixWord ++ tailWord_1929798) baseStart_1929798 baseEnd_1929798 := by
    simpa [prefixWord, tailWord_1929798, baseEnd_1929798] using wordTrace_append hprefix tailTrace_1929798
  have hstable : (prefixWord ++ tailWord_1929798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929798).length < 2 ^ (prefixWord ++ tailWord_1929798).sum := by decide
  have hdescent : baseEnd_1929798 < baseStart_1929798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929804 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1929804 : Nat := 118140960795 + 1929804 * 2 ^ 59
def prefixEnd_1929804 : Nat := 4983230072969 + 3 ^ 40 * 1929804 * 2
def baseEnd_1929804 : Nat := 990917020969272866674999

theorem tailTrace_1929804 : CollatzResearch.WordTrace tailWord_1929804 prefixEnd_1929804 990917020969272866674999 := by
  unfold tailWord_1929804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35192867150328583564382233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46923822867104778085842977 35192867150328583564382233)
  ·
    refine ⟨26394650362746437673286675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35192867150328583564382233 26394650362746437673286675)
    ·
      refine ⟨39591975544119656509930013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394650362746437673286675 39591975544119656509930013)
      ·
        refine ⟨14846990829044871191223755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39591975544119656509930013 14846990829044871191223755)
        ·
          refine ⟨22270486243567306786835633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846990829044871191223755 22270486243567306786835633)
          ·
            refine ⟨16702864682675480090126725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22270486243567306786835633 16702864682675480090126725)
            ·
              refine ⟨3131787128001652516898761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16702864682675480090126725 3131787128001652516898761)
              ·
                refine ⟨2348840346001239387674071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131787128001652516898761 2348840346001239387674071)
                ·
                  refine ⟨3523260519001859081511107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348840346001239387674071 3523260519001859081511107)
                  ·
                    refine ⟨5284890778502788622266661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523260519001859081511107 5284890778502788622266661)
                    ·
                      refine ⟨990917020969272866674999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5284890778502788622266661 990917020969272866674999)
                      ·
                        rfl

theorem cell23_1929804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1929804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929804 prefixEnd_1929804 := by exact prefixLift 1929804
  have htrace : WordTrace (prefixWord ++ tailWord_1929804) baseStart_1929804 baseEnd_1929804 := by
    simpa [prefixWord, tailWord_1929804, baseEnd_1929804] using wordTrace_append hprefix tailTrace_1929804
  have hstable : (prefixWord ++ tailWord_1929804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929804).length < 2 ^ (prefixWord ++ tailWord_1929804).sum := by decide
  have hdescent : baseEnd_1929804 < baseStart_1929804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929807 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_1929807 : Nat := 118140960795 + 1929807 * 2 ^ 59
def prefixEnd_1929807 : Nat := 4983230072969 + 3 ^ 40 * 1929807 * 2
def baseEnd_1929807 : Nat := 990918561411236354937485

theorem tailTrace_1929807 : CollatzResearch.WordTrace tailWord_1929807 prefixEnd_1929807 990918561411236354937485 := by
  unfold tailWord_1929807
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385843719646298641123675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46923895813097532427415783 70385843719646298641123675)
  ·
    refine ⟨105578765579469447961685513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70385843719646298641123675 105578765579469447961685513)
    ·
      refine ⟨79184074184602085971264135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105578765579469447961685513 79184074184602085971264135)
      ·
        refine ⟨118776111276903128956896203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79184074184602085971264135 118776111276903128956896203)
        ·
          refine ⟨178164166915354693435344305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118776111276903128956896203 178164166915354693435344305)
          ·
            refine ⟨133623125186516020076508229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178164166915354693435344305 133623125186516020076508229)
            ·
              refine ⟨25054335972471753764345293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133623125186516020076508229 25054335972471753764345293)
              ·
                refine ⟨9395375989676907661629485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25054335972471753764345293 9395375989676907661629485)
                ·
                  refine ⟨3523265996128840373111057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395375989676907661629485 3523265996128840373111057)
                  ·
                    refine ⟨2642449497096630279833293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523265996128840373111057 2642449497096630279833293)
                    ·
                      refine ⟨990918561411236354937485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642449497096630279833293 990918561411236354937485)
                      ·
                        rfl

theorem cell23_1929807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_1929807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929807 prefixEnd_1929807 := by exact prefixLift 1929807
  have htrace : WordTrace (prefixWord ++ tailWord_1929807) baseStart_1929807 baseEnd_1929807 := by
    simpa [prefixWord, tailWord_1929807, baseEnd_1929807] using wordTrace_append hprefix tailTrace_1929807
  have hstable : (prefixWord ++ tailWord_1929807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929807).length < 2 ^ (prefixWord ++ tailWord_1929807).sum := by decide
  have hdescent : baseEnd_1929807 < baseStart_1929807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929824 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_1929824 : Nat := 118140960795 + 1929824 * 2 ^ 59
def prefixEnd_1929824 : Nat := 4983230072969 + 3 ^ 40 * 1929824 * 2
def baseEnd_1929824 : Nat := 990927290582362788424907

theorem tailTrace_1929824 : CollatzResearch.WordTrace tailWord_1929824 prefixEnd_1929824 990927290582362788424907 := by
  unfold tailWord_1929824
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193231880292355272246263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46924309173723140362995017 35193231880292355272246263)
  ·
    refine ⟨52789847820438532908369395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35193231880292355272246263 52789847820438532908369395)
    ·
      refine ⟨79184771730657799362554093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52789847820438532908369395 79184771730657799362554093)
      ·
        refine ⟨29694289398996674760957785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79184771730657799362554093 29694289398996674760957785)
        ·
          refine ⟨22270717049247506070718339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29694289398996674760957785 22270717049247506070718339)
          ·
            refine ⟨33406075573871259106077509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22270717049247506070718339 33406075573871259106077509)
            ·
              refine ⟨6263639170100861082389533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33406075573871259106077509 6263639170100861082389533)
              ·
                refine ⟨2348864688787822905896075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6263639170100861082389533 2348864688787822905896075)
                ·
                  refine ⟨3523297033181734358844113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348864688787822905896075 3523297033181734358844113)
                  ·
                    refine ⟨2642472774886300769133085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523297033181734358844113 2642472774886300769133085)
                    ·
                      refine ⟨990927290582362788424907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642472774886300769133085 990927290582362788424907)
                      ·
                        rfl

theorem cell23_1929824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_1929824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929824 prefixEnd_1929824 := by exact prefixLift 1929824
  have htrace : WordTrace (prefixWord ++ tailWord_1929824) baseStart_1929824 baseEnd_1929824 := by
    simpa [prefixWord, tailWord_1929824, baseEnd_1929824] using wordTrace_append hprefix tailTrace_1929824
  have hstable : (prefixWord ++ tailWord_1929824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929824).length < 2 ^ (prefixWord ++ tailWord_1929824).sum := by decide
  have hdescent : baseEnd_1929824 < baseStart_1929824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929838 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1929838 : Nat := 118140960795 + 1929838 * 2 ^ 59
def prefixEnd_1929838 : Nat := 4983230072969 + 3 ^ 40 * 1929838 * 2
def baseEnd_1929838 : Nat := 990934479311525733649843

theorem tailTrace_1929838 : CollatzResearch.WordTrace tailWord_1929838 prefixEnd_1929838 990934479311525733649843 := by
  unfold tailWord_1929838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798371797816748866937771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46924649588355993957001445 8798371797816748866937771)
  ·
    refine ⟨13197557696725123300406657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8798371797816748866937771 13197557696725123300406657)
    ·
      refine ⟨9898168272543842475304993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13197557696725123300406657 9898168272543842475304993)
      ·
        refine ⟨7423626204407881856478745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9898168272543842475304993 7423626204407881856478745)
        ·
          refine ⟨5567719653305911392359059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7423626204407881856478745 5567719653305911392359059)
          ·
            refine ⟨8351579479958867088538589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567719653305911392359059 8351579479958867088538589)
            ·
              refine ⟨3131842304984575158201971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8351579479958867088538589 3131842304984575158201971)
              ·
                refine ⟨4697763457476862737302957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131842304984575158201971 4697763457476862737302957)
                ·
                  refine ⟨1761661296553823526488609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697763457476862737302957 1761661296553823526488609)
                  ·
                    refine ⟨1321245972415367644866457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761661296553823526488609 1321245972415367644866457)
                    ·
                      refine ⟨990934479311525733649843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321245972415367644866457 990934479311525733649843)
                      ·
                        rfl

theorem cell23_1929838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1929838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929838 prefixEnd_1929838 := by exact prefixLift 1929838
  have htrace : WordTrace (prefixWord ++ tailWord_1929838) baseStart_1929838 baseEnd_1929838 := by
    simpa [prefixWord, tailWord_1929838, baseEnd_1929838] using wordTrace_append hprefix tailTrace_1929838
  have hstable : (prefixWord ++ tailWord_1929838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929838).length < 2 ^ (prefixWord ++ tailWord_1929838).sum := by decide
  have hdescent : baseEnd_1929838 < baseStart_1929838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929888 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1929888 : Nat := 118140960795 + 1929888 * 2 ^ 59
def prefixEnd_1929888 : Nat := 4983230072969 + 3 ^ 40 * 1929888 * 2
def baseEnd_1929888 : Nat := 990960153344250538024613

theorem tailTrace_1929888 : CollatzResearch.WordTrace tailWord_1929888 prefixEnd_1929888 990960153344250538024613 := by
  unfold tailWord_1929888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35194399016176424737411159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46925865354901899649881545 35194399016176424737411159)
  ·
    refine ⟨52791598524264637106116739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35194399016176424737411159 52791598524264637106116739)
    ·
      refine ⟨79187397786396955659175109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52791598524264637106116739 79187397786396955659175109)
      ·
        refine ⟨14847637084949429186095333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79187397786396955659175109 14847637084949429186095333)
        ·
          refine ⟨2783931953428017972392875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14847637084949429186095333 2783931953428017972392875)
          ·
            refine ⟨4175897930142026958589313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783931953428017972392875 4175897930142026958589313)
            ·
              refine ⟨3131923447606520218941985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4175897930142026958589313 3131923447606520218941985)
              ·
                refine ⟨2348942585704890164206489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131923447606520218941985 2348942585704890164206489)
                ·
                  refine ⟨1761706939278667623154867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348942585704890164206489 1761706939278667623154867)
                  ·
                    refine ⟨2642560408918001434732301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761706939278667623154867 2642560408918001434732301)
                    ·
                      refine ⟨990960153344250538024613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642560408918001434732301 990960153344250538024613)
                      ·
                        rfl

theorem cell23_1929888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1929888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929888 prefixEnd_1929888 := by exact prefixLift 1929888
  have htrace : WordTrace (prefixWord ++ tailWord_1929888) baseStart_1929888 baseEnd_1929888 := by
    simpa [prefixWord, tailWord_1929888, baseEnd_1929888] using wordTrace_append hprefix tailTrace_1929888
  have hstable : (prefixWord ++ tailWord_1929888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929888).length < 2 ^ (prefixWord ++ tailWord_1929888).sum := by decide
  have hdescent : baseEnd_1929888 < baseStart_1929888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929889 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1929889 : Nat := 118140960795 + 1929889 * 2 ^ 59
def prefixEnd_1929889 : Nat := 4983230072969 + 3 ^ 40 * 1929889 * 2
def baseEnd_1929889 : Nat := 990960666824905034112109

theorem tailTrace_1929889 : CollatzResearch.WordTrace tailWord_1929889 prefixEnd_1929889 990960666824905034112109 := by
  unfold tailWord_1929889
  simp only [CollatzResearch.WordTrace]
  refine ⟨70388834505349226645608721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46925889670232817763739147 70388834505349226645608721)
  ·
    refine ⟨52791625879011919984206541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70388834505349226645608721 52791625879011919984206541)
    ·
      refine ⟨19796859704629469994077453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52791625879011919984206541 19796859704629469994077453)
      ·
        refine ⟨7423822389236051247779045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19796859704629469994077453 7423822389236051247779045)
        ·
          refine ⟨1391966697981759608958571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7423822389236051247779045 1391966697981759608958571)
          ·
            refine ⟨2087950046972639413437857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391966697981759608958571 2087950046972639413437857)
            ·
              refine ⟨1565962535229479560078393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087950046972639413437857 1565962535229479560078393)
              ·
                refine ⟨1174471901422109670058795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565962535229479560078393 1174471901422109670058795)
                ·
                  refine ⟨1761707852133164505088193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174471901422109670058795 1761707852133164505088193)
                  ·
                    refine ⟨1321280889099873378816145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761707852133164505088193 1321280889099873378816145)
                    ·
                      refine ⟨990960666824905034112109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321280889099873378816145 990960666824905034112109)
                      ·
                        rfl

theorem cell23_1929889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1929889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929889 prefixEnd_1929889 := by exact prefixLift 1929889
  have htrace : WordTrace (prefixWord ++ tailWord_1929889) baseStart_1929889 baseEnd_1929889 := by
    simpa [prefixWord, tailWord_1929889, baseEnd_1929889] using wordTrace_append hprefix tailTrace_1929889
  have hstable : (prefixWord ++ tailWord_1929889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929889).length < 2 ^ (prefixWord ++ tailWord_1929889).sum := by decide
  have hdescent : baseEnd_1929889 < baseStart_1929889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929897 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_1929897 : Nat := 118140960795 + 1929897 * 2 ^ 59
def prefixEnd_1929897 : Nat := 4983230072969 + 3 ^ 40 * 1929897 * 2
def baseEnd_1929897 : Nat := 990964774670141002812071

theorem tailTrace_1929897 : CollatzResearch.WordTrace tailWord_1929897 prefixEnd_1929897 990964774670141002812071 := by
  unfold tailWord_1929897
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389126289320244011899945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46926084192880162674599963 70389126289320244011899945)
  ·
    refine ⟨52791844716990183008924959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70389126289320244011899945 52791844716990183008924959)
    ·
      refine ⟨79187767075485274513387439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52791844716990183008924959 79187767075485274513387439)
      ·
        refine ⟨118781650613227911770081159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79187767075485274513387439 118781650613227911770081159)
        ·
          refine ⟨178172475919841867655121739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118781650613227911770081159 178172475919841867655121739)
          ·
            refine ⟨267258713879762801482682609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178172475919841867655121739 267258713879762801482682609)
            ·
              refine ⟨200444035409822101112011957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267258713879762801482682609 200444035409822101112011957)
              ·
                refine ⟨18791628319670821979251121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200444035409822101112011957 18791628319670821979251121)
                ·
                  refine ⟨14093721239753116484438341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18791628319670821979251121 14093721239753116484438341)
                  ·
                    refine ⟨2642572732453709340832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14093721239753116484438341 2642572732453709340832189)
                    ·
                      refine ⟨990964774670141002812071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642572732453709340832189 990964774670141002812071)
                      ·
                        rfl

theorem cell23_1929897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_1929897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929897 prefixEnd_1929897 := by exact prefixLift 1929897
  have htrace : WordTrace (prefixWord ++ tailWord_1929897) baseStart_1929897 baseEnd_1929897 := by
    simpa [prefixWord, tailWord_1929897, baseEnd_1929897] using wordTrace_append hprefix tailTrace_1929897
  have hstable : (prefixWord ++ tailWord_1929897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929897).length < 2 ^ (prefixWord ++ tailWord_1929897).sum := by decide
  have hdescent : baseEnd_1929897 < baseStart_1929897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929907 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_1929907 : Nat := 118140960795 + 1929907 * 2 ^ 59
def prefixEnd_1929907 : Nat := 4983230072969 + 3 ^ 40 * 1929907 * 2
def baseEnd_1929907 : Nat := 990969909476685963687025

theorem tailTrace_1929907 : CollatzResearch.WordTrace tailWord_1929907 prefixEnd_1929907 990969909476685963687025 := by
  unfold tailWord_1929907
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389491019284015719763975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46926327346189343813175983 70389491019284015719763975)
  ·
    refine ⟨105584236528926023579645963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70389491019284015719763975 105584236528926023579645963)
    ·
      refine ⟨158376354793389035369468945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105584236528926023579645963 158376354793389035369468945)
      ·
        refine ⟨118782266095041776527101709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158376354793389035369468945 118782266095041776527101709)
        ·
          refine ⟨44543349785640666197663141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118782266095041776527101709 44543349785640666197663141)
          ·
            refine ⟨8351878084807624912061839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44543349785640666197663141 8351878084807624912061839)
            ·
              refine ⟨12527817127211437368092759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351878084807624912061839 12527817127211437368092759)
              ·
                refine ⟨18791725690817156052139139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527817127211437368092759 18791725690817156052139139)
                ·
                  refine ⟨28187588536225734078208709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18791725690817156052139139 28187588536225734078208709)
                  ·
                    refine ⟨5285172850542325139664133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28187588536225734078208709 5285172850542325139664133)
                    ·
                      refine ⟨990969909476685963687025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5285172850542325139664133 990969909476685963687025)
                      ·
                        rfl

theorem cell23_1929907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_1929907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929907 prefixEnd_1929907 := by exact prefixLift 1929907
  have htrace : WordTrace (prefixWord ++ tailWord_1929907) baseStart_1929907 baseEnd_1929907 := by
    simpa [prefixWord, tailWord_1929907, baseEnd_1929907] using wordTrace_append hprefix tailTrace_1929907
  have hstable : (prefixWord ++ tailWord_1929907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929907).length < 2 ^ (prefixWord ++ tailWord_1929907).sum := by decide
  have hdescent : baseEnd_1929907 < baseStart_1929907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929917 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 9]
def baseStart_1929917 : Nat := 118140960795 + 1929917 * 2 ^ 59
def prefixEnd_1929917 : Nat := 4983230072969 + 3 ^ 40 * 1929917 * 2
def baseEnd_1929917 : Nat := 110108338253692324951331

theorem tailTrace_1929917 : CollatzResearch.WordTrace tailWord_1929917 prefixEnd_1929917 110108338253692324951331 := by
  unfold tailWord_1929917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389855749247787427628005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46926570499498524951752003 70389855749247787427628005)
  ·
    refine ⟨13198097952983960142680251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70389855749247787427628005 13198097952983960142680251)
    ·
      refine ⟨19797146929475940214020377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13198097952983960142680251 19797146929475940214020377)
      ·
        refine ⟨14847860197106955160515283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19797146929475940214020377 14847860197106955160515283)
        ·
          refine ⟨22271790295660432740772925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14847860197106955160515283 22271790295660432740772925)
          ·
            refine ⟨8351921360872662277789847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22271790295660432740772925 8351921360872662277789847)
            ·
              refine ⟨12527882041308993416684771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351921360872662277789847 12527882041308993416684771)
              ·
                refine ⟨18791823061963490125027157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527882041308993416684771 18791823061963490125027157)
                ·
                  refine ⟨110108338253692324951331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18791823061963490125027157 110108338253692324951331)
                  ·
                    rfl

theorem cell23_1929917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_1929917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929917 prefixEnd_1929917 := by exact prefixLift 1929917
  have htrace : WordTrace (prefixWord ++ tailWord_1929917) baseStart_1929917 baseEnd_1929917 := by
    simpa [prefixWord, tailWord_1929917, baseEnd_1929917] using wordTrace_append hprefix tailTrace_1929917
  have hstable : (prefixWord ++ tailWord_1929917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929917).length < 2 ^ (prefixWord ++ tailWord_1929917).sum := by decide
  have hdescent : baseEnd_1929917 < baseStart_1929917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929944 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1929944 : Nat := 118140960795 + 1929944 * 2 ^ 59
def prefixEnd_1929944 : Nat := 4983230072969 + 3 ^ 40 * 1929944 * 2
def baseEnd_1929944 : Nat := 990988908260902318924355

theorem tailTrace_1929944 : CollatzResearch.WordTrace tailWord_1929944 prefixEnd_1929944 990988908260902318924355 := by
  unfold tailWord_1929944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35195420260074985519430443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46927227013433314025907257 35195420260074985519430443)
  ·
    refine ⟨52793130390112478279145665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35195420260074985519430443 52793130390112478279145665)
    ·
      refine ⟨39594847792584358709359249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52793130390112478279145665 39594847792584358709359249)
      ·
        refine ⟨29696135844438269032019437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39594847792584358709359249 29696135844438269032019437)
        ·
          refine ⟨11136050941664350887007289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29696135844438269032019437 11136050941664350887007289)
          ·
            refine ⟨8352038206248263165255467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11136050941664350887007289 8352038206248263165255467)
            ·
              refine ⟨12528057309372394747883201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352038206248263165255467 12528057309372394747883201)
              ·
                refine ⟨9396042982029296060912401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528057309372394747883201 9396042982029296060912401)
                ·
                  refine ⟨7047032236521972045684301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9396042982029296060912401 7047032236521972045684301)
                  ·
                    refine ⟨2642637088695739517131613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7047032236521972045684301 2642637088695739517131613)
                    ·
                      refine ⟨990988908260902318924355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642637088695739517131613 990988908260902318924355)
                      ·
                        rfl

theorem cell23_1929944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1929944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929944 prefixEnd_1929944 := by exact prefixLift 1929944
  have htrace : WordTrace (prefixWord ++ tailWord_1929944) baseStart_1929944 baseEnd_1929944 := by
    simpa [prefixWord, tailWord_1929944, baseEnd_1929944] using wordTrace_append hprefix tailTrace_1929944
  have hstable : (prefixWord ++ tailWord_1929944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929944).length < 2 ^ (prefixWord ++ tailWord_1929944).sum := by decide
  have hdescent : baseEnd_1929944 < baseStart_1929944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929987 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1929987 : Nat := 118140960795 + 1929987 * 2 ^ 59
def prefixEnd_1929987 : Nat := 4983230072969 + 3 ^ 40 * 1929987 * 2
def baseEnd_1929987 : Nat := 991010987929045650686657

theorem tailTrace_1929987 : CollatzResearch.WordTrace tailWord_1929987 prefixEnd_1929987 991010987929045650686657 := by
  unfold tailWord_1929987
  simp only [CollatzResearch.WordTrace]
  refine ⟨70392408858994189382676215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46928272572662792921784143 70392408858994189382676215)
  ·
    refine ⟨105588613288491284074014323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70392408858994189382676215 105588613288491284074014323)
    ·
      refine ⟨158382919932736926111021485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105588613288491284074014323 158382919932736926111021485)
      ·
        refine ⟨59393594974776347291633057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158382919932736926111021485 59393594974776347291633057)
        ·
          refine ⟨44545196231082260468724793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59393594974776347291633057 44545196231082260468724793)
          ·
            refine ⟨33408897173311695351543595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44545196231082260468724793 33408897173311695351543595)
            ·
              refine ⟨50113345759967543027315393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33408897173311695351543595 50113345759967543027315393)
              ·
                refine ⟨37585009319975657270486545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50113345759967543027315393 37585009319975657270486545)
                ·
                  refine ⟨28188756989981742952864909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37585009319975657270486545 28188756989981742952864909)
                  ·
                    refine ⟨10570783871243153607324341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28188756989981742952864909 10570783871243153607324341)
                    ·
                      refine ⟨991010987929045650686657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10570783871243153607324341 991010987929045650686657)
                      ·
                        rfl

theorem cell23_1929987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1929987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1929987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1929987 prefixEnd_1929987 := by exact prefixLift 1929987
  have htrace : WordTrace (prefixWord ++ tailWord_1929987) baseStart_1929987 baseEnd_1929987 := by
    simpa [prefixWord, tailWord_1929987, baseEnd_1929987] using wordTrace_append hprefix tailTrace_1929987
  have hstable : (prefixWord ++ tailWord_1929987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929987).length < 2 ^ (prefixWord ++ tailWord_1929987).sum := by decide
  have hdescent : baseEnd_1929987 < baseStart_1929987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_1930027 : Nat := 118140960795 + 1930027 * 2 ^ 59
def prefixEnd_1930027 : Nat := 4983230072969 + 3 ^ 40 * 1930027 * 2
def baseEnd_1930027 : Nat := 991031527155225494186473

theorem tailTrace_1930027 : CollatzResearch.WordTrace tailWord_1930027 prefixEnd_1930027 991031527155225494186473 := by
  unfold tailWord_1930027
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393867778849276214132335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46929245185899517476088223 70393867778849276214132335)
  ·
    refine ⟨105590801668273914321198503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70393867778849276214132335 105590801668273914321198503)
    ·
      refine ⟨158386202502410871481797755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105590801668273914321198503 158386202502410871481797755)
      ·
        refine ⟨237579303753616307222696633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158386202502410871481797755 237579303753616307222696633)
        ·
          refine ⟨178184477815212230417022475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237579303753616307222696633 178184477815212230417022475)
          ·
            refine ⟨267276716722818345625533713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178184477815212230417022475 267276716722818345625533713)
            ·
              refine ⟨200457537542113759219150285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267276716722818345625533713 200457537542113759219150285)
              ·
                refine ⟨75171576578292659707181357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200457537542113759219150285 75171576578292659707181357)
                ·
                  refine ⟨28189341216859747390193009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75171576578292659707181357 28189341216859747390193009)
                  ·
                    refine ⟨21142005912644810542644757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28189341216859747390193009 21142005912644810542644757)
                    ·
                      refine ⟨991031527155225494186473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21142005912644810542644757 991031527155225494186473)
                      ·
                        rfl

theorem cell23_1930027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_1930027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930027 prefixEnd_1930027 := by exact prefixLift 1930027
  have htrace : WordTrace (prefixWord ++ tailWord_1930027) baseStart_1930027 baseEnd_1930027 := by
    simpa [prefixWord, tailWord_1930027, baseEnd_1930027] using wordTrace_append hprefix tailTrace_1930027
  have hstable : (prefixWord ++ tailWord_1930027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930027).length < 2 ^ (prefixWord ++ tailWord_1930027).sum := by decide
  have hdescent : baseEnd_1930027 < baseStart_1930027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930101 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1930101 : Nat := 118140960795 + 1930101 * 2 ^ 59
def prefixEnd_1930101 : Nat := 4983230072969 + 3 ^ 40 * 1930101 * 2
def baseEnd_1930101 : Nat := 330356508241219401553711

theorem tailTrace_1930101 : CollatzResearch.WordTrace tailWord_1930101 prefixEnd_1930101 330356508241219401553711 := by
  unfold tailWord_1930101
  simp only [CollatzResearch.WordTrace]
  refine ⟨70396566780581186852326157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46931044520387457901550771 70396566780581186852326157)
  ·
    refine ⟨26398712542717945069622309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70396566780581186852326157 26398712542717945069622309)
    ·
      refine ⟨4949758601759614700554183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26398712542717945069622309 4949758601759614700554183)
      ·
        refine ⟨7424637902639422050831275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4949758601759614700554183 7424637902639422050831275)
        ·
          refine ⟨11136956853959133076246913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424637902639422050831275 11136956853959133076246913)
          ·
            refine ⟨8352717640469349807185185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11136956853959133076246913 8352717640469349807185185)
            ·
              refine ⟨6264538230352012355388889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8352717640469349807185185 6264538230352012355388889)
              ·
                refine ⟨4698403672764009266541667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264538230352012355388889 4698403672764009266541667)
                ·
                  refine ⟨7047605509146013899812501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698403672764009266541667 7047605509146013899812501)
                  ·
                    refine ⟨330356508241219401553711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7047605509146013899812501 330356508241219401553711)
                    ·
                      rfl

theorem cell23_1930101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1930101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930101 prefixEnd_1930101 := by exact prefixLift 1930101
  have htrace : WordTrace (prefixWord ++ tailWord_1930101) baseStart_1930101 baseEnd_1930101 := by
    simpa [prefixWord, tailWord_1930101, baseEnd_1930101] using wordTrace_append hprefix tailTrace_1930101
  have hstable : (prefixWord ++ tailWord_1930101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930101).length < 2 ^ (prefixWord ++ tailWord_1930101).sum := by decide
  have hdescent : baseEnd_1930101 < baseStart_1930101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930102 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1930102 : Nat := 118140960795 + 1930102 * 2 ^ 59
def prefixEnd_1930102 : Nat := 4983230072969 + 3 ^ 40 * 1930102 * 2
def baseEnd_1930102 : Nat := 991070038204312700748629

theorem tailTrace_1930102 : CollatzResearch.WordTrace tailWord_1930102 prefixEnd_1930102 991070038204312700748629 := by
  unfold tailWord_1930102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399787703348597751444535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46931068835718376015408373 4399787703348597751444535)
  ·
    refine ⟨6599681555022896627166803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4399787703348597751444535 6599681555022896627166803)
    ·
      refine ⟨9899522332534344940750205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6599681555022896627166803 9899522332534344940750205)
      ·
        refine ⟨3712320874700379352781327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9899522332534344940750205 3712320874700379352781327)
        ·
          refine ⟨5568481312050569029171991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712320874700379352781327 5568481312050569029171991)
          ·
            refine ⟨8352721968075853543757987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568481312050569029171991 8352721968075853543757987)
            ·
              refine ⟨12529082952113780315636981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352721968075853543757987 12529082952113780315636981)
              ·
                refine ⟨1174601526760666904590967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12529082952113780315636981 1174601526760666904590967)
                ·
                  refine ⟨1761902290141000356886451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174601526760666904590967 1761902290141000356886451)
                  ·
                    refine ⟨2642853435211500535329677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761902290141000356886451 2642853435211500535329677)
                    ·
                      refine ⟨991070038204312700748629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642853435211500535329677 991070038204312700748629)
                      ·
                        rfl

theorem cell23_1930102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1930102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930102 prefixEnd_1930102 := by exact prefixLift 1930102
  have htrace : WordTrace (prefixWord ++ tailWord_1930102) baseStart_1930102 baseEnd_1930102 := by
    simpa [prefixWord, tailWord_1930102, baseEnd_1930102] using wordTrace_append hprefix tailTrace_1930102
  have hstable : (prefixWord ++ tailWord_1930102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930102).length < 2 ^ (prefixWord ++ tailWord_1930102).sum := by decide
  have hdescent : baseEnd_1930102 < baseStart_1930102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930104 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1930104 : Nat := 118140960795 + 1930104 * 2 ^ 59
def prefixEnd_1930104 : Nat := 4983230072969 + 3 ^ 40 * 1930104 * 2
def baseEnd_1930104 : Nat := 991071065165621692923619

theorem tailTrace_1930104 : CollatzResearch.WordTrace tailWord_1930104 prefixEnd_1930104 991071065165621692923619 := by
  unfold tailWord_1930104
  simp only [CollatzResearch.WordTrace]
  refine ⟨35198338099785159182342683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46931117466380212243123577 35198338099785159182342683)
  ·
    refine ⟨52797507149677738773514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35198338099785159182342683 52797507149677738773514025)
    ·
      refine ⟨39598130362258304080135519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52797507149677738773514025 39598130362258304080135519)
      ·
        refine ⟨59397195543387456120203279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39598130362258304080135519 59397195543387456120203279)
        ·
          refine ⟨89095793315081184180304919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59397195543387456120203279 89095793315081184180304919)
          ·
            refine ⟨133643689972621776270457379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89095793315081184180304919 133643689972621776270457379)
            ·
              refine ⟨200465534958932664405686069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133643689972621776270457379 200465534958932664405686069)
              ·
                refine ⟨18793643902399937288033069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200465534958932664405686069 18793643902399937288033069)
                ·
                  refine ⟨7047616463399976483012401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18793643902399937288033069 7047616463399976483012401)
                  ·
                    refine ⟨5285712347549982362259301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047616463399976483012401 5285712347549982362259301)
                    ·
                      refine ⟨991071065165621692923619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5285712347549982362259301 991071065165621692923619)
                      ·
                        rfl

theorem cell23_1930104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1930104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930104 prefixEnd_1930104 := by exact prefixLift 1930104
  have htrace : WordTrace (prefixWord ++ tailWord_1930104) baseStart_1930104 baseEnd_1930104 := by
    simpa [prefixWord, tailWord_1930104, baseEnd_1930104] using wordTrace_append hprefix tailTrace_1930104
  have hstable : (prefixWord ++ tailWord_1930104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930104).length < 2 ^ (prefixWord ++ tailWord_1930104).sum := by decide
  have hdescent : baseEnd_1930104 < baseStart_1930104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930144 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_1930144 : Nat := 118140960795 + 1930144 * 2 ^ 59
def prefixEnd_1930144 : Nat := 4983230072969 + 3 ^ 40 * 1930144 * 2
def baseEnd_1930144 : Nat := 330363868130600512141145

theorem tailTrace_1930144 : CollatzResearch.WordTrace tailWord_1930144 prefixEnd_1930144 330363868130600512141145 := by
  unfold tailWord_1930144
  simp only [CollatzResearch.WordTrace]
  refine ⟨35199067559712702598070743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46932090079616936797427657 35199067559712702598070743)
  ·
    refine ⟨52798601339569053897106115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35199067559712702598070743 52798601339569053897106115)
    ·
      refine ⟨79197902009353580845659173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52798601339569053897106115 79197902009353580845659173)
      ·
        refine ⟨14849606626753796408561095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79197902009353580845659173 14849606626753796408561095)
        ·
          refine ⟨22274409940130694612841643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14849606626753796408561095 22274409940130694612841643)
          ·
            refine ⟨33411614910196041919262465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22274409940130694612841643 33411614910196041919262465)
            ·
              refine ⟨25058711182647031439446849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33411614910196041919262465 25058711182647031439446849)
              ·
                refine ⟨18794033386985273579585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25058711182647031439446849 18794033386985273579585137)
                ·
                  refine ⟨14095525040238955184688853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18794033386985273579585137 14095525040238955184688853)
                  ·
                    refine ⟨330363868130600512141145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14095525040238955184688853 330363868130600512141145)
                    ·
                      rfl

theorem cell23_1930144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_1930144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930144 prefixEnd_1930144 := by exact prefixLift 1930144
  have htrace : WordTrace (prefixWord ++ tailWord_1930144) baseStart_1930144 baseEnd_1930144 := by
    simpa [prefixWord, tailWord_1930144, baseEnd_1930144] using wordTrace_append hprefix tailTrace_1930144
  have hstable : (prefixWord ++ tailWord_1930144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930144).length < 2 ^ (prefixWord ++ tailWord_1930144).sum := by decide
  have hdescent : baseEnd_1930144 < baseStart_1930144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930145 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1930145 : Nat := 118140960795 + 1930145 * 2 ^ 59
def prefixEnd_1930145 : Nat := 4983230072969 + 3 ^ 40 * 1930145 * 2
def baseEnd_1930145 : Nat := 991092117872456032510931

theorem tailTrace_1930145 : CollatzResearch.WordTrace tailWord_1930145 prefixEnd_1930145 991092117872456032510931 := by
  unfold tailWord_1930145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70398171592421782366927889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46932114394947854911285259 70398171592421782366927889)
  ·
    refine ⟨52798628694316336775195917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70398171592421782366927889 52798628694316336775195917)
    ·
      refine ⟨19799485760368626290698469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52798628694316336775195917 19799485760368626290698469)
      ·
        refine ⟨3712403580069117429505963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19799485760368626290698469 3712403580069117429505963)
        ·
          refine ⟨5568605370103676144258945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712403580069117429505963 5568605370103676144258945)
          ·
            refine ⟨4176454027577757108194209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568605370103676144258945 4176454027577757108194209)
            ·
              refine ⟨3132340520683317831145657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176454027577757108194209 3132340520683317831145657)
              ·
                refine ⟨2349255390512488373359243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132340520683317831145657 2349255390512488373359243)
                ·
                  refine ⟨3523883085768732560038865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349255390512488373359243 3523883085768732560038865)
                  ·
                    refine ⟨2642912314326549420029149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523883085768732560038865 2642912314326549420029149)
                    ·
                      refine ⟨991092117872456032510931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2642912314326549420029149 991092117872456032510931)
                      ·
                        rfl

theorem cell23_1930145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1930145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930145 prefixEnd_1930145 := by exact prefixLift 1930145
  have htrace : WordTrace (prefixWord ++ tailWord_1930145) baseStart_1930145 baseEnd_1930145 := by
    simpa [prefixWord, tailWord_1930145, baseEnd_1930145] using wordTrace_append hprefix tailTrace_1930145
  have hstable : (prefixWord ++ tailWord_1930145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930145).length < 2 ^ (prefixWord ++ tailWord_1930145).sum := by decide
  have hdescent : baseEnd_1930145 < baseStart_1930145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930201 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1930201 : Nat := 118140960795 + 1930201 * 2 ^ 59
def prefixEnd_1930201 : Nat := 4983230072969 + 3 ^ 40 * 1930201 * 2
def baseEnd_1930201 : Nat := 991120872789107813410673

theorem tailTrace_1930201 : CollatzResearch.WordTrace tailWord_1930201 prefixEnd_1930201 991120872789107813410673 := by
  unfold tailWord_1930201
  simp only [CollatzResearch.WordTrace]
  refine ⟨70400214080218903930966457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46933476053479269287310971 70400214080218903930966457)
  ·
    refine ⟨52800160560164177948224843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70400214080218903930966457 52800160560164177948224843)
    ·
      refine ⟨79200240840246266922337265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52800160560164177948224843 79200240840246266922337265)
      ·
        refine ⟨59400180630184700191752949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79200240840246266922337265 59400180630184700191752949)
        ·
          refine ⟨5568766934079815642976839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59400180630184700191752949 5568766934079815642976839)
          ·
            refine ⟨8353150401119723464465259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568766934079815642976839 8353150401119723464465259)
            ·
              refine ⟨12529725601679585196697889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353150401119723464465259 12529725601679585196697889)
              ·
                refine ⟨9397294201259688897523417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12529725601679585196697889 9397294201259688897523417)
                ·
                  refine ⟨7047970650944766673142563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9397294201259688897523417 7047970650944766673142563)
                  ·
                    refine ⟨10571955976417150009713845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047970650944766673142563 10571955976417150009713845)
                    ·
                      refine ⟨991120872789107813410673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10571955976417150009713845 991120872789107813410673)
                      ·
                        rfl

theorem cell23_1930201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1930201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930201 prefixEnd_1930201 := by exact prefixLift 1930201
  have htrace : WordTrace (prefixWord ++ tailWord_1930201) baseStart_1930201 baseEnd_1930201 := by
    simpa [prefixWord, tailWord_1930201, baseEnd_1930201] using wordTrace_append hprefix tailTrace_1930201
  have hstable : (prefixWord ++ tailWord_1930201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930201).length < 2 ^ (prefixWord ++ tailWord_1930201).sum := by decide
  have hdescent : baseEnd_1930201 < baseStart_1930201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930202 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_1930202 : Nat := 118140960795 + 1930202 * 2 ^ 59
def prefixEnd_1930202 : Nat := 4983230072969 + 3 ^ 40 * 1930202 * 2
def baseEnd_1930202 : Nat := 991121386269762309498169

theorem tailTrace_1930202 : CollatzResearch.WordTrace tailWord_1930202 prefixEnd_1930202 991121386269762309498169 := by
  unfold tailWord_1930202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600062638303820275438215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46933500368810187401168573 17600062638303820275438215)
  ·
    refine ⟨26400093957455730413157323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17600062638303820275438215 26400093957455730413157323)
    ·
      refine ⟨39600140936183595619735985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26400093957455730413157323 39600140936183595619735985)
      ·
        refine ⟨29700105702137696714801989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39600140936183595619735985 29700105702137696714801989)
        ·
          refine ⟨5568769819150818134025373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29700105702137696714801989 5568769819150818134025373)
          ·
            refine ⟨2088288682181556800259515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5568769819150818134025373 2088288682181556800259515)
            ·
              refine ⟨3132433023272335200389273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088288682181556800259515 3132433023272335200389273)
              ·
                refine ⟨2349324767454251400291955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132433023272335200389273 2349324767454251400291955)
                ·
                  refine ⟨3523987151181377100437933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349324767454251400291955 3523987151181377100437933)
                  ·
                    refine ⟨1321495181693016412664225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3523987151181377100437933 1321495181693016412664225)
                    ·
                      refine ⟨991121386269762309498169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321495181693016412664225 991121386269762309498169)
                      ·
                        rfl

theorem cell23_1930202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_1930202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930202 prefixEnd_1930202 := by exact prefixLift 1930202
  have htrace : WordTrace (prefixWord ++ tailWord_1930202) baseStart_1930202 baseEnd_1930202 := by
    simpa [prefixWord, tailWord_1930202, baseEnd_1930202] using wordTrace_append hprefix tailTrace_1930202
  have hstable : (prefixWord ++ tailWord_1930202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930202).length < 2 ^ (prefixWord ++ tailWord_1930202).sum := by decide
  have hdescent : baseEnd_1930202 < baseStart_1930202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930215 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1930215 : Nat := 118140960795 + 1930215 * 2 ^ 59
def prefixEnd_1930215 : Nat := 4983230072969 + 3 ^ 40 * 1930215 * 2
def baseEnd_1930215 : Nat := 991128061518270758635609

theorem tailTrace_1930215 : CollatzResearch.WordTrace tailWord_1930215 prefixEnd_1930215 991128061518270758635609 := by
  unfold tailWord_1930215
  simp only [CollatzResearch.WordTrace]
  refine ⟨70400724702168184321976099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46933816468112122881317399 70400724702168184321976099)
  ·
    refine ⟨105601087053252276482964149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70400724702168184321976099 105601087053252276482964149)
    ·
      refine ⟨9900101911242400920277889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105601087053252276482964149 9900101911242400920277889)
      ·
        refine ⟨7425076433431800690208417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9900101911242400920277889 7425076433431800690208417)
        ·
          refine ⟨5568807325073850517656313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425076433431800690208417 5568807325073850517656313)
          ·
            refine ⟨4176605493805387888242235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568807325073850517656313 4176605493805387888242235)
            ·
              refine ⟨6264908240708081832363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176605493805387888242235 6264908240708081832363353)
              ·
                refine ⟨4698681180531061374272515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264908240708081832363353 4698681180531061374272515)
                ·
                  refine ⟨7048021770796592061408773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698681180531061374272515 7048021770796592061408773)
                  ·
                    refine ⟨1321504082024361011514145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048021770796592061408773 1321504082024361011514145)
                    ·
                      refine ⟨991128061518270758635609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321504082024361011514145 991128061518270758635609)
                      ·
                        rfl

theorem cell23_1930215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1930215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930215 prefixEnd_1930215 := by exact prefixLift 1930215
  have htrace : WordTrace (prefixWord ++ tailWord_1930215) baseStart_1930215 baseEnd_1930215 := by
    simpa [prefixWord, tailWord_1930215, baseEnd_1930215] using wordTrace_append hprefix tailTrace_1930215
  have hstable : (prefixWord ++ tailWord_1930215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930215).length < 2 ^ (prefixWord ++ tailWord_1930215).sum := by decide
  have hdescent : baseEnd_1930215 < baseStart_1930215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930248 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1930248 : Nat := 118140960795 + 1930248 * 2 ^ 59
def prefixEnd_1930248 : Nat := 4983230072969 + 3 ^ 40 * 1930248 * 2
def baseEnd_1930248 : Nat := 991145006379869129522957

theorem tailTrace_1930248 : CollatzResearch.WordTrace tailWord_1930248 prefixEnd_1930248 991145006379869129522957 := by
  unfold tailWord_1930248
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200964155524315478963699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46934618874032420638618265 35200964155524315478963699)
  ·
    refine ⟨52801446233286473218445549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35200964155524315478963699 52801446233286473218445549)
    ·
      refine ⟨19800542337482427456917081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52801446233286473218445549 19800542337482427456917081)
      ·
        refine ⟨14850406753111820592687811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19800542337482427456917081 14850406753111820592687811)
        ·
          refine ⟨22275610129667730889031717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14850406753111820592687811 22275610129667730889031717)
          ·
            refine ⟨4176676899312699541693447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22275610129667730889031717 4176676899312699541693447)
            ·
              refine ⟨6265015348969049312540171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176676899312699541693447 6265015348969049312540171)
              ·
                refine ⟨9397523023453573968810257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265015348969049312540171 9397523023453573968810257)
                ·
                  refine ⟨7048142267590180476607693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9397523023453573968810257 7048142267590180476607693)
                  ·
                    refine ⟨2643053350346317678727885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7048142267590180476607693 2643053350346317678727885)
                    ·
                      refine ⟨991145006379869129522957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2643053350346317678727885 991145006379869129522957)
                      ·
                        rfl

theorem cell23_1930248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1930248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930248 prefixEnd_1930248 := by exact prefixLift 1930248
  have htrace : WordTrace (prefixWord ++ tailWord_1930248) baseStart_1930248 baseEnd_1930248 := by
    simpa [prefixWord, tailWord_1930248, baseEnd_1930248] using wordTrace_append hprefix tailTrace_1930248
  have hstable : (prefixWord ++ tailWord_1930248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930248).length < 2 ^ (prefixWord ++ tailWord_1930248).sum := by decide
  have hdescent : baseEnd_1930248 < baseStart_1930248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930268 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1930268 : Nat := 118140960795 + 1930268 * 2 ^ 59
def prefixEnd_1930268 : Nat := 4983230072969 + 3 ^ 40 * 1930268 * 2
def baseEnd_1930268 : Nat := 330385091997653017090955

theorem tailTrace_1930268 : CollatzResearch.WordTrace tailWord_1930268 prefixEnd_1930268 330385091997653017090955 := by
  unfold tailWord_1930268
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201328885488087186827729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46935105180650782915770305 35201328885488087186827729)
  ·
    refine ⟨26400996664116065390120797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35201328885488087186827729 26400996664116065390120797)
    ·
      refine ⟨9900373749043524521295299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26400996664116065390120797 9900373749043524521295299)
      ·
        refine ⟨14850560623565286781942949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900373749043524521295299 14850560623565286781942949)
        ·
          refine ⟨2784480116918491271614303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14850560623565286781942949 2784480116918491271614303)
          ·
            refine ⟨4176720175377736907421455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784480116918491271614303 4176720175377736907421455)
            ·
              refine ⟨6265080263066605361132183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176720175377736907421455 6265080263066605361132183)
              ·
                refine ⟨9397620394599908041698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265080263066605361132183 9397620394599908041698275)
                ·
                  refine ⟨14096430591899862062547413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397620394599908041698275 14096430591899862062547413)
                  ·
                    refine ⟨330385091997653017090955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14096430591899862062547413 330385091997653017090955)
                    ·
                      rfl

theorem cell23_1930268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1930268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930268 prefixEnd_1930268 := by exact prefixLift 1930268
  have htrace : WordTrace (prefixWord ++ tailWord_1930268) baseStart_1930268 baseEnd_1930268 := by
    simpa [prefixWord, tailWord_1930268, baseEnd_1930268] using wordTrace_append hprefix tailTrace_1930268
  have hstable : (prefixWord ++ tailWord_1930268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930268).length < 2 ^ (prefixWord ++ tailWord_1930268).sum := by decide
  have hdescent : baseEnd_1930268 < baseStart_1930268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930272 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 5]
def baseStart_1930272 : Nat := 118140960795 + 1930272 * 2 ^ 59
def prefixEnd_1930272 : Nat := 4983230072969 + 3 ^ 40 * 1930272 * 2
def baseEnd_1930272 : Nat := 110128592212841892846983

theorem tailTrace_1930272 : CollatzResearch.WordTrace tailWord_1930272 prefixEnd_1930272 110128592212841892846983 := by
  unfold tailWord_1930272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201401831480841528400535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46935202441974455371200713 35201401831480841528400535)
  ·
    refine ⟨52802102747221262292600803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35201401831480841528400535 52802102747221262292600803)
    ·
      refine ⟨79203154120831893438901205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802102747221262292600803 79203154120831893438901205)
      ·
        refine ⟨1856323924706997502474247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79203154120831893438901205 1856323924706997502474247)
        ·
          refine ⟨2784485887060496253711371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856323924706997502474247 2784485887060496253711371)
          ·
            refine ⟨4176728830590744380567057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784485887060496253711371 4176728830590744380567057)
            ·
              refine ⟨3132546622943058285425293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176728830590744380567057 3132546622943058285425293)
              ·
                refine ⟨1174704983603646857034485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3132546622943058285425293 1174704983603646857034485)
                ·
                  refine ⟨110128592212841892846983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174704983603646857034485 110128592212841892846983)
                  ·
                    rfl

theorem cell23_1930272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 5].length) (baseStart_1930272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930272 prefixEnd_1930272 := by exact prefixLift 1930272
  have htrace : WordTrace (prefixWord ++ tailWord_1930272) baseStart_1930272 baseEnd_1930272 := by
    simpa [prefixWord, tailWord_1930272, baseEnd_1930272] using wordTrace_append hprefix tailTrace_1930272
  have hstable : (prefixWord ++ tailWord_1930272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930272).length < 2 ^ (prefixWord ++ tailWord_1930272).sum := by decide
  have hdescent : baseEnd_1930272 < baseStart_1930272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930288 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2]
def baseStart_1930288 : Nat := 118140960795 + 1930288 * 2 ^ 59
def prefixEnd_1930288 : Nat := 4983230072969 + 3 ^ 40 * 1930288 * 2
def baseEnd_1930288 : Nat := 991165545606048973022773

theorem tailTrace_1930288 : CollatzResearch.WordTrace tailWord_1930288 prefixEnd_1930288 991165545606048973022773 := by
  unfold tailWord_1930288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201693615451858894691759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46935591487269145192922345 35201693615451858894691759)
  ·
    refine ⟨52802540423177788342037639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35201693615451858894691759 52802540423177788342037639)
    ·
      refine ⟨79203810634766682513056459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802540423177788342037639 79203810634766682513056459)
      ·
        refine ⟨118805715952150023769584689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79203810634766682513056459 118805715952150023769584689)
        ·
          refine ⟨89104286964112517827188517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118805715952150023769584689 89104286964112517827188517)
          ·
            refine ⟨16707053805771097092597847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89104286964112517827188517 16707053805771097092597847)
            ·
              refine ⟨25060580708656645638896771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707053805771097092597847 25060580708656645638896771)
              ·
                refine ⟨37590871062984968458345157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25060580708656645638896771 37590871062984968458345157)
                ·
                  refine ⟨7048288324309681585939717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37590871062984968458345157 7048288324309681585939717)
                  ·
                    refine ⟨1321554060808065297363697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048288324309681585939717 1321554060808065297363697)
                    ·
                      refine ⟨991165545606048973022773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321554060808065297363697 991165545606048973022773)
                      ·
                        rfl

theorem cell23_1930288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2].length) (baseStart_1930288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930288 prefixEnd_1930288 := by exact prefixLift 1930288
  have htrace : WordTrace (prefixWord ++ tailWord_1930288) baseStart_1930288 baseEnd_1930288 := by
    simpa [prefixWord, tailWord_1930288, baseEnd_1930288] using wordTrace_append hprefix tailTrace_1930288
  have hstable : (prefixWord ++ tailWord_1930288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930288).length < 2 ^ (prefixWord ++ tailWord_1930288).sum := by decide
  have hdescent : baseEnd_1930288 < baseStart_1930288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930298 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1930298 : Nat := 118140960795 + 1930298 * 2 ^ 59
def prefixEnd_1930298 : Nat := 4983230072969 + 3 ^ 40 * 1930298 * 2
def baseEnd_1930298 : Nat := 330390226804197977965909

theorem tailTrace_1930298 : CollatzResearch.WordTrace tailWord_1930298 prefixEnd_1930298 330390226804197977965909 := by
  unfold tailWord_1930298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600937990216872374311887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46935834640578326331498365 17600937990216872374311887)
  ·
    refine ⟨26401406985325308561467831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17600937990216872374311887 26401406985325308561467831)
    ·
      refine ⟨39602110477987962842201747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26401406985325308561467831 39602110477987962842201747)
      ·
        refine ⟨59403165716981944263302621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39602110477987962842201747 59403165716981944263302621)
        ·
          refine ⟨22276187143868229098738483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59403165716981944263302621 22276187143868229098738483)
          ·
            refine ⟨33414280715802343648107725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22276187143868229098738483 33414280715802343648107725)
            ·
              refine ⟨12530355268425878868040397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33414280715802343648107725 12530355268425878868040397)
              ·
                refine ⟨4698883225659704575515149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12530355268425878868040397 4698883225659704575515149)
                ·
                  refine ⟨1762081209622389215818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4698883225659704575515149 1762081209622389215818181)
                  ·
                    refine ⟨330390226804197977965909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762081209622389215818181 330390226804197977965909)
                    ·
                      rfl

theorem cell23_1930298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1930298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930298 prefixEnd_1930298 := by exact prefixLift 1930298
  have htrace : WordTrace (prefixWord ++ tailWord_1930298) baseStart_1930298 baseEnd_1930298 := by
    simpa [prefixWord, tailWord_1930298, baseEnd_1930298] using wordTrace_append hprefix tailTrace_1930298
  have hstable : (prefixWord ++ tailWord_1930298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930298).length < 2 ^ (prefixWord ++ tailWord_1930298).sum := by decide
  have hdescent : baseEnd_1930298 < baseStart_1930298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930349 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1930349 : Nat := 118140960795 + 1930349 * 2 ^ 59
def prefixEnd_1930349 : Nat := 4983230072969 + 3 ^ 40 * 1930349 * 2
def baseEnd_1930349 : Nat := 330398955975324411453331

theorem tailTrace_1930349 : CollatzResearch.WordTrace tailWord_1930349 prefixEnd_1930349 330398955975324411453331 := by
  unfold tailWord_1930349
  simp only [CollatzResearch.WordTrace]
  refine ⟨70405612083682725207354101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46937074722455150138236067 70405612083682725207354101)
  ·
    refine ⟨6600526132845255488189447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70405612083682725207354101 6600526132845255488189447)
    ·
      refine ⟨9900789199267883232284171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600526132845255488189447 9900789199267883232284171)
      ·
        refine ⟨14851183798901824848426257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900789199267883232284171 14851183798901824848426257)
        ·
          refine ⟨11138387849176368636319693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14851183798901824848426257 11138387849176368636319693)
          ·
            refine ⟨4176895443441138238619885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11138387849176368636319693 4176895443441138238619885)
            ·
              refine ⟨1566335791290426839482457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4176895443441138238619885 1566335791290426839482457)
              ·
                refine ⟨1174751843467820129611843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566335791290426839482457 1174751843467820129611843)
                ·
                  refine ⟨1762127765201730194417765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174751843467820129611843 1762127765201730194417765)
                  ·
                    refine ⟨330398955975324411453331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762127765201730194417765 330398955975324411453331)
                    ·
                      rfl

theorem cell23_1930349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1930349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930349 prefixEnd_1930349 := by exact prefixLift 1930349
  have htrace : WordTrace (prefixWord ++ tailWord_1930349) baseStart_1930349 baseEnd_1930349 := by
    simpa [prefixWord, tailWord_1930349, baseEnd_1930349] using wordTrace_append hprefix tailTrace_1930349
  have hstable : (prefixWord ++ tailWord_1930349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930349).length < 2 ^ (prefixWord ++ tailWord_1930349).sum := by decide
  have hdescent : baseEnd_1930349 < baseStart_1930349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930365 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_1930365 : Nat := 118140960795 + 1930365 * 2 ^ 59
def prefixEnd_1930365 : Nat := 4983230072969 + 3 ^ 40 * 1930365 * 2
def baseEnd_1930365 : Nat := 991205083616445171759919

theorem tailTrace_1930365 : CollatzResearch.WordTrace tailWord_1930365 prefixEnd_1930365 991205083616445171759919 := by
  unfold tailWord_1930365
  simp only [CollatzResearch.WordTrace]
  refine ⟨70406195651624759939936549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46937463767749839959957699 70406195651624759939936549)
  ·
    refine ⟨13201161684679642488738103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70406195651624759939936549 13201161684679642488738103)
    ·
      refine ⟨19801742527019463733107155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201161684679642488738103 19801742527019463733107155)
      ·
        refine ⟨29702613790529195599660733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19801742527019463733107155 29702613790529195599660733)
        ·
          refine ⟨11138480171448448349872775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29702613790529195599660733 11138480171448448349872775)
          ·
            refine ⟨16707720257172672524809163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138480171448448349872775 16707720257172672524809163)
            ·
              refine ⟨25061580385759008787213745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707720257172672524809163 25061580385759008787213745)
              ·
                refine ⟨18796185289319256590410309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25061580385759008787213745 18796185289319256590410309)
                ·
                  refine ⟨3524284741747360610701933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18796185289319256590410309 3524284741747360610701933)
                  ·
                    refine ⟨1321606778155260229013225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524284741747360610701933 1321606778155260229013225)
                    ·
                      refine ⟨991205083616445171759919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321606778155260229013225 991205083616445171759919)
                      ·
                        rfl

theorem cell23_1930365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_1930365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930365 prefixEnd_1930365 := by exact prefixLift 1930365
  have htrace : WordTrace (prefixWord ++ tailWord_1930365) baseStart_1930365 baseEnd_1930365 := by
    simpa [prefixWord, tailWord_1930365, baseEnd_1930365] using wordTrace_append hprefix tailTrace_1930365
  have hstable : (prefixWord ++ tailWord_1930365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930365).length < 2 ^ (prefixWord ++ tailWord_1930365).sum := by decide
  have hdescent : baseEnd_1930365 < baseStart_1930365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930382 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1930382 : Nat := 118140960795 + 1930382 * 2 ^ 59
def prefixEnd_1930382 : Nat := 4983230072969 + 3 ^ 40 * 1930382 * 2
def baseEnd_1930382 : Nat := 991213812787571605247341

theorem tailTrace_1930382 : CollatzResearch.WordTrace tailWord_1930382 prefixEnd_1930382 991213812787571605247341 := by
  unfold tailWord_1930382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800851961570396480413175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46937877128375447895536933 8800851961570396480413175)
  ·
    refine ⟨13201277942355594720619763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8800851961570396480413175 13201277942355594720619763)
    ·
      refine ⟨19801916913533392080929645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201277942355594720619763 19801916913533392080929645)
      ·
        refine ⟨7425718842575022030348617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19801916913533392080929645 7425718842575022030348617)
        ·
          refine ⟨5569289131931266522761463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425718842575022030348617 5569289131931266522761463)
          ·
            refine ⟨8353933697896899784142195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569289131931266522761463 8353933697896899784142195)
            ·
              refine ⟨12530900546845349676213293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353933697896899784142195 12530900546845349676213293)
              ·
                refine ⟨4699087705067006128579985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12530900546845349676213293 4699087705067006128579985)
                ·
                  refine ⟨3524315778800254596434989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4699087705067006128579985 3524315778800254596434989)
                  ·
                    refine ⟨1321618417050095473663121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524315778800254596434989 1321618417050095473663121)
                    ·
                      refine ⟨991213812787571605247341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321618417050095473663121 991213812787571605247341)
                      ·
                        rfl

theorem cell23_1930382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1930382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930382 prefixEnd_1930382 := by exact prefixLift 1930382
  have htrace : WordTrace (prefixWord ++ tailWord_1930382) baseStart_1930382 baseEnd_1930382 := by
    simpa [prefixWord, tailWord_1930382, baseEnd_1930382] using wordTrace_append hprefix tailTrace_1930382
  have hstable : (prefixWord ++ tailWord_1930382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930382).length < 2 ^ (prefixWord ++ tailWord_1930382).sum := by decide
  have hdescent : baseEnd_1930382 < baseStart_1930382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930392 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_1930392 : Nat := 118140960795 + 1930392 * 2 ^ 59
def prefixEnd_1930392 : Nat := 4983230072969 + 3 ^ 40 * 1930392 * 2
def baseEnd_1930392 : Nat := 330406315864705522040765

theorem tailTrace_1930392 : CollatzResearch.WordTrace tailWord_1930392 prefixEnd_1930392 330406315864705522040765 := by
  unfold tailWord_1930392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203590211263471775584715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46938120281684629034112953 35203590211263471775584715)
  ·
    refine ⟨52805385316895207663377073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35203590211263471775584715 52805385316895207663377073)
    ·
      refine ⟨39604038987671405747532805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52805385316895207663377073 39604038987671405747532805)
      ·
        refine ⟨7425757310188388577662401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39604038987671405747532805 7425757310188388577662401)
        ·
          refine ⟨5569317982641291433246801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425757310188388577662401 5569317982641291433246801)
          ·
            refine ⟨4176988486980968574935101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569317982641291433246801 4176988486980968574935101)
            ·
              refine ⟨1566370682617863215600663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4176988486980968574935101 1566370682617863215600663)
              ·
                refine ⟨2349556023926794823400995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566370682617863215600663 2349556023926794823400995)
                ·
                  refine ⟨3524334035890192235101493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349556023926794823400995 3524334035890192235101493)
                  ·
                    refine ⟨330406315864705522040765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524334035890192235101493 330406315864705522040765)
                    ·
                      rfl

theorem cell23_1930392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_1930392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930392 prefixEnd_1930392 := by exact prefixLift 1930392
  have htrace : WordTrace (prefixWord ++ tailWord_1930392) baseStart_1930392 baseEnd_1930392 := by
    simpa [prefixWord, tailWord_1930392, baseEnd_1930392] using wordTrace_append hprefix tailTrace_1930392
  have hstable : (prefixWord ++ tailWord_1930392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930392).length < 2 ^ (prefixWord ++ tailWord_1930392).sum := by decide
  have hdescent : baseEnd_1930392 < baseStart_1930392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930405 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_1930405 : Nat := 118140960795 + 1930405 * 2 ^ 59
def prefixEnd_1930405 : Nat := 4983230072969 + 3 ^ 40 * 1930405 * 2
def baseEnd_1930405 : Nat := 330408540947541671753245

theorem tailTrace_1930405 : CollatzResearch.WordTrace tailWord_1930405 prefixEnd_1930405 330408540947541671753245 := by
  unfold tailWord_1930405
  simp only [CollatzResearch.WordTrace]
  refine ⟨70407654571479846771392669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46938436380986564514261779 70407654571479846771392669)
  ·
    refine ⟨26402870464304942539272251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70407654571479846771392669 26402870464304942539272251)
    ·
      refine ⟨39604305696457413808908377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26402870464304942539272251 39604305696457413808908377)
      ·
        refine ⟨29703229272343060356681283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39604305696457413808908377 29703229272343060356681283)
        ·
          refine ⟨44554843908514590535021925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29703229272343060356681283 44554843908514590535021925)
          ·
            refine ⟨8354033232846485725316611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44554843908514590535021925 8354033232846485725316611)
            ·
              refine ⟨12531049849269728587974917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354033232846485725316611 12531049849269728587974917)
              ·
                refine ⟨2349571846738074110245297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12531049849269728587974917 2349571846738074110245297)
                ·
                  refine ⟨1762178885053555582683973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349571846738074110245297 1762178885053555582683973)
                  ·
                    refine ⟨330408540947541671753245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762178885053555582683973 330408540947541671753245)
                    ·
                      rfl

theorem cell23_1930405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_1930405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930405 prefixEnd_1930405 := by exact prefixLift 1930405
  have htrace : WordTrace (prefixWord ++ tailWord_1930405) baseStart_1930405 baseEnd_1930405 := by
    simpa [prefixWord, tailWord_1930405, baseEnd_1930405] using wordTrace_append hprefix tailTrace_1930405
  have hstable : (prefixWord ++ tailWord_1930405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930405).length < 2 ^ (prefixWord ++ tailWord_1930405).sum := by decide
  have hdescent : baseEnd_1930405 < baseStart_1930405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930418 : List Nat := [3, 2, 1, 1, 1, 4, 3, 8]
def baseStart_1930418 : Nat := 118140960795 + 1930418 * 2 ^ 59
def prefixEnd_1930418 : Nat := 4983230072969 + 3 ^ 40 * 1930418 * 2
def baseEnd_1930418 : Nat := 36712307336708646829525

theorem tailTrace_1930418 : CollatzResearch.WordTrace tailWord_1930418 prefixEnd_1930418 36712307336708646829525 := by
  unfold tailWord_1930418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602032180108187497903977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46938752480288499994410605 17602032180108187497903977)
  ·
    refine ⟨13201524135081140623427983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17602032180108187497903977 13201524135081140623427983)
    ·
      refine ⟨19802286202621710935141975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201524135081140623427983 19802286202621710935141975)
      ·
        refine ⟨29703429303932566402712963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802286202621710935141975 29703429303932566402712963)
        ·
          refine ⟨44555143955898849604069445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29703429303932566402712963 44555143955898849604069445)
          ·
            refine ⟨8354089491731034300763021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44555143955898849604069445 8354089491731034300763021)
            ·
              refine ⟨3132783559399137862786133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8354089491731034300763021 3132783559399137862786133)
              ·
                refine ⟨36712307336708646829525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3132783559399137862786133 36712307336708646829525)
                ·
                  rfl

theorem cell23_1930418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_1930418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930418 prefixEnd_1930418 := by exact prefixLift 1930418
  have htrace : WordTrace (prefixWord ++ tailWord_1930418) baseStart_1930418 baseEnd_1930418 := by
    simpa [prefixWord, tailWord_1930418, baseEnd_1930418] using wordTrace_append hprefix tailTrace_1930418
  have hstable : (prefixWord ++ tailWord_1930418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930418).length < 2 ^ (prefixWord ++ tailWord_1930418).sum := by decide
  have hdescent : baseEnd_1930418 < baseStart_1930418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930425 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1930425 : Nat := 118140960795 + 1930425 * 2 ^ 59
def prefixEnd_1930425 : Nat := 4983230072969 + 3 ^ 40 * 1930425 * 2
def baseEnd_1930425 : Nat := 991235892455714937009643

theorem tailTrace_1930425 : CollatzResearch.WordTrace tailWord_1930425 prefixEnd_1930425 991235892455714937009643 := by
  unfold tailWord_1930425
  simp only [CollatzResearch.WordTrace]
  refine ⟨70408384031407390187120729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46938922687604926791413819 70408384031407390187120729)
  ·
    refine ⟨52806288023555542640340547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70408384031407390187120729 52806288023555542640340547)
    ·
      refine ⟨79209432035333313960510821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52806288023555542640340547 79209432035333313960510821)
      ·
        refine ⟨14851768506624996367595779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79209432035333313960510821 14851768506624996367595779)
        ·
          refine ⟨22277652759937494551393669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851768506624996367595779 22277652759937494551393669)
          ·
            refine ⟨4177059892488280228386313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22277652759937494551393669 4177059892488280228386313)
            ·
              refine ⟨3132794919366210171289735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177059892488280228386313 3132794919366210171289735)
              ·
                refine ⟨4699192379049315256934603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132794919366210171289735 4699192379049315256934603)
                ·
                  refine ⟨7048788568573972885401905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699192379049315256934603 7048788568573972885401905)
                  ·
                    refine ⟨5286591426430479664051429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7048788568573972885401905 5286591426430479664051429)
                    ·
                      refine ⟨991235892455714937009643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5286591426430479664051429 991235892455714937009643)
                      ·
                        rfl

theorem cell23_1930425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1930425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930425 prefixEnd_1930425 := by exact prefixLift 1930425
  have htrace : WordTrace (prefixWord ++ tailWord_1930425) baseStart_1930425 baseEnd_1930425 := by
    simpa [prefixWord, tailWord_1930425, baseEnd_1930425] using wordTrace_append hprefix tailTrace_1930425
  have hstable : (prefixWord ++ tailWord_1930425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930425).length < 2 ^ (prefixWord ++ tailWord_1930425).sum := by decide
  have hdescent : baseEnd_1930425 < baseStart_1930425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930446 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_1930446 : Nat := 118140960795 + 1930446 * 2 ^ 59
def prefixEnd_1930446 : Nat := 4983230072969 + 3 ^ 40 * 1930446 * 2
def baseEnd_1930446 : Nat := 991246675549459354847047

theorem tailTrace_1930446 : CollatzResearch.WordTrace tailWord_1930446 prefixEnd_1930446 991246675549459354847047 := by
  unfold tailWord_1930446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801143745541413846704399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46939433309554207182423461 8801143745541413846704399)
  ·
    refine ⟨13201715618312120770056599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801143745541413846704399 13201715618312120770056599)
    ·
      refine ⟨19802573427468181155084899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201715618312120770056599 19802573427468181155084899)
      ·
        refine ⟨29703860141202271732627349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802573427468181155084899 29703860141202271732627349)
        ·
          refine ⟨1392368444118856487466907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29703860141202271732627349 1392368444118856487466907)
          ·
            refine ⟨2088552666178284731200361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392368444118856487466907 2088552666178284731200361)
            ·
              refine ⟨1566414499633713548400271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2088552666178284731200361 1566414499633713548400271)
              ·
                refine ⟨2349621749450570322600407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566414499633713548400271 2349621749450570322600407)
                ·
                  refine ⟨3524432624175855483900611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349621749450570322600407 3524432624175855483900611)
                  ·
                    refine ⟨5286648936263783225850917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524432624175855483900611 5286648936263783225850917)
                    ·
                      refine ⟨991246675549459354847047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5286648936263783225850917 991246675549459354847047)
                      ·
                        rfl

theorem cell23_1930446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_1930446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930446 prefixEnd_1930446 := by exact prefixLift 1930446
  have htrace : WordTrace (prefixWord ++ tailWord_1930446) baseStart_1930446 baseEnd_1930446 := by
    simpa [prefixWord, tailWord_1930446, baseEnd_1930446] using wordTrace_append hprefix tailTrace_1930446
  have hstable : (prefixWord ++ tailWord_1930446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930446).length < 2 ^ (prefixWord ++ tailWord_1930446).sum := by decide
  have hdescent : baseEnd_1930446 < baseStart_1930446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930468 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1930468 : Nat := 118140960795 + 1930468 * 2 ^ 59
def prefixEnd_1930468 : Nat := 4983230072969 + 3 ^ 40 * 1930468 * 2
def baseEnd_1930468 : Nat := 991257972123858268771945

theorem tailTrace_1930468 : CollatzResearch.WordTrace tailWord_1930468 prefixEnd_1930468 991257972123858268771945 := by
  unfold tailWord_1930468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35204976185125804265468029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46939968246834405687290705 35204976185125804265468029)
  ·
    refine ⟨13201866069422176599550511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35204976185125804265468029 13201866069422176599550511)
    ·
      refine ⟨19802799104133264899325767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201866069422176599550511 19802799104133264899325767)
      ·
        refine ⟨29704198656199897348988651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802799104133264899325767 29704198656199897348988651)
        ·
          refine ⟨44556297984299846023482977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29704198656199897348988651 44556297984299846023482977)
          ·
            refine ⟨33417223488224884517612233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44556297984299846023482977 33417223488224884517612233)
            ·
              refine ⟨25062917616168663388209175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33417223488224884517612233 25062917616168663388209175)
              ·
                refine ⟨37594376424252995082313763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062917616168663388209175 37594376424252995082313763)
                ·
                  refine ⟨56391564636379492623470645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37594376424252995082313763 56391564636379492623470645)
                  ·
                    refine ⟨5286709184660577433450373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56391564636379492623470645 5286709184660577433450373)
                    ·
                      refine ⟨991257972123858268771945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5286709184660577433450373 991257972123858268771945)
                      ·
                        rfl

theorem cell23_1930468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1930468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930468 prefixEnd_1930468 := by exact prefixLift 1930468
  have htrace : WordTrace (prefixWord ++ tailWord_1930468) baseStart_1930468 baseEnd_1930468 := by
    simpa [prefixWord, tailWord_1930468, baseEnd_1930468] using wordTrace_append hprefix tailTrace_1930468
  have hstable : (prefixWord ++ tailWord_1930468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930468).length < 2 ^ (prefixWord ++ tailWord_1930468).sum := by decide
  have hdescent : baseEnd_1930468 < baseStart_1930468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930479 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 3, 3]
def baseStart_1930479 : Nat := 118140960795 + 1930479 * 2 ^ 59
def prefixEnd_1930479 : Nat := 4983230072969 + 3 ^ 40 * 1930479 * 2
def baseEnd_1930479 : Nat := 991263620411057725734395

theorem tailTrace_1930479 : CollatzResearch.WordTrace tailWord_1930479 prefixEnd_1930479 991263620411057725734395 := by
  unfold tailWord_1930479
  simp only [CollatzResearch.WordTrace]
  refine ⟨70410353573211757409586491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46940235715474504939724327 70410353573211757409586491)
  ·
    refine ⟨105615530359817636114379737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70410353573211757409586491 105615530359817636114379737)
    ·
      refine ⟨79211647769863227085784803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105615530359817636114379737 79211647769863227085784803)
      ·
        refine ⟨118817471654794840628677205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79211647769863227085784803 118817471654794840628677205)
        ·
          refine ⟨1392392245954627038617311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 118817471654794840628677205 1392392245954627038617311)
          ·
            refine ⟨2088588368931940557925967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392392245954627038617311 2088588368931940557925967)
            ·
              refine ⟨3132882553397910836888951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088588368931940557925967 3132882553397910836888951)
              ·
                refine ⟨4699323830096866255333427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132882553397910836888951 4699323830096866255333427)
                ·
                  refine ⟨7048985745145299383000141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699323830096866255333427 7048985745145299383000141)
                  ·
                    refine ⟨2643369654429487268625053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7048985745145299383000141 2643369654429487268625053)
                    ·
                      refine ⟨991263620411057725734395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2643369654429487268625053 991263620411057725734395)
                      ·
                        rfl

theorem cell23_1930479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 3, 3].length) (baseStart_1930479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930479 prefixEnd_1930479 := by exact prefixLift 1930479
  have htrace : WordTrace (prefixWord ++ tailWord_1930479) baseStart_1930479 baseEnd_1930479 := by
    simpa [prefixWord, tailWord_1930479, baseEnd_1930479] using wordTrace_append hprefix tailTrace_1930479
  have hstable : (prefixWord ++ tailWord_1930479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930479).length < 2 ^ (prefixWord ++ tailWord_1930479).sum := by decide
  have hdescent : baseEnd_1930479 < baseStart_1930479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930519 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1930519 : Nat := 118140960795 + 1930519 * 2 ^ 59
def prefixEnd_1930519 : Nat := 4983230072969 + 3 ^ 40 * 1930519 * 2
def baseEnd_1930519 : Nat := 991284159637237569234211

theorem tailTrace_1930519 : CollatzResearch.WordTrace tailWord_1930519 prefixEnd_1930519 991284159637237569234211 := by
  unfold tailWord_1930519
  simp only [CollatzResearch.WordTrace]
  refine ⟨70411812493066844241042611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46941208328711229494028407 70411812493066844241042611)
  ·
    refine ⟨105617718739600266361563917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70411812493066844241042611 105617718739600266361563917)
    ·
      refine ⟨39606644527350099885586469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105617718739600266361563917 39606644527350099885586469)
      ·
        refine ⟨7426245848878143728547463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39606644527350099885586469 7426245848878143728547463)
        ·
          refine ⟨11139368773317215592821195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426245848878143728547463 11139368773317215592821195)
          ·
            refine ⟨16709053159975823389231793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139368773317215592821195 16709053159975823389231793)
            ·
              refine ⟨12531789869981867541923845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709053159975823389231793 12531789869981867541923845)
              ·
                refine ⟨2349710600621600164110721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12531789869981867541923845 2349710600621600164110721)
                ·
                  refine ⟨1762282950466200123083041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349710600621600164110721 1762282950466200123083041)
                  ·
                    refine ⟨1321712212849650092312281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1762282950466200123083041 1321712212849650092312281)
                    ·
                      refine ⟨991284159637237569234211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321712212849650092312281 991284159637237569234211)
                      ·
                        rfl

theorem cell23_1930519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1930519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930519 prefixEnd_1930519 := by exact prefixLift 1930519
  have htrace : WordTrace (prefixWord ++ tailWord_1930519) baseStart_1930519 baseEnd_1930519 := by
    simpa [prefixWord, tailWord_1930519, baseEnd_1930519] using wordTrace_append hprefix tailTrace_1930519
  have hstable : (prefixWord ++ tailWord_1930519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930519).length < 2 ^ (prefixWord ++ tailWord_1930519).sum := by decide
  have hdescent : baseEnd_1930519 < baseStart_1930519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930536 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1930536 : Nat := 118140960795 + 1930536 * 2 ^ 59
def prefixEnd_1930536 : Nat := 4983230072969 + 3 ^ 40 * 1930536 * 2
def baseEnd_1930536 : Nat := 991292888808364002721633

theorem tailTrace_1930536 : CollatzResearch.WordTrace tailWord_1930536 prefixEnd_1930536 991292888808364002721633 := by
  unfold tailWord_1930536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35206216267002628072205731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46941621689336837429607641 35206216267002628072205731)
  ·
    refine ⟨52809324400503942108308597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35206216267002628072205731 52809324400503942108308597)
    ·
      refine ⟨4950874162547244572653931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52809324400503942108308597 4950874162547244572653931)
      ·
        refine ⟨7426311243820866858980897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950874162547244572653931 7426311243820866858980897)
        ·
          refine ⟨5569733432865650144235673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7426311243820866858980897 5569733432865650144235673)
          ·
            refine ⟨4177300074649237608176755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569733432865650144235673 4177300074649237608176755)
            ·
              refine ⟨6265950111973856412265133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177300074649237608176755 6265950111973856412265133)
              ·
                refine ⟨2349731291990196154599425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6265950111973856412265133 2349731291990196154599425)
                ·
                  refine ⟨1762298468992647115949569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349731291990196154599425 1762298468992647115949569)
                  ·
                    refine ⟨1321723851744485336962177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1762298468992647115949569 1321723851744485336962177)
                    ·
                      refine ⟨991292888808364002721633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321723851744485336962177 991292888808364002721633)
                      ·
                        rfl

theorem cell23_1930536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1930536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930536 prefixEnd_1930536 := by exact prefixLift 1930536
  have htrace : WordTrace (prefixWord ++ tailWord_1930536) baseStart_1930536 baseEnd_1930536 := by
    simpa [prefixWord, tailWord_1930536, baseEnd_1930536] using wordTrace_append hprefix tailTrace_1930536
  have hstable : (prefixWord ++ tailWord_1930536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930536).length < 2 ^ (prefixWord ++ tailWord_1930536).sum := by decide
  have hdescent : baseEnd_1930536 < baseStart_1930536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930592 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2]
def baseStart_1930592 : Nat := 118140960795 + 1930592 * 2 ^ 59
def prefixEnd_1930592 : Nat := 4983230072969 + 3 ^ 40 * 1930592 * 2
def baseEnd_1930592 : Nat := 991321643725015783621375

theorem tailTrace_1930592 : CollatzResearch.WordTrace tailWord_1930592 prefixEnd_1930592 991321643725015783621375 := by
  unfold tailWord_1930592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207237510901188854225015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46942983347868251805633353 35207237510901188854225015)
  ·
    refine ⟨52810856266351783281337523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35207237510901188854225015 52810856266351783281337523)
    ·
      refine ⟨79216284399527674922006285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52810856266351783281337523 79216284399527674922006285)
      ·
        refine ⟨29706106649822878095752357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79216284399527674922006285 29706106649822878095752357)
        ·
          refine ⟨5569894996841789642953567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29706106649822878095752357 5569894996841789642953567)
          ·
            refine ⟨8354842495262684464430351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569894996841789642953567 8354842495262684464430351)
            ·
              refine ⟨12532263742894026696645527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354842495262684464430351 12532263742894026696645527)
              ·
                refine ⟨18798395614341040044968291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532263742894026696645527 18798395614341040044968291)
                ·
                  refine ⟨28197593421511560067452437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798395614341040044968291 28197593421511560067452437)
                  ·
                    refine ⟨1321762191633354378161833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28197593421511560067452437 1321762191633354378161833)
                    ·
                      refine ⟨991321643725015783621375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321762191633354378161833 991321643725015783621375)
                      ·
                        rfl

theorem cell23_1930592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_1930592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930592 prefixEnd_1930592 := by exact prefixLift 1930592
  have htrace : WordTrace (prefixWord ++ tailWord_1930592) baseStart_1930592 baseEnd_1930592 := by
    simpa [prefixWord, tailWord_1930592, baseEnd_1930592] using wordTrace_append hprefix tailTrace_1930592
  have hstable : (prefixWord ++ tailWord_1930592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930592).length < 2 ^ (prefixWord ++ tailWord_1930592).sum := by decide
  have hdescent : baseEnd_1930592 < baseStart_1930592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930606 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1930606 : Nat := 118140960795 + 1930606 * 2 ^ 59
def prefixEnd_1930606 : Nat := 4983230072969 + 3 ^ 40 * 1930606 * 2
def baseEnd_1930606 : Nat := 330442944151392909615437

theorem tailTrace_1930606 : CollatzResearch.WordTrace tailWord_1930606 prefixEnd_1930606 330442944151392909615437 := by
  unfold tailWord_1930606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801873205468957262432459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46943323762501105399639781 8801873205468957262432459)
  ·
    refine ⟨13202809808203435893648689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801873205468957262432459 13202809808203435893648689)
    ·
      refine ⟨9902107356152576920236517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13202809808203435893648689 9902107356152576920236517)
      ·
        refine ⟨1856645129278608172544347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9902107356152576920236517 1856645129278608172544347)
        ·
          refine ⟨2784967693917912258816521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856645129278608172544347 2784967693917912258816521)
          ·
            refine ⟨2088725770438434194112391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2784967693917912258816521 2088725770438434194112391)
            ·
              refine ⟨3133088655657651291168587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088725770438434194112391 3133088655657651291168587)
              ·
                refine ⟨4699632983486476936752881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133088655657651291168587 4699632983486476936752881)
                ·
                  refine ⟨3524724737614857702564661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4699632983486476936752881 3524724737614857702564661)
                  ·
                    refine ⟨330442944151392909615437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524724737614857702564661 330442944151392909615437)
                    ·
                      rfl

theorem cell23_1930606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1930606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930606 prefixEnd_1930606 := by exact prefixLift 1930606
  have htrace : WordTrace (prefixWord ++ tailWord_1930606) baseStart_1930606 baseEnd_1930606 := by
    simpa [prefixWord, tailWord_1930606, baseEnd_1930606] using wordTrace_append hprefix tailTrace_1930606
  have hstable : (prefixWord ++ tailWord_1930606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930606).length < 2 ^ (prefixWord ++ tailWord_1930606).sum := by decide
  have hdescent : baseEnd_1930606 < baseStart_1930606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930619 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 1, 4]
def baseStart_1930619 : Nat := 118140960795 + 1930619 * 2 ^ 59
def prefixEnd_1930619 : Nat := 4983230072969 + 3 ^ 40 * 1930619 * 2
def baseEnd_1930619 : Nat := 330445169234229059327917

theorem tailTrace_1930619 : CollatzResearch.WordTrace tailWord_1930619 prefixEnd_1930619 330445169234229059327917 := by
  unfold tailWord_1930619
  simp only [CollatzResearch.WordTrace]
  refine ⟨70415459792704561319682911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46943639861803040879788607 70415459792704561319682911)
  ·
    refine ⟨105623189689056841979524367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70415459792704561319682911 105623189689056841979524367)
    ·
      refine ⟨158434784533585262969286551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105623189689056841979524367 158434784533585262969286551)
      ·
        refine ⟨237652176800377894453929827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158434784533585262969286551 237652176800377894453929827)
        ·
          refine ⟨356478265200566841680894741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237652176800377894453929827 356478265200566841680894741)
          ·
            refine ⟨16709918681276570703791941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356478265200566841680894741 16709918681276570703791941)
            ·
              refine ⟨3133109752739357006960989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16709918681276570703791941 3133109752739357006960989)
              ·
                refine ⟨1174916157277258877610371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133109752739357006960989 1174916157277258877610371)
                ·
                  refine ⟨1762374235915888316415557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174916157277258877610371 1762374235915888316415557)
                  ·
                    refine ⟨330445169234229059327917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762374235915888316415557 330445169234229059327917)
                    ·
                      rfl

theorem cell23_1930619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 4].length) (baseStart_1930619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930619 prefixEnd_1930619 := by exact prefixLift 1930619
  have htrace : WordTrace (prefixWord ++ tailWord_1930619) baseStart_1930619 baseEnd_1930619 := by
    simpa [prefixWord, tailWord_1930619, baseEnd_1930619] using wordTrace_append hprefix tailTrace_1930619
  have hstable : (prefixWord ++ tailWord_1930619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930619).length < 2 ^ (prefixWord ++ tailWord_1930619).sum := by decide
  have hdescent : baseEnd_1930619 < baseStart_1930619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930626 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1930626 : Nat := 118140960795 + 1930626 * 2 ^ 59
def prefixEnd_1930626 : Nat := 4983230072969 + 3 ^ 40 * 1930626 * 2
def baseEnd_1930626 : Nat := 991339102067268650596219

theorem tailTrace_1930626 : CollatzResearch.WordTrace tailWord_1930626 prefixEnd_1930626 991339102067268650596219 := by
  unfold tailWord_1930626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603928775919800378796933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46943810069119467676791821 17603928775919800378796933)
  ·
    refine ⟨3300736645484962571024425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17603928775919800378796933 3300736645484962571024425)
    ·
      refine ⟨2475552484113721928268319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3300736645484962571024425 2475552484113721928268319)
      ·
        refine ⟨3713328726170582892402479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475552484113721928268319 3713328726170582892402479)
        ·
          refine ⟨5569993089255874338603719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713328726170582892402479 5569993089255874338603719)
          ·
            refine ⟨8354989633883811507905579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569993089255874338603719 8354989633883811507905579)
            ·
              refine ⟨12532484450825717261858369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354989633883811507905579 12532484450825717261858369)
              ·
                refine ⟨9399363338119287946393777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12532484450825717261858369 9399363338119287946393777)
                ·
                  refine ⟨7049522503589465959795333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9399363338119287946393777 7049522503589465959795333)
                  ·
                    refine ⟨1321785469423024867461625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049522503589465959795333 1321785469423024867461625)
                    ·
                      refine ⟨991339102067268650596219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321785469423024867461625 991339102067268650596219)
                      ·
                        rfl

theorem cell23_1930626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1930626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930626 prefixEnd_1930626 := by exact prefixLift 1930626
  have htrace : WordTrace (prefixWord ++ tailWord_1930626) baseStart_1930626 baseEnd_1930626 := by
    simpa [prefixWord, tailWord_1930626, baseEnd_1930626] using wordTrace_append hprefix tailTrace_1930626
  have hstable : (prefixWord ++ tailWord_1930626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930626).length < 2 ^ (prefixWord ++ tailWord_1930626).sum := by decide
  have hdescent : baseEnd_1930626 < baseStart_1930626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930632 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 6]
def baseStart_1930632 : Nat := 118140960795 + 1930632 * 2 ^ 59
def prefixEnd_1930632 : Nat := 4983230072969 + 3 ^ 40 * 1930632 * 2
def baseEnd_1930632 : Nat := 110149131439021736346799

theorem tailTrace_1930632 : CollatzResearch.WordTrace tailWord_1930632 prefixEnd_1930632 110149131439021736346799 := by
  unfold tailWord_1930632
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207966970828732269953075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46943955961104976359937433 35207966970828732269953075)
  ·
    refine ⟨52811950456243098404929613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35207966970828732269953075 52811950456243098404929613)
    ·
      refine ⟨19804481421091161901848605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52811950456243098404929613 19804481421091161901848605)
      ·
        refine ⟨7426680532909185713193227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19804481421091161901848605 7426680532909185713193227)
        ·
          refine ⟨11140020799363778569789841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426680532909185713193227 11140020799363778569789841)
          ·
            refine ⟨8355015599522833927342381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11140020799363778569789841 8355015599522833927342381)
            ·
              refine ⟨3133130849821062722753393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8355015599522833927342381 3133130849821062722753393)
              ·
                refine ⟨2349848137365797042065045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133130849821062722753393 2349848137365797042065045)
                ·
                  refine ⟨110149131439021736346799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2349848137365797042065045 110149131439021736346799)
                  ·
                    rfl

theorem cell23_1930632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_1930632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930632 prefixEnd_1930632 := by exact prefixLift 1930632
  have htrace : WordTrace (prefixWord ++ tailWord_1930632) baseStart_1930632 baseEnd_1930632 := by
    simpa [prefixWord, tailWord_1930632, baseEnd_1930632] using wordTrace_append hprefix tailTrace_1930632
  have hstable : (prefixWord ++ tailWord_1930632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930632).length < 2 ^ (prefixWord ++ tailWord_1930632).sum := by decide
  have hdescent : baseEnd_1930632 < baseStart_1930632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930645 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1930645 : Nat := 118140960795 + 1930645 * 2 ^ 59
def prefixEnd_1930645 : Nat := 4983230072969 + 3 ^ 40 * 1930645 * 2
def baseEnd_1930645 : Nat := 330449619399901358752877

theorem tailTrace_1930645 : CollatzResearch.WordTrace tailWord_1930645 prefixEnd_1930645 330449619399901358752877 := by
  unfold tailWord_1930645
  simp only [CollatzResearch.WordTrace]
  refine ⟨70416408090610367760129389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46944272060406911840086259 70416408090610367760129389)
  ·
    refine ⟨26406153033978887910048521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70416408090610367760129389 26406153033978887910048521)
    ·
      refine ⟨19804614775484165932536391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26406153033978887910048521 19804614775484165932536391)
      ·
        refine ⟨29706922163226248898804587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19804614775484165932536391 29706922163226248898804587)
        ·
          refine ⟨44560383244839373348206881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29706922163226248898804587 44560383244839373348206881)
          ·
            refine ⟨33420287433629530011155161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44560383244839373348206881 33420287433629530011155161)
            ·
              refine ⟨25065215575222147508366371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33420287433629530011155161 25065215575222147508366371)
              ·
                refine ⟨37597823362833221262549557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25065215575222147508366371 37597823362833221262549557)
                ·
                  refine ⟨3524795940265614493364021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37597823362833221262549557 3524795940265614493364021)
                  ·
                    refine ⟨330449619399901358752877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524795940265614493364021 330449619399901358752877)
                    ·
                      rfl

theorem cell23_1930645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1930645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930645 prefixEnd_1930645 := by exact prefixLift 1930645
  have htrace : WordTrace (prefixWord ++ tailWord_1930645) baseStart_1930645 baseEnd_1930645 := by
    simpa [prefixWord, tailWord_1930645, baseEnd_1930645] using wordTrace_append hprefix tailTrace_1930645
  have hstable : (prefixWord ++ tailWord_1930645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930645).length < 2 ^ (prefixWord ++ tailWord_1930645).sum := by decide
  have hdescent : baseEnd_1930645 < baseStart_1930645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930675 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 6]
def baseStart_1930675 : Nat := 118140960795 + 1930675 * 2 ^ 59
def prefixEnd_1930675 : Nat := 4983230072969 + 3 ^ 40 * 1930675 * 2
def baseEnd_1930675 : Nat := 330454754206446319627831

theorem tailTrace_1930675 : CollatzResearch.WordTrace tailWord_1930675 prefixEnd_1930675 330454754206446319627831 := by
  unfold tailWord_1930675
  simp only [CollatzResearch.WordTrace]
  refine ⟨70417502280501682883721479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46945001520334455255814319 70417502280501682883721479)
  ·
    refine ⟨105626253420752524325582219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70417502280501682883721479 105626253420752524325582219)
    ·
      refine ⟨158439380131128786488373329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105626253420752524325582219 158439380131128786488373329)
      ·
        refine ⟨118829535098346589866279997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158439380131128786488373329 118829535098346589866279997)
        ·
          refine ⟨44561075661879971199854999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118829535098346589866279997 44561075661879971199854999)
          ·
            refine ⟨66841613492819956799782499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44561075661879971199854999 66841613492819956799782499)
            ·
              refine ⟨100262420239229935199673749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66841613492819956799782499 100262420239229935199673749)
              ·
                refine ⟨4699800948713903212484707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100262420239229935199673749 4699800948713903212484707)
                ·
                  refine ⟨7049701423070854818727061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699800948713903212484707 7049701423070854818727061)
                  ·
                    refine ⟨330454754206446319627831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7049701423070854818727061 330454754206446319627831)
                    ·
                      rfl

theorem cell23_1930675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_1930675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930675 prefixEnd_1930675 := by exact prefixLift 1930675
  have htrace : WordTrace (prefixWord ++ tailWord_1930675) baseStart_1930675 baseEnd_1930675 := by
    simpa [prefixWord, tailWord_1930675, baseEnd_1930675] using wordTrace_append hprefix tailTrace_1930675
  have hstable : (prefixWord ++ tailWord_1930675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930675).length < 2 ^ (prefixWord ++ tailWord_1930675).sum := by decide
  have hdescent : baseEnd_1930675 < baseStart_1930675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930695 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1930695 : Nat := 118140960795 + 1930695 * 2 ^ 59
def prefixEnd_1930695 : Nat := 4983230072969 + 3 ^ 40 * 1930695 * 2
def baseEnd_1930695 : Nat := 991374532232428880633401

theorem tailTrace_1930695 : CollatzResearch.WordTrace tailWord_1930695 prefixEnd_1930695 991374532232428880633401 := by
  unfold tailWord_1930695
  simp only [CollatzResearch.WordTrace]
  refine ⟨70418231740429226299449539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46945487826952817532966359 70418231740429226299449539)
  ·
    refine ⟨105627347610643839449174309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70418231740429226299449539 105627347610643839449174309)
    ·
      refine ⟨19805127676995719896720183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105627347610643839449174309 19805127676995719896720183)
      ·
        refine ⟨29707691515493579845080275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19805127676995719896720183 29707691515493579845080275)
        ·
          refine ⟨44561537273240369767620413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29707691515493579845080275 44561537273240369767620413)
          ·
            refine ⟨16710576477465138662857655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44561537273240369767620413 16710576477465138662857655)
            ·
              refine ⟨25065864716197707994286483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16710576477465138662857655 25065864716197707994286483)
              ·
                refine ⟨37598797074296561991429725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25065864716197707994286483 37598797074296561991429725)
                ·
                  refine ⟨14099548902861210746786147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37598797074296561991429725 14099548902861210746786147)
                  ·
                    refine ⟨21149323354291816120179221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14099548902861210746786147 21149323354291816120179221)
                    ·
                      refine ⟨991374532232428880633401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21149323354291816120179221 991374532232428880633401)
                      ·
                        rfl

theorem cell23_1930695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1930695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930695 prefixEnd_1930695 := by exact prefixLift 1930695
  have htrace : WordTrace (prefixWord ++ tailWord_1930695) baseStart_1930695 baseEnd_1930695 := by
    simpa [prefixWord, tailWord_1930695, baseEnd_1930695] using wordTrace_append hprefix tailTrace_1930695
  have hstable : (prefixWord ++ tailWord_1930695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930695).length < 2 ^ (prefixWord ++ tailWord_1930695).sum := by decide
  have hdescent : baseEnd_1930695 < baseStart_1930695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930702 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1930702 : Nat := 118140960795 + 1930702 * 2 ^ 59
def prefixEnd_1930702 : Nat := 4983230072969 + 3 ^ 40 * 1930702 * 2
def baseEnd_1930702 : Nat := 991378126597010353245869

theorem tailTrace_1930702 : CollatzResearch.WordTrace tailWord_1930702 prefixEnd_1930702 991378126597010353245869 := by
  unfold tailWord_1930702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802310881425483311869295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46945658034269244329969573 8802310881425483311869295)
  ·
    refine ⟨13203466322138224967803943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802310881425483311869295 13203466322138224967803943)
    ·
      refine ⟨19805199483207337451705915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203466322138224967803943 19805199483207337451705915)
      ·
        refine ⟨29707799224811006177558873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19805199483207337451705915 29707799224811006177558873)
        ·
          refine ⟨22280849418608254633169155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29707799224811006177558873 22280849418608254633169155)
          ·
            refine ⟨33421274127912381949753733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22280849418608254633169155 33421274127912381949753733)
            ·
              refine ⟨6266488898983571615578825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33421274127912381949753733 6266488898983571615578825)
              ·
                refine ⟨4699866674237678711684119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266488898983571615578825 4699866674237678711684119)
                ·
                  refine ⟨7049800011356518067526179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699866674237678711684119 7049800011356518067526179)
                  ·
                    refine ⟨10574700017034777101289269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049800011356518067526179 10574700017034777101289269)
                    ·
                      refine ⟨991378126597010353245869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10574700017034777101289269 991378126597010353245869)
                      ·
                        rfl

theorem cell23_1930702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1930702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930702 prefixEnd_1930702 := by exact prefixLift 1930702
  have htrace : WordTrace (prefixWord ++ tailWord_1930702) baseStart_1930702 baseEnd_1930702 := by
    simpa [prefixWord, tailWord_1930702, baseEnd_1930702] using wordTrace_append hprefix tailTrace_1930702
  have hstable : (prefixWord ++ tailWord_1930702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930702).length < 2 ^ (prefixWord ++ tailWord_1930702).sum := by decide
  have hdescent : baseEnd_1930702 < baseStart_1930702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930709 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1930709 : Nat := 118140960795 + 1930709 * 2 ^ 59
def prefixEnd_1930709 : Nat := 4983230072969 + 3 ^ 40 * 1930709 * 2
def baseEnd_1930709 : Nat := 330460573653863941952779

theorem tailTrace_1930709 : CollatzResearch.WordTrace tailWord_1930709 prefixEnd_1930709 330460573653863941952779 := by
  unfold tailWord_1930709
  simp only [CollatzResearch.WordTrace]
  refine ⟨70418742362378506690459181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46945828241585671126972787 70418742362378506690459181)
  ·
    refine ⟨26407028385891940008922193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70418742362378506690459181 26407028385891940008922193)
    ·
      refine ⟨19805271289418955006691645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26407028385891940008922193 19805271289418955006691645)
      ·
        refine ⟨7426976733532108127509367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19805271289418955006691645 7426976733532108127509367)
        ·
          refine ⟨11140465100298162191264051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426976733532108127509367 11140465100298162191264051)
          ·
            refine ⟨16710697650447243286896077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11140465100298162191264051 16710697650447243286896077)
            ·
              refine ⟨6266511618917716232586029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16710697650447243286896077 6266511618917716232586029)
              ·
                refine ⟨2349941857094143587219761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266511618917716232586029 2349941857094143587219761)
                ·
                  refine ⟨1762456392820607690414821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349941857094143587219761 1762456392820607690414821)
                  ·
                    refine ⟨330460573653863941952779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762456392820607690414821 330460573653863941952779)
                    ·
                      rfl

theorem cell23_1930709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1930709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930709 prefixEnd_1930709 := by exact prefixLift 1930709
  have htrace : WordTrace (prefixWord ++ tailWord_1930709) baseStart_1930709 baseEnd_1930709 := by
    simpa [prefixWord, tailWord_1930709, baseEnd_1930709] using wordTrace_append hprefix tailTrace_1930709
  have hstable : (prefixWord ++ tailWord_1930709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930709).length < 2 ^ (prefixWord ++ tailWord_1930709).sum := by decide
  have hdescent : baseEnd_1930709 < baseStart_1930709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930733 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1930733 : Nat := 118140960795 + 1930733 * 2 ^ 59
def prefixEnd_1930733 : Nat := 4983230072969 + 3 ^ 40 * 1930733 * 2
def baseEnd_1930733 : Nat := 991394044497299731958227

theorem tailTrace_1930733 : CollatzResearch.WordTrace tailWord_1930733 prefixEnd_1930733 991394044497299731958227 := by
  unfold tailWord_1930733
  simp only [CollatzResearch.WordTrace]
  refine ⟨70419617714291558789332853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46946411809527705859555235 70419617714291558789332853)
  ·
    refine ⟨6601839160714833636499955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70419617714291558789332853 6601839160714833636499955)
    ·
      refine ⟨9902758741072250454749933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601839160714833636499955 9902758741072250454749933)
      ·
        refine ⟨3713534527902093920531225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9902758741072250454749933 3713534527902093920531225)
        ·
          refine ⟨2785150895926570440398419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3713534527902093920531225 2785150895926570440398419)
          ·
            refine ⟨4177726343889855660597629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785150895926570440398419 4177726343889855660597629)
            ·
              refine ⟨1566647378958695872724111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4177726343889855660597629 1566647378958695872724111)
              ·
                refine ⟨2349971068438043809086167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566647378958695872724111 2349971068438043809086167)
                ·
                  refine ⟨3524956602657065713629251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349971068438043809086167 3524956602657065713629251)
                  ·
                    refine ⟨5287434903985598570443877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524956602657065713629251 5287434903985598570443877)
                    ·
                      refine ⟨991394044497299731958227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5287434903985598570443877 991394044497299731958227)
                      ·
                        rfl

theorem cell23_1930733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1930733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930733 prefixEnd_1930733 := by exact prefixLift 1930733
  have htrace : WordTrace (prefixWord ++ tailWord_1930733) baseStart_1930733 baseEnd_1930733 := by
    simpa [prefixWord, tailWord_1930733, baseEnd_1930733] using wordTrace_append hprefix tailTrace_1930733
  have hstable : (prefixWord ++ tailWord_1930733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930733).length < 2 ^ (prefixWord ++ tailWord_1930733).sum := by decide
  have hdescent : baseEnd_1930733 < baseStart_1930733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930736 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3]
def baseStart_1930736 : Nat := 118140960795 + 1930736 * 2 ^ 59
def prefixEnd_1930736 : Nat := 4983230072969 + 3 ^ 40 * 1930736 * 2
def baseEnd_1930736 : Nat := 991395584939263220220713

theorem tailTrace_1930736 : CollatzResearch.WordTrace tailWord_1930736 prefixEnd_1930736 991395584939263220220713 := by
  unfold tailWord_1930736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209863566640345150846031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46946484755520460201128041 35209863566640345150846031)
  ·
    refine ⟨52814795349960517726269047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35209863566640345150846031 52814795349960517726269047)
    ·
      refine ⟨79222193024940776589403571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52814795349960517726269047 79222193024940776589403571)
      ·
        refine ⟨118833289537411164884105357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79222193024940776589403571 118833289537411164884105357)
        ·
          refine ⟨44562483576529186831539509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118833289537411164884105357 44562483576529186831539509)
          ·
            refine ⟨4177732835299611265456829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44562483576529186831539509 4177732835299611265456829)
            ·
              refine ⟨1566649813237354224546311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4177732835299611265456829 1566649813237354224546311)
              ·
                refine ⟨2349974719856031336819467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566649813237354224546311 2349974719856031336819467)
                ·
                  refine ⟨3524962079784047005229201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349974719856031336819467 3524962079784047005229201)
                  ·
                    refine ⟨2643721559838035253921901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524962079784047005229201 2643721559838035253921901)
                    ·
                      refine ⟨991395584939263220220713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2643721559838035253921901 991395584939263220220713)
                      ·
                        rfl

theorem cell23_1930736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3].length) (baseStart_1930736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930736 prefixEnd_1930736 := by exact prefixLift 1930736
  have htrace : WordTrace (prefixWord ++ tailWord_1930736) baseStart_1930736 baseEnd_1930736 := by
    simpa [prefixWord, tailWord_1930736, baseEnd_1930736] using wordTrace_append hprefix tailTrace_1930736
  have hstable : (prefixWord ++ tailWord_1930736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930736).length < 2 ^ (prefixWord ++ tailWord_1930736).sum := by decide
  have hdescent : baseEnd_1930736 < baseStart_1930736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930756 : List Nat := [2, 3, 2, 3, 3, 1, 1, 8]
def baseStart_1930756 : Nat := 118140960795 + 1930756 * 2 ^ 59
def prefixEnd_1930756 : Nat := 4983230072969 + 3 ^ 40 * 1930756 * 2
def baseEnd_1930756 : Nat := 36718735353790857110023

theorem tailTrace_1930756 : CollatzResearch.WordTrace tailWord_1930756 prefixEnd_1930756 36718735353790857110023 := by
  unfold tailWord_1930756
  simp only [CollatzResearch.WordTrace]
  refine ⟨35210228296604116858710061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46946971062138822478280081 35210228296604116858710061)
  ·
    refine ⟨13203835611226543822016273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35210228296604116858710061 13203835611226543822016273)
    ·
      refine ⟨9902876708419907866512205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203835611226543822016273 9902876708419907866512205)
      ·
        refine ⟨3713578765657465449942077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9902876708419907866512205 3713578765657465449942077)
        ·
          refine ⟨1392592037121549543728279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3713578765657465449942077 1392592037121549543728279)
          ·
            refine ⟨2088888055682324315592419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392592037121549543728279 2088888055682324315592419)
            ·
              refine ⟨3133332083523486473388629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088888055682324315592419 3133332083523486473388629)
              ·
                refine ⟨36718735353790857110023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3133332083523486473388629 36718735353790857110023)
                ·
                  rfl

theorem cell23_1930756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 8].length) (baseStart_1930756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930756 prefixEnd_1930756 := by exact prefixLift 1930756
  have htrace : WordTrace (prefixWord ++ tailWord_1930756) baseStart_1930756 baseEnd_1930756 := by
    simpa [prefixWord, tailWord_1930756, baseEnd_1930756] using wordTrace_append hprefix tailTrace_1930756
  have hstable : (prefixWord ++ tailWord_1930756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930756).length < 2 ^ (prefixWord ++ tailWord_1930756).sum := by decide
  have hdescent : baseEnd_1930756 < baseStart_1930756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930766 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1930766 : Nat := 118140960795 + 1930766 * 2 ^ 59
def prefixEnd_1930766 : Nat := 4983230072969 + 3 ^ 40 * 1930766 * 2
def baseEnd_1930766 : Nat := 991410989358898102845575

theorem tailTrace_1930766 : CollatzResearch.WordTrace tailWord_1930766 prefixEnd_1930766 991410989358898102845575 := by
  unfold tailWord_1930766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802602665396500678160519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46947214215448003616856101 8802602665396500678160519)
  ·
    refine ⟨13203903998094751017240779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802602665396500678160519 13203903998094751017240779)
    ·
      refine ⟨19805855997142126525861169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203903998094751017240779 19805855997142126525861169)
      ·
        refine ⟨14854391997856594894395877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19805855997142126525861169 14854391997856594894395877)
        ·
          refine ⟨2785198499598111542699227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14854391997856594894395877 2785198499598111542699227)
          ·
            refine ⟨4177797749397167314048841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785198499598111542699227 4177797749397167314048841)
            ·
              refine ⟨3133348312047875485536631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177797749397167314048841 3133348312047875485536631)
              ·
                refine ⟨4700022468071813228304947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133348312047875485536631 4700022468071813228304947)
                ·
                  refine ⟨7050033702107719842457421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700022468071813228304947 7050033702107719842457421)
                  ·
                    refine ⟨2643762638290394940921533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7050033702107719842457421 2643762638290394940921533)
                    ·
                      refine ⟨991410989358898102845575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2643762638290394940921533 991410989358898102845575)
                      ·
                        rfl

theorem cell23_1930766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1930766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930766 prefixEnd_1930766 := by exact prefixLift 1930766
  have htrace : WordTrace (prefixWord ++ tailWord_1930766) baseStart_1930766 baseEnd_1930766 := by
    simpa [prefixWord, tailWord_1930766, baseEnd_1930766] using wordTrace_append hprefix tailTrace_1930766
  have hstable : (prefixWord ++ tailWord_1930766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930766).length < 2 ^ (prefixWord ++ tailWord_1930766).sum := by decide
  have hdescent : baseEnd_1930766 < baseStart_1930766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930823 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_1930823 : Nat := 118140960795 + 1930823 * 2 ^ 59
def prefixEnd_1930823 : Nat := 4983230072969 + 3 ^ 40 * 1930823 * 2
def baseEnd_1930823 : Nat := 991440257756204379832813

theorem tailTrace_1930823 : CollatzResearch.WordTrace tailWord_1930823 prefixEnd_1930823 991440257756204379832813 := by
  unfold tailWord_1930823
  simp only [CollatzResearch.WordTrace]
  refine ⟨70422900283965504160109123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46948600189310336106739415 70422900283965504160109123)
  ·
    refine ⟨105634350425948256240163685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70422900283965504160109123 105634350425948256240163685)
    ·
      refine ⟨19806440704865298045030691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105634350425948256240163685 19806440704865298045030691)
      ·
        refine ⟨29709661057297947067546037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19806440704865298045030691 29709661057297947067546037)
        ·
          refine ⟨2785280724121682537582441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29709661057297947067546037 2785280724121682537582441)
          ·
            refine ⟨2088960543091261903186831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785280724121682537582441 2088960543091261903186831)
            ·
              refine ⟨3133440814636892854780247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088960543091261903186831 3133440814636892854780247)
              ·
                refine ⟨4700161221955339282170371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133440814636892854780247 4700161221955339282170371)
                ·
                  refine ⟨7050241832933008923255557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700161221955339282170371 7050241832933008923255557)
                  ·
                    refine ⟨1321920343674939173110417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050241832933008923255557 1321920343674939173110417)
                    ·
                      refine ⟨991440257756204379832813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321920343674939173110417 991440257756204379832813)
                      ·
                        rfl

theorem cell23_1930823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_1930823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930823 prefixEnd_1930823 := by exact prefixLift 1930823
  have htrace : WordTrace (prefixWord ++ tailWord_1930823) baseStart_1930823 baseEnd_1930823 := by
    simpa [prefixWord, tailWord_1930823, baseEnd_1930823] using wordTrace_append hprefix tailTrace_1930823
  have hstable : (prefixWord ++ tailWord_1930823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930823).length < 2 ^ (prefixWord ++ tailWord_1930823).sum := by decide
  have hdescent : baseEnd_1930823 < baseStart_1930823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930842 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1930842 : Nat := 118140960795 + 1930842 * 2 ^ 59
def prefixEnd_1930842 : Nat := 4983230072969 + 3 ^ 40 * 1930842 * 2
def baseEnd_1930842 : Nat := 330483337962879935165075

theorem tailTrace_1930842 : CollatzResearch.WordTrace tailWord_1930842 prefixEnd_1930842 330483337962879935165075 := by
  unfold tailWord_1930842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605898317724167601262695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46949062180597780270033853 17605898317724167601262695)
  ·
    refine ⟨26408847476586251401894043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17605898317724167601262695 26408847476586251401894043)
    ·
      refine ⟨39613271214879377102841065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26408847476586251401894043 39613271214879377102841065)
      ·
        refine ⟨29709953411159532827130799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39613271214879377102841065 29709953411159532827130799)
        ·
          refine ⟨44564930116739299240696199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29709953411159532827130799 44564930116739299240696199)
          ·
            refine ⟨66847395175108948861044299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44564930116739299240696199 66847395175108948861044299)
            ·
              refine ⟨100271092762663423291566449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66847395175108948861044299 100271092762663423291566449)
              ·
                refine ⟨75203319571997567468674837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100271092762663423291566449 75203319571997567468674837)
                ·
                  refine ⟨3525155604937385975094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75203319571997567468674837 3525155604937385975094133)
                  ·
                    refine ⟨330483337962879935165075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3525155604937385975094133 330483337962879935165075)
                    ·
                      rfl

theorem cell23_1930842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1930842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930842 prefixEnd_1930842 := by exact prefixLift 1930842
  have htrace : WordTrace (prefixWord ++ tailWord_1930842) baseStart_1930842 baseEnd_1930842 := by
    simpa [prefixWord, tailWord_1930842, baseEnd_1930842] using wordTrace_append hprefix tailTrace_1930842
  have hstable : (prefixWord ++ tailWord_1930842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930842).length < 2 ^ (prefixWord ++ tailWord_1930842).sum := by decide
  have hdescent : baseEnd_1930842 < baseStart_1930842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930869 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1930869 : Nat := 118140960795 + 1930869 * 2 ^ 59
def prefixEnd_1930869 : Nat := 4983230072969 + 3 ^ 40 * 1930869 * 2
def baseEnd_1930869 : Nat := 991463877866311199857601

theorem tailTrace_1930869 : CollatzResearch.WordTrace tailWord_1930869 prefixEnd_1930869 991463877866311199857601 := by
  unfold tailWord_1930869
  simp only [CollatzResearch.WordTrace]
  refine ⟨70424578041798854016283661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46949718694532569344189107 70424578041798854016283661)
  ·
    refine ⟨26409216765674570256106373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70424578041798854016283661 26409216765674570256106373)
    ·
      refine ⟨4951728143563981923019945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26409216765674570256106373 4951728143563981923019945)
      ·
        refine ⟨3713796107672986442264959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4951728143563981923019945 3713796107672986442264959)
        ·
          refine ⟨5570694161509479663397439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713796107672986442264959 5570694161509479663397439)
          ·
            refine ⟨8356041242264219495096159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570694161509479663397439 8356041242264219495096159)
            ·
              refine ⟨12534061863396329242644239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356041242264219495096159 12534061863396329242644239)
              ·
                refine ⟨18801092795094493863966359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534061863396329242644239 18801092795094493863966359)
                ·
                  refine ⟨28201639192641740795949539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18801092795094493863966359 28201639192641740795949539)
                  ·
                    refine ⟨42302458788962611193924309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28201639192641740795949539 42302458788962611193924309)
                    ·
                      refine ⟨991463877866311199857601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42302458788962611193924309 991463877866311199857601)
                      ·
                        rfl

theorem cell23_1930869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1930869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930869 prefixEnd_1930869 := by exact prefixLift 1930869
  have htrace : WordTrace (prefixWord ++ tailWord_1930869) baseStart_1930869 baseEnd_1930869 := by
    simpa [prefixWord, tailWord_1930869, baseEnd_1930869] using wordTrace_append hprefix tailTrace_1930869
  have hstable : (prefixWord ++ tailWord_1930869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930869).length < 2 ^ (prefixWord ++ tailWord_1930869).sum := by decide
  have hdescent : baseEnd_1930869 < baseStart_1930869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930879 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 4, 2]
def baseStart_1930879 : Nat := 118140960795 + 1930879 * 2 ^ 59
def prefixEnd_1930879 : Nat := 4983230072969 + 3 ^ 40 * 1930879 * 2
def baseEnd_1930879 : Nat := 991469012672856160732555

theorem tailTrace_1930879 : CollatzResearch.WordTrace tailWord_1930879 prefixEnd_1930879 991469012672856160732555 := by
  unfold tailWord_1930879
  simp only [CollatzResearch.WordTrace]
  refine ⟨70424942771762625724147691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46949961847841750482765127 70424942771762625724147691)
  ·
    refine ⟨105637414157643938586221537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70424942771762625724147691 105637414157643938586221537)
    ·
      refine ⟨79228060618232953939666153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105637414157643938586221537 79228060618232953939666153)
      ·
        refine ⟨59421045463674715454749615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79228060618232953939666153 59421045463674715454749615)
        ·
          refine ⟨89131568195512073182124423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59421045463674715454749615 89131568195512073182124423)
          ·
            refine ⟨133697352293268109773186635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89131568195512073182124423 133697352293268109773186635)
            ·
              refine ⟨200546028439902164659779953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133697352293268109773186635 200546028439902164659779953)
              ·
                refine ⟨150409521329926623494834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200546028439902164659779953 150409521329926623494834965)
                ·
                  refine ⟨7050446312340310476320389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150409521329926623494834965 7050446312340310476320389)
                  ·
                    refine ⟨1321958683563808214310073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050446312340310476320389 1321958683563808214310073)
                    ·
                      refine ⟨991469012672856160732555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1321958683563808214310073 991469012672856160732555)
                      ·
                        rfl

theorem cell23_1930879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_1930879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930879 prefixEnd_1930879 := by exact prefixLift 1930879
  have htrace : WordTrace (prefixWord ++ tailWord_1930879) baseStart_1930879 baseEnd_1930879 := by
    simpa [prefixWord, tailWord_1930879, baseEnd_1930879] using wordTrace_append hprefix tailTrace_1930879
  have hstable : (prefixWord ++ tailWord_1930879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930879).length < 2 ^ (prefixWord ++ tailWord_1930879).sum := by decide
  have hdescent : baseEnd_1930879 < baseStart_1930879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930889 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_1930889 : Nat := 118140960795 + 1930889 * 2 ^ 59
def prefixEnd_1930889 : Nat := 4983230072969 + 3 ^ 40 * 1930889 * 2
def baseEnd_1930889 : Nat := 330491382493133707202503

theorem tailTrace_1930889 : CollatzResearch.WordTrace tailWord_1930889 prefixEnd_1930889 330491382493133707202503 := by
  unfold tailWord_1930889
  simp only [CollatzResearch.WordTrace]
  refine ⟨70425307501726397432011721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46950205001150931621341147 70425307501726397432011721)
  ·
    refine ⟨52818980626294798074008791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70425307501726397432011721 52818980626294798074008791)
    ·
      refine ⟨79228470939442197111013187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52818980626294798074008791 79228470939442197111013187)
      ·
        refine ⟨118842706409163295666519781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79228470939442197111013187 118842706409163295666519781)
        ·
          refine ⟨22283007451718117937472459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118842706409163295666519781 22283007451718117937472459)
          ·
            refine ⟨33424511177577176906208689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283007451718117937472459 33424511177577176906208689)
            ·
              refine ⟨25068383383182882679656517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33424511177577176906208689 25068383383182882679656517)
              ·
                refine ⟨4700321884346790502435597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25068383383182882679656517 4700321884346790502435597)
                ·
                  refine ⟨1762620706630046438413349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4700321884346790502435597 1762620706630046438413349)
                  ·
                    refine ⟨330491382493133707202503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762620706630046438413349 330491382493133707202503)
                    ·
                      rfl

theorem cell23_1930889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_1930889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930889 prefixEnd_1930889 := by exact prefixLift 1930889
  have htrace : WordTrace (prefixWord ++ tailWord_1930889) baseStart_1930889 baseEnd_1930889 := by
    simpa [prefixWord, tailWord_1930889, baseEnd_1930889] using wordTrace_append hprefix tailTrace_1930889
  have hstable : (prefixWord ++ tailWord_1930889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930889).length < 2 ^ (prefixWord ++ tailWord_1930889).sum := by decide
  have hdescent : baseEnd_1930889 < baseStart_1930889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930916 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1930916 : Nat := 118140960795 + 1930916 * 2 ^ 59
def prefixEnd_1930916 : Nat := 4983230072969 + 3 ^ 40 * 1930916 * 2
def baseEnd_1930916 : Nat := 991488011457072515969885

theorem tailTrace_1930916 : CollatzResearch.WordTrace tailWord_1930916 prefixEnd_1930916 991488011457072515969885 := by
  unfold tailWord_1930916
  simp only [CollatzResearch.WordTrace]
  refine ⟨35213146136314290521622301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46950861515085720695496401 35213146136314290521622301)
  ·
    refine ⟨13204929801117858945608363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35213146136314290521622301 13204929801117858945608363)
    ·
      refine ⟨19807394701676788418412545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13204929801117858945608363 19807394701676788418412545)
      ·
        refine ⟨14855546026257591313809409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19807394701676788418412545 14855546026257591313809409)
        ·
          refine ⟨11141659519693193485357057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14855546026257591313809409 11141659519693193485357057)
          ·
            refine ⟨8356244639769895114017793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11141659519693193485357057 8356244639769895114017793)
            ·
              refine ⟨6267183479827421335513345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356244639769895114017793 6267183479827421335513345)
              ·
                refine ⟨4700387609870566001635009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267183479827421335513345 4700387609870566001635009)
                ·
                  refine ⟨3525290707402924501226257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700387609870566001635009 3525290707402924501226257)
                  ·
                    refine ⟨2643968030552193375919693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525290707402924501226257 2643968030552193375919693)
                    ·
                      refine ⟨991488011457072515969885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2643968030552193375919693 991488011457072515969885)
                      ·
                        rfl

theorem cell23_1930916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1930916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930916 prefixEnd_1930916 := by exact prefixLift 1930916
  have htrace : WordTrace (prefixWord ++ tailWord_1930916) baseStart_1930916 baseEnd_1930916 := by
    simpa [prefixWord, tailWord_1930916, baseEnd_1930916] using wordTrace_append hprefix tailTrace_1930916
  have hstable : (prefixWord ++ tailWord_1930916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930916).length < 2 ^ (prefixWord ++ tailWord_1930916).sum := by decide
  have hdescent : baseEnd_1930916 < baseStart_1930916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930950 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1930950 : Nat := 118140960795 + 1930950 * 2 ^ 59
def prefixEnd_1930950 : Nat := 4983230072969 + 3 ^ 40 * 1930950 * 2
def baseEnd_1930950 : Nat := 991505469799325382944729

theorem tailTrace_1930950 : CollatzResearch.WordTrace tailWord_1930950 prefixEnd_1930950 991505469799325382944729 := by
  unfold tailWord_1930950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200860386078293901561947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46951688236336936566654869 2200860386078293901561947)
  ·
    refine ⟨3301290579117440852342921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2200860386078293901561947 3301290579117440852342921)
    ·
      refine ⟨2475967934338080639257191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301290579117440852342921 2475967934338080639257191)
      ·
        refine ⟨3713951901507120958885787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475967934338080639257191 3713951901507120958885787)
        ·
          refine ⟨5570927852260681438328681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713951901507120958885787 5570927852260681438328681)
          ·
            refine ⟨4178195889195511078746511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570927852260681438328681 4178195889195511078746511)
            ·
              refine ⟨6267293833793266618119767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178195889195511078746511 6267293833793266618119767)
              ·
                refine ⟨9400940750689899927179651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267293833793266618119767 9400940750689899927179651)
                ·
                  refine ⟨14101411126034849890769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400940750689899927179651 14101411126034849890769477)
                  ·
                    refine ⟨2644014586131534354519277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14101411126034849890769477 2644014586131534354519277)
                    ·
                      refine ⟨991505469799325382944729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2644014586131534354519277 991505469799325382944729)
                      ·
                        rfl

theorem cell23_1930950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1930950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930950 prefixEnd_1930950 := by exact prefixLift 1930950
  have htrace : WordTrace (prefixWord ++ tailWord_1930950) baseStart_1930950 baseEnd_1930950 := by
    simpa [prefixWord, tailWord_1930950, baseEnd_1930950] using wordTrace_append hprefix tailTrace_1930950
  have hstable : (prefixWord ++ tailWord_1930950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930950).length < 2 ^ (prefixWord ++ tailWord_1930950).sum := by decide
  have hdescent : baseEnd_1930950 < baseStart_1930950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930957 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1930957 : Nat := 118140960795 + 1930957 * 2 ^ 59
def prefixEnd_1930957 : Nat := 4983230072969 + 3 ^ 40 * 1930957 * 2
def baseEnd_1930957 : Nat := 330503021387968951852399

theorem tailTrace_1930957 : CollatzResearch.WordTrace tailWord_1930957 prefixEnd_1930957 330503021387968951852399 := by
  unfold tailWord_1930957
  simp only [CollatzResearch.WordTrace]
  refine ⟨70427787665480045045487125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46951858443653363363658083 70427787665480045045487125)
  ·
    refine ⟨3301302546819377111507209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70427787665480045045487125 3301302546819377111507209)
    ·
      refine ⟨2475976910114532833630407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301302546819377111507209 2475976910114532833630407)
      ·
        refine ⟨3713965365171799250445611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475976910114532833630407 3713965365171799250445611)
        ·
          refine ⟨5570948047757698875668417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713965365171799250445611 5570948047757698875668417)
          ·
            refine ⟨4178211035818274156751313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570948047757698875668417 4178211035818274156751313)
            ·
              refine ⟨3133658276863705617563485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178211035818274156751313 3133658276863705617563485)
              ·
                refine ⟨1175121853823889606586307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133658276863705617563485 1175121853823889606586307)
                ·
                  refine ⟨1762682780735834409879461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175121853823889606586307 1762682780735834409879461)
                  ·
                    refine ⟨330503021387968951852399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762682780735834409879461 330503021387968951852399)
                    ·
                      rfl

theorem cell23_1930957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1930957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1930957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1930957 prefixEnd_1930957 := by exact prefixLift 1930957
  have htrace : WordTrace (prefixWord ++ tailWord_1930957) baseStart_1930957 baseEnd_1930957 := by
    simpa [prefixWord, tailWord_1930957, baseEnd_1930957] using wordTrace_append hprefix tailTrace_1930957
  have hstable : (prefixWord ++ tailWord_1930957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930957).length < 2 ^ (prefixWord ++ tailWord_1930957).sum := by decide
  have hdescent : baseEnd_1930957 < baseStart_1930957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931026 : List Nat := [3, 2, 4, 1, 1, 1, 11]
def baseStart_1931026 : Nat := 118140960795 + 1931026 * 2 ^ 59
def prefixEnd_1931026 : Nat := 4983230072969 + 3 ^ 40 * 1931026 * 2
def baseEnd_1931026 : Nat := 12241290053445272661659

theorem tailTrace_1931026 : CollatzResearch.WordTrace tailWord_1931026 prefixEnd_1931026 12241290053445272661659 := by
  unfold tailWord_1931026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17607576075557517457437233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46953536201486713219832621 17607576075557517457437233)
  ·
    refine ⟨13205682056668138093077925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17607576075557517457437233 13205682056668138093077925)
    ·
      refine ⟨2476065385625275892452111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13205682056668138093077925 2476065385625275892452111)
      ·
        refine ⟨3714098078437913838678167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476065385625275892452111 3714098078437913838678167)
        ·
          refine ⟨5571147117656870758017251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714098078437913838678167 5571147117656870758017251)
          ·
            refine ⟨8356720676485306137025877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571147117656870758017251 8356720676485306137025877)
            ·
              refine ⟨12241290053445272661659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8356720676485306137025877 12241290053445272661659)
              ·
                rfl

theorem cell23_1931026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 11].length) (baseStart_1931026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931026 prefixEnd_1931026 := by exact prefixLift 1931026
  have htrace : WordTrace (prefixWord ++ tailWord_1931026) baseStart_1931026 baseEnd_1931026 := by
    simpa [prefixWord, tailWord_1931026, baseEnd_1931026] using wordTrace_append hprefix tailTrace_1931026
  have hstable : (prefixWord ++ tailWord_1931026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931026).length < 2 ^ (prefixWord ++ tailWord_1931026).sum := by decide
  have hdescent : baseEnd_1931026 < baseStart_1931026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931039 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 7]
def baseStart_1931039 : Nat := 118140960795 + 1931039 * 2 ^ 59
def prefixEnd_1931039 : Nat := 4983230072969 + 3 ^ 40 * 1931039 * 2
def baseEnd_1931039 : Nat := 330517056525858511577273

theorem tailTrace_1931039 : CollatzResearch.WordTrace tailWord_1931039 prefixEnd_1931039 330517056525858511577273 := by
  unfold tailWord_1931039
  simp only [CollatzResearch.WordTrace]
  refine ⟨70430778451182973049972171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46953852300788648699981447 70430778451182973049972171)
  ·
    refine ⟨105646167676774459574958257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70430778451182973049972171 105646167676774459574958257)
    ·
      refine ⟨79234625757580844681218693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105646167676774459574958257 79234625757580844681218693)
      ·
        refine ⟨14856492329546408377728505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79234625757580844681218693 14856492329546408377728505)
        ·
          refine ⟨11142369247159806283296379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856492329546408377728505 11142369247159806283296379)
          ·
            refine ⟨16713553870739709424944569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142369247159806283296379 16713553870739709424944569)
            ·
              refine ⟨12535165403054782068708427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16713553870739709424944569 12535165403054782068708427)
              ·
                refine ⟨18802748104582173103062641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535165403054782068708427 18802748104582173103062641)
                ·
                  refine ⟨14102061078436629827296981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18802748104582173103062641 14102061078436629827296981)
                  ·
                    refine ⟨330517056525858511577273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14102061078436629827296981 330517056525858511577273)
                    ·
                      rfl

theorem cell23_1931039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_1931039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931039 prefixEnd_1931039 := by exact prefixLift 1931039
  have htrace : WordTrace (prefixWord ++ tailWord_1931039) baseStart_1931039 baseEnd_1931039 := by
    simpa [prefixWord, tailWord_1931039, baseEnd_1931039] using wordTrace_append hprefix tailTrace_1931039
  have hstable : (prefixWord ++ tailWord_1931039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931039).length < 2 ^ (prefixWord ++ tailWord_1931039).sum := by decide
  have hdescent : baseEnd_1931039 < baseStart_1931039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931063 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_1931063 : Nat := 118140960795 + 1931063 * 2 ^ 59
def prefixEnd_1931063 : Nat := 4983230072969 + 3 ^ 40 * 1931063 * 2
def baseEnd_1931063 : Nat := 991563493113283440831709

theorem tailTrace_1931063 : CollatzResearch.WordTrace tailWord_1931063 prefixEnd_1931063 991563493113283440831709 := by
  unfold tailWord_1931063
  simp only [CollatzResearch.WordTrace]
  refine ⟨70431653803096025148845843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46954435868730683432563895 70431653803096025148845843)
  ·
    refine ⟨105647480704644037723268765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70431653803096025148845843 105647480704644037723268765)
    ·
      refine ⟨39617805264241514146225787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105647480704644037723268765 39617805264241514146225787)
      ·
        refine ⟨59426707896362271219338681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39617805264241514146225787 59426707896362271219338681)
        ·
          refine ⟨44570030922271703414504011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59426707896362271219338681 44570030922271703414504011)
          ·
            refine ⟨66855046383407555121756017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44570030922271703414504011 66855046383407555121756017)
            ·
              refine ⟨50141284787555666341317013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66855046383407555121756017 50141284787555666341317013)
              ·
                refine ⟨2350372724416671859749235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50141284787555666341317013 2350372724416671859749235)
                ·
                  refine ⟨3525559086625007789623853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350372724416671859749235 3525559086625007789623853)
                  ·
                    refine ⟨1322084657484377921108945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525559086625007789623853 1322084657484377921108945)
                    ·
                      refine ⟨991563493113283440831709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322084657484377921108945 991563493113283440831709)
                      ·
                        rfl

theorem cell23_1931063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_1931063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931063 prefixEnd_1931063 := by exact prefixLift 1931063
  have htrace : WordTrace (prefixWord ++ tailWord_1931063) baseStart_1931063 baseEnd_1931063 := by
    simpa [prefixWord, tailWord_1931063, baseEnd_1931063] using wordTrace_append hprefix tailTrace_1931063
  have hstable : (prefixWord ++ tailWord_1931063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931063).length < 2 ^ (prefixWord ++ tailWord_1931063).sum := by decide
  have hdescent : baseEnd_1931063 < baseStart_1931063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931116 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 7]
def baseStart_1931116 : Nat := 118140960795 + 1931116 * 2 ^ 59
def prefixEnd_1931116 : Nat := 4983230072969 + 3 ^ 40 * 1931116 * 2
def baseEnd_1931116 : Nat := 110176745287552414829885

theorem tailTrace_1931116 : CollatzResearch.WordTrace tailWord_1931116 prefixEnd_1931116 110176745287552414829885 := by
  unfold tailWord_1931116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216793435952007600262601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46955724581269343467016801 35216793435952007600262601)
  ·
    refine ⟨26412595076964005700196951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35216793435952007600262601 26412595076964005700196951)
    ·
      refine ⟨39618892615446008550295427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26412595076964005700196951 39618892615446008550295427)
      ·
        refine ⟨59428338923169012825443141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39618892615446008550295427 59428338923169012825443141)
        ·
          refine ⟨11142813548094189904770589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59428338923169012825443141 11142813548094189904770589)
          ·
            refine ⟨4178555080535321214288971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11142813548094189904770589 4178555080535321214288971)
            ·
              refine ⟨6267832620802981821433457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178555080535321214288971 6267832620802981821433457)
              ·
                refine ⟨4700874465602236366075093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267832620802981821433457 4700874465602236366075093)
                ·
                  refine ⟨110176745287552414829885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4700874465602236366075093 110176745287552414829885)
                  ·
                    rfl

theorem cell23_1931116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_1931116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931116 prefixEnd_1931116 := by exact prefixLift 1931116
  have htrace : WordTrace (prefixWord ++ tailWord_1931116) baseStart_1931116 baseEnd_1931116 := by
    simpa [prefixWord, tailWord_1931116, baseEnd_1931116] using wordTrace_append hprefix tailTrace_1931116
  have hstable : (prefixWord ++ tailWord_1931116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931116).length < 2 ^ (prefixWord ++ tailWord_1931116).sum := by decide
  have hdescent : baseEnd_1931116 < baseStart_1931116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931144 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1931144 : Nat := 118140960795 + 1931144 * 2 ^ 59
def prefixEnd_1931144 : Nat := 4983230072969 + 3 ^ 40 * 1931144 * 2
def baseEnd_1931144 : Nat := 991605085046297623918837

theorem tailTrace_1931144 : CollatzResearch.WordTrace tailWord_1931144 prefixEnd_1931144 991605085046297623918837 := by
  unfold tailWord_1931144
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217304057901287991272243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46956405410535050655029657 35217304057901287991272243)
  ·
    refine ⟨52825956086851931986908365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35217304057901287991272243 52825956086851931986908365)
    ·
      refine ⟨19809733532569474495090637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52825956086851931986908365 19809733532569474495090637)
      ·
        refine ⟨7428650074713552935658989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19809733532569474495090637 7428650074713552935658989)
        ·
          refine ⟨2785743778017582350872121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7428650074713552935658989 2785743778017582350872121)
          ·
            refine ⟨2089307833513186763154091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785743778017582350872121 2089307833513186763154091)
            ·
              refine ⟨3133961750269780144731137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089307833513186763154091 3133961750269780144731137)
              ·
                refine ⟨2350471312702335108548353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133961750269780144731137 2350471312702335108548353)
                ·
                  refine ⟨1762853484526751331411265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2350471312702335108548353 1762853484526751331411265)
                  ·
                    refine ⟨1322140113395063498558449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1762853484526751331411265 1322140113395063498558449)
                    ·
                      refine ⟨991605085046297623918837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322140113395063498558449 991605085046297623918837)
                      ·
                        rfl

theorem cell23_1931144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1931144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931144 prefixEnd_1931144 := by exact prefixLift 1931144
  have htrace : WordTrace (prefixWord ++ tailWord_1931144) baseStart_1931144 baseEnd_1931144 := by
    simpa [prefixWord, tailWord_1931144, baseEnd_1931144] using wordTrace_append hprefix tailTrace_1931144
  have hstable : (prefixWord ++ tailWord_1931144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931144).length < 2 ^ (prefixWord ++ tailWord_1931144).sum := by decide
  have hdescent : baseEnd_1931144 < baseStart_1931144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931150 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_1931150 : Nat := 118140960795 + 1931150 * 2 ^ 59
def prefixEnd_1931150 : Nat := 4983230072969 + 3 ^ 40 * 1931150 * 2
def baseEnd_1931150 : Nat := 110178685103358288938201

theorem tailTrace_1931150 : CollatzResearch.WordTrace tailWord_1931150 prefixEnd_1931150 110178685103358288938201 := by
  unfold tailWord_1931150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8804353369222604875907863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46956551302520559338175269 8804353369222604875907863)
  ·
    refine ⟨13206530053833907313861795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8804353369222604875907863 13206530053833907313861795)
    ·
      refine ⟨19809795080750860970792693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13206530053833907313861795 19809795080750860970792693)
      ·
        refine ⟨1857168288820393216011815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19809795080750860970792693 1857168288820393216011815)
        ·
          refine ⟨2785752433230589824017723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857168288820393216011815 2785752433230589824017723)
          ·
            refine ⟨4178628649845884736026585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785752433230589824017723 4178628649845884736026585)
            ·
              refine ⟨3133971487384413552019939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178628649845884736026585 3133971487384413552019939)
              ·
                refine ⟨4700957231076620328029909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133971487384413552019939 4700957231076620328029909)
                ·
                  refine ⟨110178685103358288938201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4700957231076620328029909 110178685103358288938201)
                  ·
                    rfl

theorem cell23_1931150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_1931150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931150 prefixEnd_1931150 := by exact prefixLift 1931150
  have htrace : WordTrace (prefixWord ++ tailWord_1931150) baseStart_1931150 baseEnd_1931150 := by
    simpa [prefixWord, tailWord_1931150, baseEnd_1931150] using wordTrace_append hprefix tailTrace_1931150
  have hstable : (prefixWord ++ tailWord_1931150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931150).length < 2 ^ (prefixWord ++ tailWord_1931150).sum := by decide
  have hdescent : baseEnd_1931150 < baseStart_1931150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931210 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1931210 : Nat := 118140960795 + 1931210 * 2 ^ 59
def prefixEnd_1931210 : Nat := 4983230072969 + 3 ^ 40 * 1931210 * 2
def baseEnd_1931210 : Nat := 330546324923164788564511

theorem tailTrace_1931210 : CollatzResearch.WordTrace tailWord_1931210 prefixEnd_1931210 330546324923164788564511 := by
  unfold tailWord_1931210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609253833390867313611771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46958010222375646169631389 17609253833390867313611771)
  ·
    refine ⟨26413880750086300970417657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17609253833390867313611771 26413880750086300970417657)
    ·
      refine ⟨19810410562564725727813243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26413880750086300970417657 19810410562564725727813243)
      ·
        refine ⟨29715615843847088591719865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19810410562564725727813243 29715615843847088591719865)
        ·
          refine ⟨22286711882885316443789899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29715615843847088591719865 22286711882885316443789899)
          ·
            refine ⟨33430067824327974665684849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22286711882885316443789899 33430067824327974665684849)
            ·
              refine ⟨25072550868245980999263637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33430067824327974665684849 25072550868245980999263637)
              ·
                refine ⟨1175275821949030359340483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25072550868245980999263637 1175275821949030359340483)
                ·
                  refine ⟨1762913732923545539010725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175275821949030359340483 1762913732923545539010725)
                  ·
                    refine ⟨330546324923164788564511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762913732923545539010725 330546324923164788564511)
                    ·
                      rfl

theorem cell23_1931210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1931210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931210 prefixEnd_1931210 := by exact prefixLift 1931210
  have htrace : WordTrace (prefixWord ++ tailWord_1931210) baseStart_1931210 baseEnd_1931210 := by
    simpa [prefixWord, tailWord_1931210, baseEnd_1931210] using wordTrace_append hprefix tailTrace_1931210
  have hstable : (prefixWord ++ tailWord_1931210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931210).length < 2 ^ (prefixWord ++ tailWord_1931210).sum := by decide
  have hdescent : baseEnd_1931210 < baseStart_1931210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931243 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 5, 2]
def baseStart_1931243 : Nat := 118140960795 + 1931243 * 2 ^ 59
def prefixEnd_1931243 : Nat := 4983230072969 + 3 ^ 40 * 1931243 * 2
def baseEnd_1931243 : Nat := 991655919631092736580881

theorem tailTrace_1931243 : CollatzResearch.WordTrace tailWord_1931243 prefixEnd_1931243 991655919631092736580881 := by
  unfold tailWord_1931243
  simp only [CollatzResearch.WordTrace]
  refine ⟨70438218942443915890398383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46958812628295943926932255 70438218942443915890398383)
  ·
    refine ⟨105657328413665873835597575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70438218942443915890398383 105657328413665873835597575)
    ·
      refine ⟨158485992620498810753396363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105657328413665873835597575 158485992620498810753396363)
      ·
        refine ⟨237728988930748216130094545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158485992620498810753396363 237728988930748216130094545)
        ·
          refine ⟨178296741698061162097570909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237728988930748216130094545 178296741698061162097570909)
          ·
            refine ⟨66861278136772935786589091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178296741698061162097570909 66861278136772935786589091)
            ·
              refine ⟨100291917205159403679883637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66861278136772935786589091 100291917205159403679883637)
              ·
                refine ⟨9402367237983694094989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100291917205159403679883637 9402367237983694094989091)
                ·
                  refine ⟨14103550856975541142483637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402367237983694094989091 14103550856975541142483637)
                  ·
                    refine ⟨1322207892841456982107841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103550856975541142483637 1322207892841456982107841)
                    ·
                      refine ⟨991655919631092736580881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322207892841456982107841 991655919631092736580881)
                      ·
                        rfl

theorem cell23_1931243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5, 2].length) (baseStart_1931243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931243 prefixEnd_1931243 := by exact prefixLift 1931243
  have htrace : WordTrace (prefixWord ++ tailWord_1931243) baseStart_1931243 baseEnd_1931243 := by
    simpa [prefixWord, tailWord_1931243, baseEnd_1931243] using wordTrace_append hprefix tailTrace_1931243
  have hstable : (prefixWord ++ tailWord_1931243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931243).length < 2 ^ (prefixWord ++ tailWord_1931243).sum := by decide
  have hdescent : baseEnd_1931243 < baseStart_1931243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931260 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_1931260 : Nat := 118140960795 + 1931260 * 2 ^ 59
def prefixEnd_1931260 : Nat := 4983230072969 + 3 ^ 40 * 1931260 * 2
def baseEnd_1931260 : Nat := 991664648802219170068303

theorem tailTrace_1931260 : CollatzResearch.WordTrace tailWord_1931260 prefixEnd_1931260 991664648802219170068303 := by
  unfold tailWord_1931260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219419491691163896883617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46959225988921551862511489 35219419491691163896883617)
  ·
    refine ⟨26414564618768372922662713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35219419491691163896883617 26414564618768372922662713)
    ·
      refine ⟨19810923464076279691997035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26414564618768372922662713 19810923464076279691997035)
      ·
        refine ⟨29716385196114419537995553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19810923464076279691997035 29716385196114419537995553)
        ·
          refine ⟨22287288897085814653496665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29716385196114419537995553 22287288897085814653496665)
          ·
            refine ⟨16715466672814360990122499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22287288897085814653496665 16715466672814360990122499)
            ·
              refine ⟨25073200009221541485183749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16715466672814360990122499 25073200009221541485183749)
              ·
                refine ⟨4701225001729039028471953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25073200009221541485183749 4701225001729039028471953)
                ·
                  refine ⟨3525918751296779271353965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701225001729039028471953 3525918751296779271353965)
                  ·
                    refine ⟨1322219531736292226757737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525918751296779271353965 1322219531736292226757737)
                    ·
                      refine ⟨991664648802219170068303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322219531736292226757737 991664648802219170068303)
                      ·
                        rfl

theorem cell23_1931260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_1931260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931260 prefixEnd_1931260 := by exact prefixLift 1931260
  have htrace : WordTrace (prefixWord ++ tailWord_1931260) baseStart_1931260 baseEnd_1931260 := by
    simpa [prefixWord, tailWord_1931260, baseEnd_1931260] using wordTrace_append hprefix tailTrace_1931260
  have hstable : (prefixWord ++ tailWord_1931260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931260).length < 2 ^ (prefixWord ++ tailWord_1931260).sum := by decide
  have hdescent : baseEnd_1931260 < baseStart_1931260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931273 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 6, 2]
def baseStart_1931273 : Nat := 118140960795 + 1931273 * 2 ^ 59
def prefixEnd_1931273 : Nat := 4983230072969 + 3 ^ 40 * 1931273 * 2
def baseEnd_1931273 : Nat := 991671324050727619205743

theorem tailTrace_1931273 : CollatzResearch.WordTrace tailWord_1931273 prefixEnd_1931273 991671324050727619205743 := by
  unfold tailWord_1931273
  simp only [CollatzResearch.WordTrace]
  refine ⟨70439313132335231013990473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46959542088223487342660315 70439313132335231013990473)
  ·
    refine ⟨52829484849251423260492855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70439313132335231013990473 52829484849251423260492855)
    ·
      refine ⟨79244227273877134890739283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52829484849251423260492855 79244227273877134890739283)
      ·
        refine ⟨118866340910815702336108925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79244227273877134890739283 118866340910815702336108925)
        ·
          refine ⟨44574877841555888376040847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118866340910815702336108925 44574877841555888376040847)
          ·
            refine ⟨66862316762333832564061271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44574877841555888376040847 66862316762333832564061271)
            ·
              refine ⟨100293475143500748846091907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66862316762333832564061271 100293475143500748846091907)
              ·
                refine ⟨150440212715251123269137861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100293475143500748846091907 150440212715251123269137861)
                ·
                  refine ⟨28207539884109585612963349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150440212715251123269137861 28207539884109585612963349)
                  ·
                    refine ⟨1322228432067636825607657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28207539884109585612963349 1322228432067636825607657)
                    ·
                      refine ⟨991671324050727619205743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322228432067636825607657 991671324050727619205743)
                      ·
                        rfl

theorem cell23_1931273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 6, 2].length) (baseStart_1931273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931273 prefixEnd_1931273 := by exact prefixLift 1931273
  have htrace : WordTrace (prefixWord ++ tailWord_1931273) baseStart_1931273 baseEnd_1931273 := by
    simpa [prefixWord, tailWord_1931273, baseEnd_1931273] using wordTrace_append hprefix tailTrace_1931273
  have hstable : (prefixWord ++ tailWord_1931273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931273).length < 2 ^ (prefixWord ++ tailWord_1931273).sum := by decide
  have hdescent : baseEnd_1931273 < baseStart_1931273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931324 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_1931324 : Nat := 118140960795 + 1931324 * 2 ^ 59
def prefixEnd_1931324 : Nat := 4983230072969 + 3 ^ 40 * 1931324 * 2
def baseEnd_1931324 : Nat := 991697511564106919668009

theorem tailTrace_1931324 : CollatzResearch.WordTrace tailWord_1931324 prefixEnd_1931324 991697511564106919668009 := by
  unfold tailWord_1931324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220586627575233362048513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46960782170100311149398017 35220586627575233362048513)
  ·
    refine ⟨26415439970681425021536385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35220586627575233362048513 26415439970681425021536385)
    ·
      refine ⟨19811579978011068766152289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26415439970681425021536385 19811579978011068766152289)
      ·
        refine ⟨14858684983508301574614217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19811579978011068766152289 14858684983508301574614217)
        ·
          refine ⟨11144013737631226180960663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14858684983508301574614217 11144013737631226180960663)
          ·
            refine ⟨16716020606446839271440995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11144013737631226180960663 16716020606446839271440995)
            ·
              refine ⟨25074030909670258907161493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16716020606446839271440995 25074030909670258907161493)
              ·
                refine ⟨1175345198890793386273195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25074030909670258907161493 1175345198890793386273195)
                ·
                  refine ⟨1763017798336190079409793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175345198890793386273195 1763017798336190079409793)
                  ·
                    refine ⟨1322263348752142559557345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763017798336190079409793 1322263348752142559557345)
                    ·
                      refine ⟨991697511564106919668009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322263348752142559557345 991697511564106919668009)
                      ·
                        rfl

theorem cell23_1931324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_1931324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931324 prefixEnd_1931324 := by exact prefixLift 1931324
  have htrace : WordTrace (prefixWord ++ tailWord_1931324) baseStart_1931324 baseEnd_1931324 := by
    simpa [prefixWord, tailWord_1931324, baseEnd_1931324] using wordTrace_append hprefix tailTrace_1931324
  have hstable : (prefixWord ++ tailWord_1931324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931324).length < 2 ^ (prefixWord ++ tailWord_1931324).sum := by decide
  have hdescent : baseEnd_1931324 < baseStart_1931324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931340 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1931340 : Nat := 118140960795 + 1931340 * 2 ^ 59
def prefixEnd_1931340 : Nat := 4983230072969 + 3 ^ 40 * 1931340 * 2
def baseEnd_1931340 : Nat := 991705727254578857067935

theorem tailTrace_1931340 : CollatzResearch.WordTrace tailWord_1931340 prefixEnd_1931340 991705727254578857067935 := by
  unfold tailWord_1931340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220878411546250728339737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46961171215395000971119649 35220878411546250728339737)
  ·
    refine ⟨26415658808659688046254803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35220878411546250728339737 26415658808659688046254803)
    ·
      refine ⟨39623488212989532069382205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26415658808659688046254803 39623488212989532069382205)
      ·
        refine ⟨14858808079871074526018327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39623488212989532069382205 14858808079871074526018327)
        ·
          refine ⟨22288212119806611789027491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14858808079871074526018327 22288212119806611789027491)
          ·
            refine ⟨33432318179709917683541237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22288212119806611789027491 33432318179709917683541237)
            ·
              refine ⟨3134279829347804782831991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33432318179709917683541237 3134279829347804782831991)
              ·
                refine ⟨4701419744021707174247987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134279829347804782831991 4701419744021707174247987)
                ·
                  refine ⟨7052129616032560761371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701419744021707174247987 7052129616032560761371981)
                  ·
                    refine ⟨2644548606012210285514493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7052129616032560761371981 2644548606012210285514493)
                    ·
                      refine ⟨991705727254578857067935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2644548606012210285514493 991705727254578857067935)
                      ·
                        rfl

theorem cell23_1931340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1931340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931340 prefixEnd_1931340 := by exact prefixLift 1931340
  have htrace : WordTrace (prefixWord ++ tailWord_1931340) baseStart_1931340 baseEnd_1931340 := by
    simpa [prefixWord, tailWord_1931340, baseEnd_1931340] using wordTrace_append hprefix tailTrace_1931340
  have hstable : (prefixWord ++ tailWord_1931340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931340).length < 2 ^ (prefixWord ++ tailWord_1931340).sum := by decide
  have hdescent : baseEnd_1931340 < baseStart_1931340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931367 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_1931367 : Nat := 118140960795 + 1931367 * 2 ^ 59
def prefixEnd_1931367 : Nat := 4983230072969 + 3 ^ 40 * 1931367 * 2
def baseEnd_1931367 : Nat := 991719591232250251430311

theorem tailTrace_1931367 : CollatzResearch.WordTrace tailWord_1931367 prefixEnd_1931367 991719591232250251430311 := by
  unfold tailWord_1931367
  simp only [CollatzResearch.WordTrace]
  refine ⟨70442741593994685067912355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46961827729329790045274903 70442741593994685067912355)
  ·
    refine ⟨105664112390992027601868533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70442741593994685067912355 105664112390992027601868533)
    ·
      refine ⟨9906010536655502587675175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105664112390992027601868533 9906010536655502587675175)
      ·
        refine ⟨14859015804983253881512763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906010536655502587675175 14859015804983253881512763)
        ·
          refine ⟨22288523707474880822269145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14859015804983253881512763 22288523707474880822269145)
          ·
            refine ⟨16716392780606160616701859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22288523707474880822269145 16716392780606160616701859)
            ·
              refine ⟨25074589170909240925052789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16716392780606160616701859 25074589170909240925052789)
              ·
                refine ⟨2350742734772741336723699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25074589170909240925052789 2350742734772741336723699)
                ·
                  refine ⟨3526114102159112005085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350742734772741336723699 3526114102159112005085549)
                  ·
                    refine ⟨1322292788309667001907081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526114102159112005085549 1322292788309667001907081)
                    ·
                      refine ⟨991719591232250251430311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322292788309667001907081 991719591232250251430311)
                      ·
                        rfl

theorem cell23_1931367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_1931367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931367 prefixEnd_1931367 := by exact prefixLift 1931367
  have htrace : WordTrace (prefixWord ++ tailWord_1931367) baseStart_1931367 baseEnd_1931367 := by
    simpa [prefixWord, tailWord_1931367, baseEnd_1931367] using wordTrace_append hprefix tailTrace_1931367
  have hstable : (prefixWord ++ tailWord_1931367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931367).length < 2 ^ (prefixWord ++ tailWord_1931367).sum := by decide
  have hdescent : baseEnd_1931367 < baseStart_1931367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931400 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1931400 : Nat := 118140960795 + 1931400 * 2 ^ 59
def prefixEnd_1931400 : Nat := 4983230072969 + 3 ^ 40 * 1931400 * 2
def baseEnd_1931400 : Nat := 991736536093848622317659

theorem tailTrace_1931400 : CollatzResearch.WordTrace tailWord_1931400 prefixEnd_1931400 991736536093848622317659 := by
  unfold tailWord_1931400
  simp only [CollatzResearch.WordTrace]
  refine ⟨35221972601437565851931827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46962630135250087802575769 35221972601437565851931827)
  ·
    refine ⟨52832958902156348777897741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35221972601437565851931827 52832958902156348777897741)
    ·
      refine ⟨19812359588308630791711653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52832958902156348777897741 19812359588308630791711653)
      ·
        refine ⟨3714817422807868273445935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19812359588308630791711653 3714817422807868273445935)
        ·
          refine ⟨5572226134211802410168903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714817422807868273445935 5572226134211802410168903)
          ·
            refine ⟨8358339201317703615253355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572226134211802410168903 8358339201317703615253355)
            ·
              refine ⟨12537508801976555422880033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358339201317703615253355 12537508801976555422880033)
              ·
                refine ⟨9403131601482416567160025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12537508801976555422880033 9403131601482416567160025)
                ·
                  refine ⟨7052348701111812425370019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403131601482416567160025 7052348701111812425370019)
                  ·
                    refine ⟨10578523051667718638055029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052348701111812425370019 10578523051667718638055029)
                    ·
                      refine ⟨991736536093848622317659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10578523051667718638055029 991736536093848622317659)
                      ·
                        rfl

theorem cell23_1931400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1931400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931400 prefixEnd_1931400 := by exact prefixLift 1931400
  have htrace : WordTrace (prefixWord ++ tailWord_1931400) baseStart_1931400 baseEnd_1931400 := by
    simpa [prefixWord, tailWord_1931400, baseEnd_1931400] using wordTrace_append hprefix tailTrace_1931400
  have hstable : (prefixWord ++ tailWord_1931400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931400).length < 2 ^ (prefixWord ++ tailWord_1931400).sum := by decide
  have hdescent : baseEnd_1931400 < baseStart_1931400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_1931483 : Nat := 118140960795 + 1931483 * 2 ^ 59
def prefixEnd_1931483 : Nat := 4983230072969 + 3 ^ 40 * 1931483 * 2
def baseEnd_1931483 : Nat := 991779154988171797579777

theorem tailTrace_1931483 : CollatzResearch.WordTrace tailWord_1931483 prefixEnd_1931483 991779154988171797579777 := by
  unfold tailWord_1931483
  simp only [CollatzResearch.WordTrace]
  refine ⟨70446972461574436879135103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46964648307716291252756735 70446972461574436879135103)
  ·
    refine ⟨105670458692361655318702655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70446972461574436879135103 105670458692361655318702655)
    ·
      refine ⟨158505688038542482978053983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105670458692361655318702655 158505688038542482978053983)
      ·
        refine ⟨237758532057813724467080975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158505688038542482978053983 237758532057813724467080975)
        ·
          refine ⟨356637798086720586700621463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237758532057813724467080975 356637798086720586700621463)
          ·
            refine ⟨534956697130080880050932195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356637798086720586700621463 534956697130080880050932195)
            ·
              refine ⟨802435045695121320076398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534956697130080880050932195 802435045695121320076398293)
              ·
                refine ⟨18807071383479405939290585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 802435045695121320076398293 18807071383479405939290585)
                ·
                  refine ⟨14105303537609554454467939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18807071383479405939290585 14105303537609554454467939)
                  ·
                    refine ⟨21157955306414331681701909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14105303537609554454467939 21157955306414331681701909)
                    ·
                      refine ⟨991779154988171797579777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21157955306414331681701909 991779154988171797579777)
                      ·
                        rfl

theorem cell23_1931483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_1931483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931483 prefixEnd_1931483 := by exact prefixLift 1931483
  have htrace : WordTrace (prefixWord ++ tailWord_1931483) baseStart_1931483 baseEnd_1931483 := by
    simpa [prefixWord, tailWord_1931483, baseEnd_1931483] using wordTrace_append hprefix tailTrace_1931483
  have hstable : (prefixWord ++ tailWord_1931483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931483).length < 2 ^ (prefixWord ++ tailWord_1931483).sum := by decide
  have hdescent : baseEnd_1931483 < baseStart_1931483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931547 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 4, 3, 2]
def baseStart_1931547 : Nat := 118140960795 + 1931547 * 2 ^ 59
def prefixEnd_1931547 : Nat := 4983230072969 + 3 ^ 40 * 1931547 * 2
def baseEnd_1931547 : Nat := 991812017750059547179483

theorem tailTrace_1931547 : CollatzResearch.WordTrace tailWord_1931547 prefixEnd_1931547 991812017750059547179483 := by
  unfold tailWord_1931547
  simp only [CollatzResearch.WordTrace]
  refine ⟨70449306733342575809464895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46966204488895050539643263 70449306733342575809464895)
  ·
    refine ⟨105673960100013863714197343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70449306733342575809464895 105673960100013863714197343)
    ·
      refine ⟨158510940150020795571296015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105673960100013863714197343 158510940150020795571296015)
      ·
        refine ⟨237766410225031193356944023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158510940150020795571296015 237766410225031193356944023)
        ·
          refine ⟨356649615337546790035416035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237766410225031193356944023 356649615337546790035416035)
          ·
            refine ⟨534974423006320185053124053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356649615337546790035416035 534974423006320185053124053)
            ·
              refine ⟨12538463039210629337182595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 534974423006320185053124053 12538463039210629337182595)
              ·
                refine ⟨18807694558815944005773893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12538463039210629337182595 18807694558815944005773893)
                ·
                  refine ⟨3526442729777989501082605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18807694558815944005773893 3526442729777989501082605)
                  ·
                    refine ⟨1322416023666746062905977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526442729777989501082605 1322416023666746062905977)
                    ·
                      refine ⟨991812017750059547179483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322416023666746062905977 991812017750059547179483)
                      ·
                        rfl

theorem cell23_1931547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3, 2].length) (baseStart_1931547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931547 prefixEnd_1931547 := by exact prefixLift 1931547
  have htrace : WordTrace (prefixWord ++ tailWord_1931547) baseStart_1931547 baseEnd_1931547 := by
    simpa [prefixWord, tailWord_1931547, baseEnd_1931547] using wordTrace_append hprefix tailTrace_1931547
  have hstable : (prefixWord ++ tailWord_1931547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931547).length < 2 ^ (prefixWord ++ tailWord_1931547).sum := by decide
  have hdescent : baseEnd_1931547 < baseStart_1931547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931604 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1931604 : Nat := 118140960795 + 1931604 * 2 ^ 59
def prefixEnd_1931604 : Nat := 4983230072969 + 3 ^ 40 * 1931604 * 2
def baseEnd_1931604 : Nat := 330613762049121941388907

theorem tailTrace_1931604 : CollatzResearch.WordTrace tailWord_1931604 prefixEnd_1931604 330613762049121941388907 := by
  unfold tailWord_1931604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35225692847068037272144933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46967590462757383029526577 35225692847068037272144933)
  ·
    refine ⟨6604817408825256988527175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35225692847068037272144933 6604817408825256988527175)
    ·
      refine ⟨9907226113237885482790763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604817408825256988527175 9907226113237885482790763)
      ·
        refine ⟨14860839169856828224186145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907226113237885482790763 14860839169856828224186145)
        ·
          refine ⟨11145629377392621168139609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14860839169856828224186145 11145629377392621168139609)
          ·
            refine ⟨8359222033044465876104707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11145629377392621168139609 8359222033044465876104707)
            ·
              refine ⟨12538833049566698814157061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359222033044465876104707 12538833049566698814157061)
              ·
                refine ⟨2351031196793756027654449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12538833049566698814157061 2351031196793756027654449)
                ·
                  refine ⟨1763273397595317020740837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351031196793756027654449 1763273397595317020740837)
                  ·
                    refine ⟨330613762049121941388907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763273397595317020740837 330613762049121941388907)
                    ·
                      rfl

theorem cell23_1931604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1931604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931604 prefixEnd_1931604 := by exact prefixLift 1931604
  have htrace : WordTrace (prefixWord ++ tailWord_1931604) baseStart_1931604 baseEnd_1931604 := by
    simpa [prefixWord, tailWord_1931604, baseEnd_1931604] using wordTrace_append hprefix tailTrace_1931604
  have hstable : (prefixWord ++ tailWord_1931604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931604).length < 2 ^ (prefixWord ++ tailWord_1931604).sum := by decide
  have hdescent : baseEnd_1931604 < baseStart_1931604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931605 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1931605 : Nat := 118140960795 + 1931605 * 2 ^ 59
def prefixEnd_1931605 : Nat := 4983230072969 + 3 ^ 40 * 1931605 * 2
def baseEnd_1931605 : Nat := 991841799628020320254217

theorem tailTrace_1931605 : CollatzResearch.WordTrace tailWord_1931605 prefixEnd_1931605 991841799628020320254217 := by
  unfold tailWord_1931605
  simp only [CollatzResearch.WordTrace]
  refine ⟨70451422167132451715076269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46967614778088301143384179 70451422167132451715076269)
  ·
    refine ⟨26419283312674669393153601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70451422167132451715076269 26419283312674669393153601)
    ·
      refine ⟨19814462484506002044865201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26419283312674669393153601 19814462484506002044865201)
      ·
        refine ⟨14860846863379501533648901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19814462484506002044865201 14860846863379501533648901)
        ·
          refine ⟨2786408786883656537559169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14860846863379501533648901 2786408786883656537559169)
          ·
            refine ⟨2089806590162742403169377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786408786883656537559169 2089806590162742403169377)
            ·
              refine ⟨1567354942622056802377033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089806590162742403169377 1567354942622056802377033)
              ·
                refine ⟨1175516206966542601782775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567354942622056802377033 1175516206966542601782775)
                ·
                  refine ⟨1763274310449813902674163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175516206966542601782775 1763274310449813902674163)
                  ·
                    refine ⟨2644911465674720854011245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763274310449813902674163 2644911465674720854011245)
                    ·
                      refine ⟨991841799628020320254217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2644911465674720854011245 991841799628020320254217)
                      ·
                        rfl

theorem cell23_1931605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1931605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931605 prefixEnd_1931605 := by exact prefixLift 1931605
  have htrace : WordTrace (prefixWord ++ tailWord_1931605) baseStart_1931605 baseEnd_1931605 := by
    simpa [prefixWord, tailWord_1931605, baseEnd_1931605] using wordTrace_append hprefix tailTrace_1931605
  have hstable : (prefixWord ++ tailWord_1931605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931605).length < 2 ^ (prefixWord ++ tailWord_1931605).sum := by decide
  have hdescent : baseEnd_1931605 < baseStart_1931605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931624 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1931624 : Nat := 118140960795 + 1931624 * 2 ^ 59
def prefixEnd_1931624 : Nat := 4983230072969 + 3 ^ 40 * 1931624 * 2
def baseEnd_1931624 : Nat := 991851555760455745916629

theorem tailTrace_1931624 : CollatzResearch.WordTrace tailWord_1931624 prefixEnd_1931624 991851555760455745916629 := by
  unfold tailWord_1931624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35226057577031808980008963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46968076769375745306678617 35226057577031808980008963)
  ·
    refine ⟨52839086365547713470013445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35226057577031808980008963 52839086365547713470013445)
    ·
      refine ⟨9907328693540196275627521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52839086365547713470013445 9907328693540196275627521)
      ·
        refine ⟨7430496520155147206720641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9907328693540196275627521 7430496520155147206720641)
        ·
          refine ⟨5572872390116360405040481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7430496520155147206720641 5572872390116360405040481)
          ·
            refine ⟨4179654292587270303780361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572872390116360405040481 4179654292587270303780361)
            ·
              refine ⟨3134740719440452727835271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179654292587270303780361 3134740719440452727835271)
              ·
                refine ⟨4702111079160679091752907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134740719440452727835271 4702111079160679091752907)
                ·
                  refine ⟨7053166618741018637629361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702111079160679091752907 7053166618741018637629361)
                  ·
                    refine ⟨5289874964055763978222021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7053166618741018637629361 5289874964055763978222021)
                    ·
                      refine ⟨991851555760455745916629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5289874964055763978222021 991851555760455745916629)
                      ·
                        rfl

theorem cell23_1931624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1931624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931624 prefixEnd_1931624 := by exact prefixLift 1931624
  have htrace : WordTrace (prefixWord ++ tailWord_1931624) baseStart_1931624 baseEnd_1931624 := by
    simpa [prefixWord, tailWord_1931624, baseEnd_1931624] using wordTrace_append hprefix tailTrace_1931624
  have hstable : (prefixWord ++ tailWord_1931624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931624).length < 2 ^ (prefixWord ++ tailWord_1931624).sum := by decide
  have hdescent : baseEnd_1931624 < baseStart_1931624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 10, 2]
def baseStart_1931667 : Nat := 118140960795 + 1931667 * 2 ^ 59
def prefixEnd_1931667 : Nat := 4983230072969 + 3 ^ 40 * 1931667 * 2
def baseEnd_1931667 : Nat := 991873635428599077678931

theorem tailTrace_1931667 : CollatzResearch.WordTrace tailWord_1931667 prefixEnd_1931667 991873635428599077678931 := by
  unfold tailWord_1931667
  simp only [CollatzResearch.WordTrace]
  refine ⟨70453683492907836303833255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46969122328605224202555503 70453683492907836303833255)
  ·
    refine ⟨105680525239361754455749883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70453683492907836303833255 105680525239361754455749883)
    ·
      refine ⟨158520787859042631683624825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105680525239361754455749883 158520787859042631683624825)
      ·
        refine ⟨118890590894281973762718619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158520787859042631683624825 118890590894281973762718619)
        ·
          refine ⟨178335886341422960644077929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118890590894281973762718619 178335886341422960644077929)
          ·
            refine ⟨133751914756067220483058447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178335886341422960644077929 133751914756067220483058447)
            ·
              refine ⟨200627872134100830724587671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133751914756067220483058447 200627872134100830724587671)
              ·
                refine ⟨300941808201151246086881507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200627872134100830724587671 300941808201151246086881507)
                ·
                  refine ⟨451412712301726869130322261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300941808201151246086881507 451412712301726869130322261)
                  ·
                    refine ⟨1322498180571465436905241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 451412712301726869130322261 1322498180571465436905241)
                    ·
                      refine ⟨991873635428599077678931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322498180571465436905241 991873635428599077678931)
                      ·
                        rfl

theorem cell23_1931667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10, 2].length) (baseStart_1931667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931667 prefixEnd_1931667 := by exact prefixLift 1931667
  have htrace : WordTrace (prefixWord ++ tailWord_1931667) baseStart_1931667 baseEnd_1931667 := by
    simpa [prefixWord, tailWord_1931667, baseEnd_1931667] using wordTrace_append hprefix tailTrace_1931667
  have hstable : (prefixWord ++ tailWord_1931667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931667).length < 2 ^ (prefixWord ++ tailWord_1931667).sum := by decide
  have hdescent : baseEnd_1931667 < baseStart_1931667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931678 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1931678 : Nat := 118140960795 + 1931678 * 2 ^ 59
def prefixEnd_1931678 : Nat := 4983230072969 + 3 ^ 40 * 1931678 * 2
def baseEnd_1931678 : Nat := 991879283715798534641381

theorem tailTrace_1931678 : CollatzResearch.WordTrace tailWord_1931678 prefixEnd_1931678 991879283715798534641381 := by
  unfold tailWord_1931678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806760586983498147810461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46969389797245323454989125 8806760586983498147810461)
  ·
    refine ⟨3302535220118811805428923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8806760586983498147810461 3302535220118811805428923)
    ·
      refine ⟨4953802830178217708143385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302535220118811805428923 4953802830178217708143385)
      ·
        refine ⟨3715352122633663281107539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4953802830178217708143385 3715352122633663281107539)
        ·
          refine ⟨5573028183950494921661309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715352122633663281107539 5573028183950494921661309)
          ·
            refine ⟨2089885568981435595622991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5573028183950494921661309 2089885568981435595622991)
            ·
              refine ⟨3134828353472153393434487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089885568981435595622991 3134828353472153393434487)
              ·
                refine ⟨4702242530208230090151731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134828353472153393434487 4702242530208230090151731)
                ·
                  refine ⟨7053363795312345135227597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702242530208230090151731 7053363795312345135227597)
                  ·
                    refine ⟨2645011423242129425710349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7053363795312345135227597 2645011423242129425710349)
                    ·
                      refine ⟨991879283715798534641381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645011423242129425710349 991879283715798534641381)
                      ·
                        rfl

theorem cell23_1931678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1931678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931678 prefixEnd_1931678 := by exact prefixLift 1931678
  have htrace : WordTrace (prefixWord ++ tailWord_1931678) baseStart_1931678 baseEnd_1931678 := by
    simpa [prefixWord, tailWord_1931678, baseEnd_1931678] using wordTrace_append hprefix tailTrace_1931678
  have hstable : (prefixWord ++ tailWord_1931678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931678).length < 2 ^ (prefixWord ++ tailWord_1931678).sum := by decide
  have hdescent : baseEnd_1931678 < baseStart_1931678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931688 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1931688 : Nat := 118140960795 + 1931688 * 2 ^ 59
def prefixEnd_1931688 : Nat := 4983230072969 + 3 ^ 40 * 1931688 * 2
def baseEnd_1931688 : Nat := 991884418522343495516335

theorem tailTrace_1931688 : CollatzResearch.WordTrace tailWord_1931688 prefixEnd_1931688 991884418522343495516335 := by
  unfold tailWord_1931688
  simp only [CollatzResearch.WordTrace]
  refine ⟨35227224712915878445173859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46969632950554504593565145 35227224712915878445173859)
  ·
    refine ⟨52840837069373817667760789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35227224712915878445173859 52840837069373817667760789)
    ·
      refine ⟨2476914237626897703176287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52840837069373817667760789 2476914237626897703176287)
      ·
        refine ⟨3715371356440346554764431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476914237626897703176287 3715371356440346554764431)
        ·
          refine ⟨5573057034660519832146647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715371356440346554764431 5573057034660519832146647)
          ·
            refine ⟨8359585551990779748219971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573057034660519832146647 8359585551990779748219971)
            ·
              refine ⟨12539378327986169622329957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359585551990779748219971 12539378327986169622329957)
              ·
                refine ⟨2351133436497406804186867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12539378327986169622329957 2351133436497406804186867)
                ·
                  refine ⟨3526700154746110206280301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351133436497406804186867 3526700154746110206280301)
                  ·
                    refine ⟨1322512558029791327355113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526700154746110206280301 1322512558029791327355113)
                    ·
                      refine ⟨991884418522343495516335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322512558029791327355113 991884418522343495516335)
                      ·
                        rfl

theorem cell23_1931688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1931688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931688 prefixEnd_1931688 := by exact prefixLift 1931688
  have htrace : WordTrace (prefixWord ++ tailWord_1931688) baseStart_1931688 baseEnd_1931688 := by
    simpa [prefixWord, tailWord_1931688, baseEnd_1931688] using wordTrace_append hprefix tailTrace_1931688
  have hstable : (prefixWord ++ tailWord_1931688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931688).length < 2 ^ (prefixWord ++ tailWord_1931688).sum := by decide
  have hdescent : baseEnd_1931688 < baseStart_1931688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931737 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_1931737 : Nat := 118140960795 + 1931737 * 2 ^ 59
def prefixEnd_1931737 : Nat := 4983230072969 + 3 ^ 40 * 1931737 * 2
def baseEnd_1931737 : Nat := 330636526358137934601203

theorem tailTrace_1931737 : CollatzResearch.WordTrace tailWord_1931737 prefixEnd_1931737 330636526358137934601203 := by
  unfold tailWord_1931737
  simp only [CollatzResearch.WordTrace]
  refine ⟨70456236602654238258881465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46970824401769492172587643 70456236602654238258881465)
  ·
    refine ⟨52842177451990678694161099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70456236602654238258881465 52842177451990678694161099)
    ·
      refine ⟨79263266177986018041241649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52842177451990678694161099 79263266177986018041241649)
      ·
        refine ⟨59447449633489513530931237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79263266177986018041241649 59447449633489513530931237)
        ·
          refine ⟨11146396806279283787049607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59447449633489513530931237 11146396806279283787049607)
          ·
            refine ⟨16719595209418925680574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146396806279283787049607 16719595209418925680574411)
            ·
              refine ⟨25079392814128388520861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719595209418925680574411 25079392814128388520861617)
              ·
                refine ⟨18809544610596291390646213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25079392814128388520861617 18809544610596291390646213)
                ·
                  refine ⟨3526789614486804635746165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18809544610596291390646213 3526789614486804635746165)
                  ·
                    refine ⟨330636526358137934601203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3526789614486804635746165 330636526358137934601203)
                    ·
                      rfl

theorem cell23_1931737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_1931737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931737 prefixEnd_1931737 := by exact prefixLift 1931737
  have htrace : WordTrace (prefixWord ++ tailWord_1931737) baseStart_1931737 baseEnd_1931737 := by
    simpa [prefixWord, tailWord_1931737, baseEnd_1931737] using wordTrace_append hprefix tailTrace_1931737
  have hstable : (prefixWord ++ tailWord_1931737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931737).length < 2 ^ (prefixWord ++ tailWord_1931737).sum := by decide
  have hdescent : baseEnd_1931737 < baseStart_1931737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931754 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1931754 : Nat := 118140960795 + 1931754 * 2 ^ 59
def prefixEnd_1931754 : Nat := 4983230072969 + 3 ^ 40 * 1931754 * 2
def baseEnd_1931754 : Nat := 330639436081846745763677

theorem tailTrace_1931754 : CollatzResearch.WordTrace tailWord_1931754 prefixEnd_1931754 330639436081846745763677 := by
  unfold tailWord_1931754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614214160898162540562579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46971237762395100108166877 17614214160898162540562579)
  ·
    refine ⟨26421321241347243810843869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17614214160898162540562579 26421321241347243810843869)
    ·
      refine ⟨9907995465505216429066451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26421321241347243810843869 9907995465505216429066451)
      ·
        refine ⟨14861993198257824643599677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907995465505216429066451 14861993198257824643599677)
        ·
          refine ⟨5573247449346684241349879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14861993198257824643599677 5573247449346684241349879)
          ·
            refine ⟨8359871174020026362024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573247449346684241349879 8359871174020026362024819)
            ·
              refine ⟨12539806761030039543037229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359871174020026362024819 12539806761030039543037229)
              ·
                refine ⟨4702427535386264828638961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12539806761030039543037229 4702427535386264828638961)
                ·
                  refine ⟨3526820651539698621479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702427535386264828638961 3526820651539698621479221)
                  ·
                    refine ⟨330639436081846745763677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3526820651539698621479221 330639436081846745763677)
                    ·
                      rfl

theorem cell23_1931754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1931754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931754 prefixEnd_1931754 := by exact prefixLift 1931754
  have htrace : WordTrace (prefixWord ++ tailWord_1931754) baseStart_1931754 baseEnd_1931754 := by
    simpa [prefixWord, tailWord_1931754, baseEnd_1931754] using wordTrace_append hprefix tailTrace_1931754
  have hstable : (prefixWord ++ tailWord_1931754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931754).length < 2 ^ (prefixWord ++ tailWord_1931754).sum := by decide
  have hdescent : baseEnd_1931754 < baseStart_1931754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931784 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1931784 : Nat := 118140960795 + 1931784 * 2 ^ 59
def prefixEnd_1931784 : Nat := 4983230072969 + 3 ^ 40 * 1931784 * 2
def baseEnd_1931784 : Nat := 330644570888391706638631

theorem tailTrace_1931784 : CollatzResearch.WordTrace tailWord_1931784 prefixEnd_1931784 330644570888391706638631 := by
  unfold tailWord_1931784
  simp only [CollatzResearch.WordTrace]
  refine ⟨35228975416741982642921203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46971967222322643523894937 35228975416741982642921203)
  ·
    refine ⟨52843463125112973964381805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35228975416741982642921203 52843463125112973964381805)
    ·
      refine ⟨19816298671917365236643177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52843463125112973964381805 19816298671917365236643177)
      ·
        refine ⟨14862224003938023927482383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19816298671917365236643177 14862224003938023927482383)
        ·
          refine ⟨22293336005907035891223575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14862224003938023927482383 22293336005907035891223575)
          ·
            refine ⟨33440004008860553836835363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22293336005907035891223575 33440004008860553836835363)
            ·
              refine ⟨50160006013290830755253045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33440004008860553836835363 50160006013290830755253045)
              ·
                refine ⟨4702500563746015383304973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50160006013290830755253045 4702500563746015383304973)
                ·
                  refine ⟨1763437711404755768739365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4702500563746015383304973 1763437711404755768739365)
                  ·
                    refine ⟨330644570888391706638631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763437711404755768739365 330644570888391706638631)
                    ·
                      rfl

theorem cell23_1931784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1931784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931784 prefixEnd_1931784 := by exact prefixLift 1931784
  have htrace : WordTrace (prefixWord ++ tailWord_1931784) baseStart_1931784 baseEnd_1931784 := by
    simpa [prefixWord, tailWord_1931784, baseEnd_1931784] using wordTrace_append hprefix tailTrace_1931784
  have hstable : (prefixWord ++ tailWord_1931784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931784).length < 2 ^ (prefixWord ++ tailWord_1931784).sum := by decide
  have hdescent : baseEnd_1931784 < baseStart_1931784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931808 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1931808 : Nat := 118140960795 + 1931808 * 2 ^ 59
def prefixEnd_1931808 : Nat := 4983230072969 + 3 ^ 40 * 1931808 * 2
def baseEnd_1931808 : Nat := 991946036200883026015783

theorem tailTrace_1931808 : CollatzResearch.WordTrace tailWord_1931808 prefixEnd_1931808 991946036200883026015783 := by
  unfold tailWord_1931808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35229413092698508692358039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46972550790264678256477385 35229413092698508692358039)
  ·
    refine ⟨52844119639047763038537059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35229413092698508692358039 52844119639047763038537059)
    ·
      refine ⟨79266179458571644557805589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52844119639047763038537059 79266179458571644557805589)
      ·
        refine ⟨3715602162120545838647137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79266179458571644557805589 3715602162120545838647137)
        ·
          refine ⟨2786701621590409378985353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3715602162120545838647137 2786701621590409378985353)
          ·
            refine ⟨2090026216192807034239015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786701621590409378985353 2090026216192807034239015)
            ·
              refine ⟨3135039324289210551358523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090026216192807034239015 3135039324289210551358523)
              ·
                refine ⟨4702558986433815827037785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135039324289210551358523 4702558986433815827037785)
                ·
                  refine ⟨3526919239825361870278339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702558986433815827037785 3526919239825361870278339)
                  ·
                    refine ⟨5290378859738042805417509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3526919239825361870278339 5290378859738042805417509)
                    ·
                      refine ⟨991946036200883026015783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5290378859738042805417509 991946036200883026015783)
                      ·
                        rfl

theorem cell23_1931808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1931808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931808 prefixEnd_1931808 := by exact prefixLift 1931808
  have htrace : WordTrace (prefixWord ++ tailWord_1931808) baseStart_1931808 baseEnd_1931808 := by
    simpa [prefixWord, tailWord_1931808, baseEnd_1931808] using wordTrace_append hprefix tailTrace_1931808
  have hstable : (prefixWord ++ tailWord_1931808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931808).length < 2 ^ (prefixWord ++ tailWord_1931808).sum := by decide
  have hdescent : baseEnd_1931808 < baseStart_1931808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931811 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1931811 : Nat := 118140960795 + 1931811 * 2 ^ 59
def prefixEnd_1931811 : Nat := 4983230072969 + 3 ^ 40 * 1931811 * 2
def baseEnd_1931811 : Nat := 991947576642846514278269

theorem tailTrace_1931811 : CollatzResearch.WordTrace tailWord_1931811 prefixEnd_1931811 991947576642846514278269 := by
  unfold tailWord_1931811
  simp only [CollatzResearch.WordTrace]
  refine ⟨70458935604386148897075287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46972623736257432598050191 70458935604386148897075287)
  ·
    refine ⟨105688403406579223345612931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70458935604386148897075287 105688403406579223345612931)
    ·
      refine ⟨158532605109868835018419397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105688403406579223345612931 158532605109868835018419397)
      ·
        refine ⟨29724863458100406565953637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158532605109868835018419397 29724863458100406565953637)
        ·
          refine ⟨5573411898393826231116307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29724863458100406565953637 5573411898393826231116307)
          ·
            refine ⟨8360117847590739346674461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573411898393826231116307 8360117847590739346674461)
            ·
              refine ⟨3135044192846527255002923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360117847590739346674461 3135044192846527255002923)
              ·
                refine ⟨4702566289269790882504385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135044192846527255002923 4702566289269790882504385)
                ·
                  refine ⟨3526924716952343161878289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702566289269790882504385 3526924716952343161878289)
                  ·
                    refine ⟨2645193537714257371408717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526924716952343161878289 2645193537714257371408717)
                    ·
                      refine ⟨991947576642846514278269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645193537714257371408717 991947576642846514278269)
                      ·
                        rfl

theorem cell23_1931811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1931811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931811 prefixEnd_1931811 := by exact prefixLift 1931811
  have htrace : WordTrace (prefixWord ++ tailWord_1931811) baseStart_1931811 baseEnd_1931811 := by
    simpa [prefixWord, tailWord_1931811, baseEnd_1931811] using wordTrace_append hprefix tailTrace_1931811
  have hstable : (prefixWord ++ tailWord_1931811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931811).length < 2 ^ (prefixWord ++ tailWord_1931811).sum := by decide
  have hdescent : baseEnd_1931811 < baseStart_1931811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931818 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1931818 : Nat := 118140960795 + 1931818 * 2 ^ 59
def prefixEnd_1931818 : Nat := 4983230072969 + 3 ^ 40 * 1931818 * 2
def baseEnd_1931818 : Nat := 330650390335809328963579

theorem tailTrace_1931818 : CollatzResearch.WordTrace tailWord_1931818 prefixEnd_1931818 330650390335809328963579 := by
  unfold tailWord_1931818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614797728840197273145027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46972793943573859395053405 17614797728840197273145027)
  ·
    refine ⟨26422196593260295909717541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17614797728840197273145027 26422196593260295909717541)
    ·
      refine ⟨4954161861236305483072039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26422196593260295909717541 4954161861236305483072039)
      ·
        refine ⟨7431242791854458224608059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954161861236305483072039 7431242791854458224608059)
        ·
          refine ⟨11146864187781687336912089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431242791854458224608059 11146864187781687336912089)
          ·
            refine ⟨8360148140836265502684067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11146864187781687336912089 8360148140836265502684067)
            ·
              refine ⟨12540222211254398254026101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360148140836265502684067 12540222211254398254026101)
              ·
                refine ⟨1175645832305099836314947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12540222211254398254026101 1175645832305099836314947)
                ·
                  refine ⟨1763468748457649754472421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175645832305099836314947 1763468748457649754472421)
                  ·
                    refine ⟨330650390335809328963579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763468748457649754472421 330650390335809328963579)
                    ·
                      rfl

theorem cell23_1931818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1931818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931818 prefixEnd_1931818 := by exact prefixLift 1931818
  have htrace : WordTrace (prefixWord ++ tailWord_1931818) baseStart_1931818 baseEnd_1931818 := by
    simpa [prefixWord, tailWord_1931818, baseEnd_1931818] using wordTrace_append hprefix tailTrace_1931818
  have hstable : (prefixWord ++ tailWord_1931818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931818).length < 2 ^ (prefixWord ++ tailWord_1931818).sum := by decide
  have hdescent : baseEnd_1931818 < baseStart_1931818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931864 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1931864 : Nat := 118140960795 + 1931864 * 2 ^ 59
def prefixEnd_1931864 : Nat := 4983230072969 + 3 ^ 40 * 1931864 * 2
def baseEnd_1931864 : Nat := 991974791117534806915525

theorem tailTrace_1931864 : CollatzResearch.WordTrace tailWord_1931864 prefixEnd_1931864 991974791117534806915525 := by
  unfold tailWord_1931864
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230434336597069474377323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46973912448796092632503097 35230434336597069474377323)
  ·
    refine ⟨52845651504895604211565985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35230434336597069474377323 52845651504895604211565985)
    ·
      refine ⟨39634238628671703158674489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52845651504895604211565985 39634238628671703158674489)
      ·
        refine ⟨29725678971503777369005867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39634238628671703158674489 29725678971503777369005867)
        ·
          refine ⟨44588518457255666053508801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29725678971503777369005867 44588518457255666053508801)
          ·
            refine ⟨33441388842941749540131601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44588518457255666053508801 33441388842941749540131601)
            ·
              refine ⟨25081041632206312155098701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33441388842941749540131601 25081041632206312155098701)
              ·
                refine ⟨9405390612077367058162013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25081041632206312155098701 9405390612077367058162013)
                ·
                  refine ⟨3527021479529012646810755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9405390612077367058162013 3527021479529012646810755)
                  ·
                    refine ⟨5290532219293518970216133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527021479529012646810755 5290532219293518970216133)
                    ·
                      refine ⟨991974791117534806915525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5290532219293518970216133 991974791117534806915525)
                      ·
                        rfl

theorem cell23_1931864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1931864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931864 prefixEnd_1931864 := by exact prefixLift 1931864
  have htrace : WordTrace (prefixWord ++ tailWord_1931864) baseStart_1931864 baseEnd_1931864 := by
    simpa [prefixWord, tailWord_1931864, baseEnd_1931864] using wordTrace_append hprefix tailTrace_1931864
  have hstable : (prefixWord ++ tailWord_1931864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931864).length < 2 ^ (prefixWord ++ tailWord_1931864).sum := by decide
  have hdescent : baseEnd_1931864 < baseStart_1931864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931884 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1931884 : Nat := 118140960795 + 1931884 * 2 ^ 59
def prefixEnd_1931884 : Nat := 4983230072969 + 3 ^ 40 * 1931884 * 2
def baseEnd_1931884 : Nat := 991985060730624728665433

theorem tailTrace_1931884 : CollatzResearch.WordTrace tailWord_1931884 prefixEnd_1931884 991985060730624728665433 := by
  unfold tailWord_1931884
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230799066560841182241353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46974398755414454909655137 35230799066560841182241353)
  ·
    refine ⟨26423099299920630886681015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35230799066560841182241353 26423099299920630886681015)
    ·
      refine ⟨39634648949880946330021523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26423099299920630886681015 39634648949880946330021523)
      ·
        refine ⟨59451973424821419495032285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39634648949880946330021523 59451973424821419495032285)
        ·
          refine ⟨22294490034308032310637107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59451973424821419495032285 22294490034308032310637107)
          ·
            refine ⟨33441735051462048465955661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22294490034308032310637107 33441735051462048465955661)
            ·
              refine ⟨12540650644298268174733373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33441735051462048465955661 12540650644298268174733373)
              ·
                refine ⟨4702743991611850565525015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12540650644298268174733373 4702743991611850565525015)
                ·
                  refine ⟨7054115987417775848287523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702743991611850565525015 7054115987417775848287523)
                  ·
                    refine ⟨10581173981126663772431285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054115987417775848287523 10581173981126663772431285)
                    ·
                      refine ⟨991985060730624728665433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10581173981126663772431285 991985060730624728665433)
                      ·
                        rfl

theorem cell23_1931884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1931884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931884 prefixEnd_1931884 := by exact prefixLift 1931884
  have htrace : WordTrace (prefixWord ++ tailWord_1931884) baseStart_1931884 baseEnd_1931884 := by
    simpa [prefixWord, tailWord_1931884, baseEnd_1931884] using wordTrace_append hprefix tailTrace_1931884
  have hstable : (prefixWord ++ tailWord_1931884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931884).length < 2 ^ (prefixWord ++ tailWord_1931884).sum := by decide
  have hdescent : baseEnd_1931884 < baseStart_1931884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931887 : List Nat := [1, 1, 2, 1, 3, 2, 13]
def baseStart_1931887 : Nat := 118140960795 + 1931887 * 2 ^ 59
def prefixEnd_1931887 : Nat := 4983230072969 + 3 ^ 40 * 1931887 * 2
def baseEnd_1931887 : Nat := 12246748162624545887999

theorem tailTrace_1931887 : CollatzResearch.WordTrace tailWord_1931887 prefixEnd_1931887 12246748162624545887999 := by
  unfold tailWord_1931887
  simp only [CollatzResearch.WordTrace]
  refine ⟨70461707552110813876841915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46974471701407209251227943 70461707552110813876841915)
  ·
    refine ⟨105692561328166220815262873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70461707552110813876841915 105692561328166220815262873)
    ·
      refine ⟨79269420996124665611447155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105692561328166220815262873 79269420996124665611447155)
      ·
        refine ⟨118904131494186998417170733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79269420996124665611447155 118904131494186998417170733)
        ·
          refine ⟨44589049310320124406439025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118904131494186998417170733 44589049310320124406439025)
          ·
            refine ⟨33441786982740093304829269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44589049310320124406439025 33441786982740093304829269)
            ·
              refine ⟨12246748162624545887999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 33441786982740093304829269 12246748162624545887999)
              ·
                rfl

theorem cell23_1931887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 13].length) (baseStart_1931887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931887 prefixEnd_1931887 := by exact prefixLift 1931887
  have htrace : WordTrace (prefixWord ++ tailWord_1931887) baseStart_1931887 baseEnd_1931887 := by
    simpa [prefixWord, tailWord_1931887, baseEnd_1931887] using wordTrace_append hprefix tailTrace_1931887
  have hstable : (prefixWord ++ tailWord_1931887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931887).length < 2 ^ (prefixWord ++ tailWord_1931887).sum := by decide
  have hdescent : baseEnd_1931887 < baseStart_1931887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931904 : List Nat := [2, 1, 1, 2, 1, 6, 2, 8]
def baseStart_1931904 : Nat := 118140960795 + 1931904 * 2 ^ 59
def prefixEnd_1931904 : Nat := 4983230072969 + 3 ^ 40 * 1931904 * 2
def baseEnd_1931904 : Nat := 36740567790507950015383

theorem tailTrace_1931904 : CollatzResearch.WordTrace tailWord_1931904 prefixEnd_1931904 36740567790507950015383 := by
  unfold tailWord_1931904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231163796524612890105383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46974885062032817186807177 35231163796524612890105383)
  ·
    refine ⟨52846745694786919335158075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35231163796524612890105383 52846745694786919335158075)
    ·
      refine ⟨79270118542180379002737113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52846745694786919335158075 79270118542180379002737113)
      ·
        refine ⟨59452588906635284252052835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79270118542180379002737113 59452588906635284252052835)
        ·
          refine ⟨89178883359952926378079253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59452588906635284252052835 89178883359952926378079253)
          ·
            refine ⟨4180260157497793423972465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89178883359952926378079253 4180260157497793423972465)
            ·
              refine ⟨3135195118123345067979349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180260157497793423972465 3135195118123345067979349)
              ·
                refine ⟨36740567790507950015383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3135195118123345067979349 36740567790507950015383)
                ·
                  rfl

theorem cell23_1931904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_1931904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931904 prefixEnd_1931904 := by exact prefixLift 1931904
  have htrace : WordTrace (prefixWord ++ tailWord_1931904) baseStart_1931904 baseEnd_1931904 := by
    simpa [prefixWord, tailWord_1931904, baseEnd_1931904] using wordTrace_append hprefix tailTrace_1931904
  have hstable : (prefixWord ++ tailWord_1931904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931904).length < 2 ^ (prefixWord ++ tailWord_1931904).sum := by decide
  have hdescent : baseEnd_1931904 < baseStart_1931904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931908 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1931908 : Nat := 118140960795 + 1931908 * 2 ^ 59
def prefixEnd_1931908 : Nat := 4983230072969 + 3 ^ 40 * 1931908 * 2
def baseEnd_1931908 : Nat := 330665794755444211588441

theorem tailTrace_1931908 : CollatzResearch.WordTrace tailWord_1931908 prefixEnd_1931908 330665794755444211588441 := by
  unfold tailWord_1931908
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231236742517367231678189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46974982323356489642237585 35231236742517367231678189)
  ·
    refine ⟨13211713778444012711879321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35231236742517367231678189 13211713778444012711879321)
    ·
      refine ⟨9908785333833009533909491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13211713778444012711879321 9908785333833009533909491)
      ·
        refine ⟨14863178000749514300864237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9908785333833009533909491 14863178000749514300864237)
        ·
          refine ⟨5573691750281067862824089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14863178000749514300864237 5573691750281067862824089)
          ·
            refine ⟨4180268812710800897118067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5573691750281067862824089 4180268812710800897118067)
            ·
              refine ⟨6270403219066201345677101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180268812710800897118067 6270403219066201345677101)
              ·
                refine ⟨2351401207149825504628913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6270403219066201345677101 2351401207149825504628913)
                ·
                  refine ⟨1763550905362369128471685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351401207149825504628913 1763550905362369128471685)
                  ·
                    refine ⟨330665794755444211588441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763550905362369128471685 330665794755444211588441)
                    ·
                      rfl

theorem cell23_1931908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1931908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931908 prefixEnd_1931908 := by exact prefixLift 1931908
  have htrace : WordTrace (prefixWord ++ tailWord_1931908) baseStart_1931908 baseEnd_1931908 := by
    simpa [prefixWord, tailWord_1931908, baseEnd_1931908] using wordTrace_append hprefix tailTrace_1931908
  have hstable : (prefixWord ++ tailWord_1931908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931908).length < 2 ^ (prefixWord ++ tailWord_1931908).sum := by decide
  have hdescent : baseEnd_1931908 < baseStart_1931908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931949 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_1931949 : Nat := 118140960795 + 1931949 * 2 ^ 59
def prefixEnd_1931949 : Nat := 4983230072969 + 3 ^ 40 * 1931949 * 2
def baseEnd_1931949 : Nat := 992018436973166974352635

theorem tailTrace_1931949 : CollatzResearch.WordTrace tailWord_1931949 prefixEnd_1931949 992018436973166974352635 := by
  unfold tailWord_1931949
  simp only [CollatzResearch.WordTrace]
  refine ⟨70463968877886198465598901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46975979251924132310399267 70463968877886198465598901)
  ·
    refine ⟨6605997082301831106149897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70463968877886198465598901 6605997082301831106149897)
    ·
      refine ⟨4954497811726373329612423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6605997082301831106149897 4954497811726373329612423)
      ·
        refine ⟨7431746717589559994418635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954497811726373329612423 7431746717589559994418635)
        ·
          refine ⟨11147620076384339991627953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431746717589559994418635 11147620076384339991627953)
          ·
            refine ⟨8360715057288254993720965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147620076384339991627953 8360715057288254993720965)
            ·
              refine ⟨1567634073241547811322681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8360715057288254993720965 1567634073241547811322681)
              ·
                refine ⟨1175725554931160858492011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567634073241547811322681 1175725554931160858492011)
                ·
                  refine ⟨1763588332396741287738017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175725554931160858492011 1763588332396741287738017)
                  ·
                    refine ⟨1322691249297555965803513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763588332396741287738017 1322691249297555965803513)
                    ·
                      refine ⟨992018436973166974352635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322691249297555965803513 992018436973166974352635)
                      ·
                        rfl

theorem cell23_1931949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_1931949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931949 prefixEnd_1931949 := by exact prefixLift 1931949
  have htrace : WordTrace (prefixWord ++ tailWord_1931949) baseStart_1931949 baseEnd_1931949 := by
    simpa [prefixWord, tailWord_1931949, baseEnd_1931949] using wordTrace_append hprefix tailTrace_1931949
  have hstable : (prefixWord ++ tailWord_1931949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931949).length < 2 ^ (prefixWord ++ tailWord_1931949).sum := by decide
  have hdescent : baseEnd_1931949 < baseStart_1931949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931992 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_1931992 : Nat := 118140960795 + 1931992 * 2 ^ 59
def prefixEnd_1931992 : Nat := 4983230072969 + 3 ^ 40 * 1931992 * 2
def baseEnd_1931992 : Nat := 992040516641310306114937

theorem tailTrace_1931992 : CollatzResearch.WordTrace tailWord_1931992 prefixEnd_1931992 992040516641310306114937 := by
  unfold tailWord_1931992
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232768608365208404707115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46977024811153611206276153 35232768608365208404707115)
  ·
    refine ⟨52849152912547812607060673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35232768608365208404707115 52849152912547812607060673)
    ·
      refine ⟨39636864684410859455295505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52849152912547812607060673 39636864684410859455295505)
      ·
        refine ⟨29727648513308144591471629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39636864684410859455295505 29727648513308144591471629)
        ·
          refine ⟨11147868192490554221801861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29727648513308144591471629 11147868192490554221801861)
          ·
            refine ⟨2090225286091978916587849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11147868192490554221801861 2090225286091978916587849)
            ·
              refine ⟨1567668964568984187440887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090225286091978916587849 1567668964568984187440887)
              ·
                refine ⟨2351503446853476281161331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567668964568984187440887 2351503446853476281161331)
                ·
                  refine ⟨3527255170280214421741997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351503446853476281161331 3527255170280214421741997)
                  ·
                    refine ⟨1322720688855080408153249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527255170280214421741997 1322720688855080408153249)
                    ·
                      refine ⟨992040516641310306114937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322720688855080408153249 992040516641310306114937)
                      ·
                        rfl

theorem cell23_1931992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_1931992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931992 prefixEnd_1931992 := by exact prefixLift 1931992
  have htrace : WordTrace (prefixWord ++ tailWord_1931992) baseStart_1931992 baseEnd_1931992 := by
    simpa [prefixWord, tailWord_1931992, baseEnd_1931992] using wordTrace_append hprefix tailTrace_1931992
  have hstable : (prefixWord ++ tailWord_1931992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931992).length < 2 ^ (prefixWord ++ tailWord_1931992).sum := by decide
  have hdescent : baseEnd_1931992 < baseStart_1931992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931994 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_1931994 : Nat := 118140960795 + 1931994 * 2 ^ 59
def prefixEnd_1931994 : Nat := 4983230072969 + 3 ^ 40 * 1931994 * 2
def baseEnd_1931994 : Nat := 110226838178068810921103

theorem tailTrace_1931994 : CollatzResearch.WordTrace tailWord_1931994 prefixEnd_1931994 110226838178068810921103 := by
  unfold tailWord_1931994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17616402540680792787746759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46977073441815447433991357 17616402540680792787746759)
  ·
    refine ⟨26424603811021189181620139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17616402540680792787746759 26424603811021189181620139)
    ·
      refine ⟨39636905716531783772430209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26424603811021189181620139 39636905716531783772430209)
      ·
        refine ⟨29727679287398837829322657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39636905716531783772430209 29727679287398837829322657)
        ·
          refine ⟨22295759465549128371991993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29727679287398837829322657 22295759465549128371991993)
          ·
            refine ⟨16721819599161846278993995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22295759465549128371991993 16721819599161846278993995)
            ·
              refine ⟨25082729398742769418490993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16721819599161846278993995 25082729398742769418490993)
              ·
                refine ⟨18812047049057077063868245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25082729398742769418490993 18812047049057077063868245)
                ·
                  refine ⟨110226838178068810921103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18812047049057077063868245 110226838178068810921103)
                  ·
                    rfl

theorem cell23_1931994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_1931994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1931994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1931994 prefixEnd_1931994 := by exact prefixLift 1931994
  have htrace : WordTrace (prefixWord ++ tailWord_1931994) baseStart_1931994 baseEnd_1931994 := by
    simpa [prefixWord, tailWord_1931994, baseEnd_1931994] using wordTrace_append hprefix tailTrace_1931994
  have hstable : (prefixWord ++ tailWord_1931994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931994).length < 2 ^ (prefixWord ++ tailWord_1931994).sum := by decide
  have hdescent : baseEnd_1931994 < baseStart_1931994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932001 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1932001 : Nat := 118140960795 + 1932001 * 2 ^ 59
def prefixEnd_1932001 : Nat := 4983230072969 + 3 ^ 40 * 1932001 * 2
def baseEnd_1932001 : Nat := 992045137967200770902395

theorem tailTrace_1932001 : CollatzResearch.WordTrace tailWord_1932001 prefixEnd_1932001 992045137967200770902395 := by
  unfold tailWord_1932001
  simp only [CollatzResearch.WordTrace]
  refine ⟨70465865473697811346491857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46977243649131874230994571 70465865473697811346491857)
  ·
    refine ⟨52849399105273358509868893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70465865473697811346491857 52849399105273358509868893)
    ·
      refine ⟨19818524664477509441200835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52849399105273358509868893 19818524664477509441200835)
      ·
        refine ⟨29727786996716264161801253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19818524664477509441200835 29727786996716264161801253)
        ·
          refine ⟨5573960061884299530337735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29727786996716264161801253 5573960061884299530337735)
          ·
            refine ⟨8360940092826449295506603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573960061884299530337735 8360940092826449295506603)
            ·
              refine ⟨12541410139239673943259905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360940092826449295506603 12541410139239673943259905)
              ·
                refine ⟨9406057604429755457444929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12541410139239673943259905 9406057604429755457444929)
                ·
                  refine ⟨7054543203322316593083697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9406057604429755457444929 7054543203322316593083697)
                  ·
                    refine ⟨5290907402491737444812773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054543203322316593083697 5290907402491737444812773)
                    ·
                      refine ⟨992045137967200770902395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5290907402491737444812773 992045137967200770902395)
                      ·
                        rfl

theorem cell23_1932001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1932001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932001 prefixEnd_1932001 := by exact prefixLift 1932001
  have htrace : WordTrace (prefixWord ++ tailWord_1932001) baseStart_1932001 baseEnd_1932001 := by
    simpa [prefixWord, tailWord_1932001, baseEnd_1932001] using wordTrace_append hprefix tailTrace_1932001
  have hstable : (prefixWord ++ tailWord_1932001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932001).length < 2 ^ (prefixWord ++ tailWord_1932001).sum := by decide
  have hdescent : baseEnd_1932001 < baseStart_1932001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932005 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1932005 : Nat := 118140960795 + 1932005 * 2 ^ 59
def prefixEnd_1932005 : Nat := 4983230072969 + 3 ^ 40 * 1932005 * 2
def baseEnd_1932005 : Nat := 992047191889818755252377

theorem tailTrace_1932005 : CollatzResearch.WordTrace tailWord_1932005 prefixEnd_1932005 992047191889818755252377 := by
  unfold tailWord_1932005
  simp only [CollatzResearch.WordTrace]
  refine ⟨70466011365683320029637469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46977340910455546686424979 70466011365683320029637469)
  ·
    refine ⟨26424754262131245011114051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70466011365683320029637469 26424754262131245011114051)
    ·
      refine ⟨39637131393196867516671077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26424754262131245011114051 39637131393196867516671077)
      ·
        refine ⟨7431962136224412659375827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39637131393196867516671077 7431962136224412659375827)
        ·
          refine ⟨11147943204336618989063741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431962136224412659375827 11147943204336618989063741)
          ·
            refine ⟨4180478701626232120898903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11147943204336618989063741 4180478701626232120898903)
            ·
              refine ⟨6270718052439348181348355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180478701626232120898903 6270718052439348181348355)
              ·
                refine ⟨9406077078659022272022533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270718052439348181348355 9406077078659022272022533)
                ·
                  refine ⟨1763639452248566676004225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9406077078659022272022533 1763639452248566676004225)
                  ·
                    refine ⟨1322729589186425007003169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763639452248566676004225 1322729589186425007003169)
                    ·
                      refine ⟨992047191889818755252377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322729589186425007003169 992047191889818755252377)
                      ·
                        rfl

theorem cell23_1932005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1932005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932005 prefixEnd_1932005 := by exact prefixLift 1932005
  have htrace : WordTrace (prefixWord ++ tailWord_1932005) baseStart_1932005 baseEnd_1932005 := by
    simpa [prefixWord, tailWord_1932005, baseEnd_1932005] using wordTrace_append hprefix tailTrace_1932005
  have hstable : (prefixWord ++ tailWord_1932005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932005).length < 2 ^ (prefixWord ++ tailWord_1932005).sum := by decide
  have hdescent : baseEnd_1932005 < baseStart_1932005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932024 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1932024 : Nat := 118140960795 + 1932024 * 2 ^ 59
def prefixEnd_1932024 : Nat := 4983230072969 + 3 ^ 40 * 1932024 * 2
def baseEnd_1932024 : Nat := 330685649340751393638263

theorem tailTrace_1932024 : CollatzResearch.WordTrace tailWord_1932024 prefixEnd_1932024 330685649340751393638263 := by
  unfold tailWord_1932024
  simp only [CollatzResearch.WordTrace]
  refine ⟨35233352176307243137289563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46977802901742990849719417 35233352176307243137289563)
  ·
    refine ⟨52850028264460864705934345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35233352176307243137289563 52850028264460864705934345)
    ·
      refine ⟨39637521198345648529450759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52850028264460864705934345 39637521198345648529450759)
      ·
        refine ⟨59456281797518472794176139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39637521198345648529450759 59456281797518472794176139)
        ·
          refine ⟨89184422696277709191264209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59456281797518472794176139 89184422696277709191264209)
          ·
            refine ⟨66888317022208281893448157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89184422696277709191264209 66888317022208281893448157)
            ·
              refine ⟨25083118883328105710043059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66888317022208281893448157 25083118883328105710043059)
              ·
                refine ⟨37624678324992158565064589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25083118883328105710043059 37624678324992158565064589)
                ·
                  refine ⟨14109254371872059461899221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37624678324992158565064589 14109254371872059461899221)
                  ·
                    refine ⟨330685649340751393638263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14109254371872059461899221 330685649340751393638263)
                    ·
                      rfl

theorem cell23_1932024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1932024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932024 prefixEnd_1932024 := by exact prefixLift 1932024
  have htrace : WordTrace (prefixWord ++ tailWord_1932024) baseStart_1932024 baseEnd_1932024 := by
    simpa [prefixWord, tailWord_1932024, baseEnd_1932024] using wordTrace_append hprefix tailTrace_1932024
  have hstable : (prefixWord ++ tailWord_1932024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932024).length < 2 ^ (prefixWord ++ tailWord_1932024).sum := by decide
  have hdescent : baseEnd_1932024 < baseStart_1932024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932068 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1932068 : Nat := 118140960795 + 1932068 * 2 ^ 59
def prefixEnd_1932068 : Nat := 4983230072969 + 3 ^ 40 * 1932068 * 2
def baseEnd_1932068 : Nat := 992079541171052008764587

theorem tailTrace_1932068 : CollatzResearch.WordTrace tailWord_1932068 prefixEnd_1932068 992079541171052008764587 := by
  unfold tailWord_1932068
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234154582227540894590429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46978872776303387859453905 35234154582227540894590429)
  ·
    refine ⟨13212807968335327835471411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35234154582227540894590429 13212807968335327835471411)
    ·
      refine ⟨19819211952502991753207117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212807968335327835471411 19819211952502991753207117)
      ·
        refine ⟨7432204482188621907452669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19819211952502991753207117 7432204482188621907452669)
        ·
          refine ⟨2787076680820733215294751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7432204482188621907452669 2787076680820733215294751)
          ·
            refine ⟨4180615021231099822942127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787076680820733215294751 4180615021231099822942127)
            ·
              refine ⟨6270922531846649734413191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180615021231099822942127 6270922531846649734413191)
              ·
                refine ⟨9406383797769974601619787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270922531846649734413191 9406383797769974601619787)
                ·
                  refine ⟨14109575696654961902429681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406383797769974601619787 14109575696654961902429681)
                  ·
                    refine ⟨10582181772491221426822261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14109575696654961902429681 10582181772491221426822261)
                    ·
                      refine ⟨992079541171052008764587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10582181772491221426822261 992079541171052008764587)
                      ·
                        rfl

theorem cell23_1932068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1932068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932068 prefixEnd_1932068 := by exact prefixLift 1932068
  have htrace : WordTrace (prefixWord ++ tailWord_1932068) baseStart_1932068 baseEnd_1932068 := by
    simpa [prefixWord, tailWord_1932068, baseEnd_1932068] using wordTrace_append hprefix tailTrace_1932068
  have hstable : (prefixWord ++ tailWord_1932068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932068).length < 2 ^ (prefixWord ++ tailWord_1932068).sum := by decide
  have hdescent : baseEnd_1932068 < baseStart_1932068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932122 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_1932122 : Nat := 118140960795 + 1932122 * 2 ^ 59
def prefixEnd_1932122 : Nat := 4983230072969 + 3 ^ 40 * 1932122 * 2
def baseEnd_1932122 : Nat := 330702423042131599163113

theorem tailTrace_1932122 : CollatzResearch.WordTrace tailWord_1932122 prefixEnd_1932122 330702423042131599163113 := by
  unfold tailWord_1932122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617569676564862252911655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46980185804172966007764413 17617569676564862252911655)
  ·
    refine ⟨26426354514847293379367483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17617569676564862252911655 26426354514847293379367483)
    ·
      refine ⟨39639531772270940069051225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26426354514847293379367483 39639531772270940069051225)
      ·
        refine ⟨29729648829203205051788419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39639531772270940069051225 29729648829203205051788419)
        ·
          refine ⟨44594473243804807577682629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29729648829203205051788419 44594473243804807577682629)
          ·
            refine ⟨8361463733213401420815493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44594473243804807577682629 8361463733213401420815493)
            ·
              refine ⟨1567774449977512766402905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8361463733213401420815493 1567774449977512766402905)
              ·
                refine ⟨1175830837483134574802179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567774449977512766402905 1175830837483134574802179)
                ·
                  refine ⟨1763746256224701862203269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175830837483134574802179 1763746256224701862203269)
                  ·
                    refine ⟨330702423042131599163113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763746256224701862203269 330702423042131599163113)
                    ·
                      rfl

theorem cell23_1932122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_1932122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932122 prefixEnd_1932122 := by exact prefixLift 1932122
  have htrace : WordTrace (prefixWord ++ tailWord_1932122) baseStart_1932122 baseEnd_1932122 := by
    simpa [prefixWord, tailWord_1932122, baseEnd_1932122] using wordTrace_append hprefix tailTrace_1932122
  have hstable : (prefixWord ++ tailWord_1932122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932122).length < 2 ^ (prefixWord ++ tailWord_1932122).sum := by decide
  have hdescent : baseEnd_1932122 < baseStart_1932122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932141 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1932141 : Nat := 118140960795 + 1932141 * 2 ^ 59
def prefixEnd_1932141 : Nat := 4983230072969 + 3 ^ 40 * 1932141 * 2
def baseEnd_1932141 : Nat := 992117025258830223151751

theorem tailTrace_1932141 : CollatzResearch.WordTrace tailWord_1932141 prefixEnd_1932141 992117025258830223151751 := by
  unfold tailWord_1932141
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470971693190615256588277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980647795460410171058851 70470971693190615256588277)
  ·
    refine ⟨6606653596236620180305151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70470971693190615256588277 6606653596236620180305151)
    ·
      refine ⟨9909980394354930270457727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606653596236620180305151 9909980394354930270457727)
      ·
        refine ⟨14864970591532395405686591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909980394354930270457727 14864970591532395405686591)
        ·
          refine ⟨22297455887298593108529887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864970591532395405686591 22297455887298593108529887)
          ·
            refine ⟨33446183830947889662794831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22297455887298593108529887 33446183830947889662794831)
            ·
              refine ⟨50169275746421834494192247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33446183830947889662794831 50169275746421834494192247)
              ·
                refine ⟨75253913619632751741288371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50169275746421834494192247 75253913619632751741288371)
                ·
                  refine ⟨112880870429449127611932557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75253913619632751741288371 112880870429449127611932557)
                  ·
                    refine ⟨42330326411043422854474709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112880870429449127611932557 42330326411043422854474709)
                    ·
                      refine ⟨992117025258830223151751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42330326411043422854474709 992117025258830223151751)
                      ·
                        rfl

theorem cell23_1932141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1932141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932141 prefixEnd_1932141 := by exact prefixLift 1932141
  have htrace : WordTrace (prefixWord ++ tailWord_1932141) baseStart_1932141 baseEnd_1932141 := by
    simpa [prefixWord, tailWord_1932141, baseEnd_1932141] using wordTrace_append hprefix tailTrace_1932141
  have hstable : (prefixWord ++ tailWord_1932141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932141).length < 2 ^ (prefixWord ++ tailWord_1932141).sum := by decide
  have hdescent : baseEnd_1932141 < baseStart_1932141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932145 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_1932145 : Nat := 118140960795 + 1932145 * 2 ^ 59
def prefixEnd_1932145 : Nat := 4983230072969 + 3 ^ 40 * 1932145 * 2
def baseEnd_1932145 : Nat := 992119079181448207501733

theorem tailTrace_1932145 : CollatzResearch.WordTrace tailWord_1932145 prefixEnd_1932145 992119079181448207501733 := by
  unfold tailWord_1932145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471117585176123939733889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980745056784082626489259 70471117585176123939733889)
  ·
    refine ⟨52853338188882092954800417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70471117585176123939733889 52853338188882092954800417)
    ·
      refine ⟨39640003641661569716100313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52853338188882092954800417 39640003641661569716100313)
      ·
        refine ⟨29730002731246177287075235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39640003641661569716100313 29730002731246177287075235)
        ·
          refine ⟨44595004096869265930612853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730002731246177287075235 44595004096869265930612853)
          ·
            refine ⟨4180781634081493680994955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44595004096869265930612853 4180781634081493680994955)
            ·
              refine ⟨6271172451122240521492433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180781634081493680994955 6271172451122240521492433)
              ·
                refine ⟨4703379338341680391119325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271172451122240521492433 4703379338341680391119325)
                ·
                  refine ⟨1763767251878130146669747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4703379338341680391119325 1763767251878130146669747)
                  ·
                    refine ⟨2645650877817195220004621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763767251878130146669747 2645650877817195220004621)
                    ·
                      refine ⟨992119079181448207501733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645650877817195220004621 992119079181448207501733)
                      ·
                        rfl

theorem cell23_1932145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_1932145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932145 prefixEnd_1932145 := by exact prefixLift 1932145
  have htrace : WordTrace (prefixWord ++ tailWord_1932145) baseStart_1932145 baseEnd_1932145 := by
    simpa [prefixWord, tailWord_1932145, baseEnd_1932145] using wordTrace_append hprefix tailTrace_1932145
  have hstable : (prefixWord ++ tailWord_1932145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932145).length < 2 ^ (prefixWord ++ tailWord_1932145).sum := by decide
  have hdescent : baseEnd_1932145 < baseStart_1932145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932155 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 2, 3, 2]
def baseStart_1932155 : Nat := 118140960795 + 1932155 * 2 ^ 59
def prefixEnd_1932155 : Nat := 4983230072969 + 3 ^ 40 * 1932155 * 2
def baseEnd_1932155 : Nat := 992124213987993168376687

theorem tailTrace_1932155 : CollatzResearch.WordTrace tailWord_1932155 prefixEnd_1932155 992124213987993168376687 := by
  unfold tailWord_1932155
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471482315139895647597919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980988210093263765065279 70471482315139895647597919)
  ·
    refine ⟨105707223472709843471396879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70471482315139895647597919 105707223472709843471396879)
    ·
      refine ⟨158560835209064765207095319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105707223472709843471396879 158560835209064765207095319)
      ·
        refine ⟨237841252813597147810642979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158560835209064765207095319 237841252813597147810642979)
        ·
          refine ⟨356761879220395721715964469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237841252813597147810642979 356761879220395721715964469)
          ·
            refine ⟨33446426176912098910871669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356761879220395721715964469 33446426176912098910871669)
            ·
              refine ⟨3135602454085509272894219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33446426176912098910871669 3135602454085509272894219)
              ·
                refine ⟨4703403681128263909341329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135602454085509272894219 4703403681128263909341329)
                ·
                  refine ⟨3527552760846197932005997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703403681128263909341329 3527552760846197932005997)
                  ·
                    refine ⟨1322832285317324224502249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527552760846197932005997 1322832285317324224502249)
                    ·
                      refine ⟨992124213987993168376687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322832285317324224502249 992124213987993168376687)
                      ·
                        rfl

theorem cell23_1932155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3, 2].length) (baseStart_1932155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932155 prefixEnd_1932155 := by exact prefixLift 1932155
  have htrace : WordTrace (prefixWord ++ tailWord_1932155) baseStart_1932155 baseEnd_1932155 := by
    simpa [prefixWord, tailWord_1932155, baseEnd_1932155] using wordTrace_append hprefix tailTrace_1932155
  have hstable : (prefixWord ++ tailWord_1932155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932155).length < 2 ^ (prefixWord ++ tailWord_1932155).sum := by decide
  have hdescent : baseEnd_1932155 < baseStart_1932155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932165 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_1932165 : Nat := 118140960795 + 1932165 * 2 ^ 59
def prefixEnd_1932165 : Nat := 4983230072969 + 3 ^ 40 * 1932165 * 2
def baseEnd_1932165 : Nat := 330709782931512709750547

theorem tailTrace_1932165 : CollatzResearch.WordTrace tailWord_1932165 prefixEnd_1932165 330709782931512709750547 := by
  unfold tailWord_1932165
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471847045103667355461949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46981231363402444903641299 70471847045103667355461949)
  ·
    refine ⟨26426942641913875258298231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70471847045103667355461949 26426942641913875258298231)
    ·
      refine ⟨39640413962870812887447347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26426942641913875258298231 39640413962870812887447347)
      ·
        refine ⟨59460620944306219331171021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39640413962870812887447347 59460620944306219331171021)
        ·
          refine ⟨22297732854114832249189133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59460620944306219331171021 22297732854114832249189133)
          ·
            refine ⟨8361649820293062093445925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22297732854114832249189133 8361649820293062093445925)
            ·
              refine ⟨1567809341304949142521111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8361649820293062093445925 1567809341304949142521111)
              ·
                refine ⟨2351714011957423713781667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567809341304949142521111 2351714011957423713781667)
                ·
                  refine ⟨3527571017936135570672501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351714011957423713781667 3527571017936135570672501)
                  ·
                    refine ⟨330709782931512709750547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3527571017936135570672501 330709782931512709750547)
                    ·
                      rfl

theorem cell23_1932165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_1932165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932165 prefixEnd_1932165 := by exact prefixLift 1932165
  have htrace : WordTrace (prefixWord ++ tailWord_1932165) baseStart_1932165 baseEnd_1932165 := by
    simpa [prefixWord, tailWord_1932165, baseEnd_1932165] using wordTrace_append hprefix tailTrace_1932165
  have hstable : (prefixWord ++ tailWord_1932165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932165).length < 2 ^ (prefixWord ++ tailWord_1932165).sum := by decide
  have hdescent : baseEnd_1932165 < baseStart_1932165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932212 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1932212 : Nat := 118140960795 + 1932212 * 2 ^ 59
def prefixEnd_1932212 : Nat := 4983230072969 + 3 ^ 40 * 1932212 * 2
def baseEnd_1932212 : Nat := 330717827461766481787975

theorem tailTrace_1932212 : CollatzResearch.WordTrace tailWord_1932212 prefixEnd_1932212 330717827461766481787975 := by
  unfold tailWord_1932212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35236780637966697191211445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46982374183955596254948593 35236780637966697191211445)
  ·
    refine ⟨3303448184809377861676073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35236780637966697191211445 3303448184809377861676073)
    ·
      refine ⟨2477586138607033396257055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3303448184809377861676073 2477586138607033396257055)
      ·
        refine ⟨3716379207910550094385583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477586138607033396257055 3716379207910550094385583)
        ·
          refine ⟨5574568811865825141578375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716379207910550094385583 5574568811865825141578375)
          ·
            refine ⟨8361853217798737712367563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574568811865825141578375 8361853217798737712367563)
            ·
              refine ⟨12542779826698106568551345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8361853217798737712367563 12542779826698106568551345)
              ·
                refine ⟨9407084870023579926413509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12542779826698106568551345 9407084870023579926413509)
                ·
                  refine ⟨1763828413129421236202533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9407084870023579926413509 1763828413129421236202533)
                  ·
                    refine ⟨330717827461766481787975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763828413129421236202533 330717827461766481787975)
                    ·
                      rfl

theorem cell23_1932212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1932212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932212 prefixEnd_1932212 := by exact prefixLift 1932212
  have htrace : WordTrace (prefixWord ++ tailWord_1932212) baseStart_1932212 baseEnd_1932212 := by
    simpa [prefixWord, tailWord_1932212, baseEnd_1932212] using wordTrace_append hprefix tailTrace_1932212
  have hstable : (prefixWord ++ tailWord_1932212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932212).length < 2 ^ (prefixWord ++ tailWord_1932212).sum := by decide
  have hdescent : baseEnd_1932212 < baseStart_1932212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932218 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1932218 : Nat := 118140960795 + 1932218 * 2 ^ 59
def prefixEnd_1932218 : Nat := 4983230072969 + 3 ^ 40 * 1932218 * 2
def baseEnd_1932218 : Nat := 992156563269226421888897

theorem tailTrace_1932218 : CollatzResearch.WordTrace tailWord_1932218 prefixEnd_1932218 992156563269226421888897 := by
  unfold tailWord_1932218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618445028477914351785327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46982520075941104938094205 17618445028477914351785327)
  ·
    refine ⟨26427667542716871527677991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618445028477914351785327 26427667542716871527677991)
    ·
      refine ⟨39641501314075307291516987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26427667542716871527677991 39641501314075307291516987)
      ·
        refine ⟨59462251971112960937275481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39641501314075307291516987 59462251971112960937275481)
        ·
          refine ⟨44596688978334720702956611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59462251971112960937275481 44596688978334720702956611)
          ·
            refine ⟨66895033467502081054434917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44596688978334720702956611 66895033467502081054434917)
            ·
              refine ⟨12542818775156640197706547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66895033467502081054434917 12542818775156640197706547)
              ·
                refine ⟨18814228162734960296559821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542818775156640197706547 18814228162734960296559821)
                ·
                  refine ⟨7055335561025610111209933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18814228162734960296559821 7055335561025610111209933)
                  ·
                    refine ⟨2645750835384603791703725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7055335561025610111209933 2645750835384603791703725)
                    ·
                      refine ⟨992156563269226421888897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645750835384603791703725 992156563269226421888897)
                      ·
                        rfl

theorem cell23_1932218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1932218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932218 prefixEnd_1932218 := by exact prefixLift 1932218
  have htrace : WordTrace (prefixWord ++ tailWord_1932218) baseStart_1932218 baseEnd_1932218 := by
    simpa [prefixWord, tailWord_1932218, baseEnd_1932218] using wordTrace_append hprefix tailTrace_1932218
  have hstable : (prefixWord ++ tailWord_1932218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932218).length < 2 ^ (prefixWord ++ tailWord_1932218).sum := by decide
  have hdescent : baseEnd_1932218 < baseStart_1932218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932230 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1932230 : Nat := 118140960795 + 1932230 * 2 ^ 59
def prefixEnd_1932230 : Nat := 4983230072969 + 3 ^ 40 * 1932230 * 2
def baseEnd_1932230 : Nat := 992162725037080374938843

theorem tailTrace_1932230 : CollatzResearch.WordTrace tailWord_1932230 prefixEnd_1932230 992162725037080374938843 := by
  unfold tailWord_1932230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202319305933380733018067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46982811859912122304385429 2202319305933380733018067)
  ·
    refine ⟨3303478958900071099527101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202319305933380733018067 3303478958900071099527101)
    ·
      refine ⟨1238804609587526662322663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3303478958900071099527101 1238804609587526662322663)
      ·
        refine ⟨1858206914381289993483995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238804609587526662322663 1858206914381289993483995)
        ·
          refine ⟨2787310371571934990225993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858206914381289993483995 2787310371571934990225993)
          ·
            refine ⟨2090482778678951242669495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787310371571934990225993 2090482778678951242669495)
            ·
              refine ⟨3135724168018426864004243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090482778678951242669495 3135724168018426864004243)
              ·
                refine ⟨4703586252027640296006365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135724168018426864004243 4703586252027640296006365)
                ·
                  refine ⟨1763844844510365111002387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4703586252027640296006365 1763844844510365111002387)
                  ·
                    refine ⟨2645767266765547666503581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763844844510365111002387 2645767266765547666503581)
                    ·
                      refine ⟨992162725037080374938843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645767266765547666503581 992162725037080374938843)
                      ·
                        rfl

theorem cell23_1932230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1932230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932230 prefixEnd_1932230 := by exact prefixLift 1932230
  have htrace : WordTrace (prefixWord ++ tailWord_1932230) baseStart_1932230 baseEnd_1932230 := by
    simpa [prefixWord, tailWord_1932230, baseEnd_1932230] using wordTrace_append hprefix tailTrace_1932230
  have hstable : (prefixWord ++ tailWord_1932230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932230).length < 2 ^ (prefixWord ++ tailWord_1932230).sum := by decide
  have hdescent : baseEnd_1932230 < baseStart_1932230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932235 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 3]
def baseStart_1932235 : Nat := 118140960795 + 1932235 * 2 ^ 59
def prefixEnd_1932235 : Nat := 4983230072969 + 3 ^ 40 * 1932235 * 2
def baseEnd_1932235 : Nat := 992165292440352855376319

theorem tailTrace_1932235 : CollatzResearch.WordTrace tailWord_1932235 prefixEnd_1932235 992165292440352855376319 := by
  unfold tailWord_1932235
  simp only [CollatzResearch.WordTrace]
  refine ⟨70474400154850069310510159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46982933436566712873673439 70474400154850069310510159)
  ·
    refine ⟨105711600232275103965765239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70474400154850069310510159 105711600232275103965765239)
    ·
      refine ⟨158567400348412655948647859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105711600232275103965765239 158567400348412655948647859)
      ·
        refine ⟨237851100522618983922971789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158567400348412655948647859 237851100522618983922971789)
        ·
          refine ⟨89194162695982118971114421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237851100522618983922971789 89194162695982118971114421)
          ·
            refine ⟨8361952752748323653541977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89194162695982118971114421 8361952752748323653541977)
            ·
              refine ⟨6271464564561242740156483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361952752748323653541977 6271464564561242740156483)
              ·
                refine ⟨9407196846841864110234725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271464564561242740156483 9407196846841864110234725)
                ·
                  refine ⟨1763849408782849520669011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9407196846841864110234725 1763849408782849520669011)
                  ·
                    refine ⟨2645774113174274281003517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763849408782849520669011 2645774113174274281003517)
                    ·
                      refine ⟨992165292440352855376319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645774113174274281003517 992165292440352855376319)
                      ·
                        rfl

theorem cell23_1932235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 3].length) (baseStart_1932235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932235 prefixEnd_1932235 := by exact prefixLift 1932235
  have htrace : WordTrace (prefixWord ++ tailWord_1932235) baseStart_1932235 baseEnd_1932235 := by
    simpa [prefixWord, tailWord_1932235, baseEnd_1932235] using wordTrace_append hprefix tailTrace_1932235
  have hstable : (prefixWord ++ tailWord_1932235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932235).length < 2 ^ (prefixWord ++ tailWord_1932235).sum := by decide
  have hdescent : baseEnd_1932235 < baseStart_1932235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932236 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1932236 : Nat := 118140960795 + 1932236 * 2 ^ 59
def prefixEnd_1932236 : Nat := 4983230072969 + 3 ^ 40 * 1932236 * 2
def baseEnd_1932236 : Nat := 992165805921007351463815

theorem tailTrace_1932236 : CollatzResearch.WordTrace tailWord_1932236 prefixEnd_1932236 992165805921007351463815 := by
  unfold tailWord_1932236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35237218313923223240648281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46982957751897630987531041 35237218313923223240648281)
  ·
    refine ⟨26427913735442417430486211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35237218313923223240648281 26427913735442417430486211)
    ·
      refine ⟨39641870603163626145729317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26427913735442417430486211 39641870603163626145729317)
      ·
        refine ⟨7432850738093179902324247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39641870603163626145729317 7432850738093179902324247)
        ·
          refine ⟨11149276107139769853486371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432850738093179902324247 11149276107139769853486371)
          ·
            refine ⟨16723914160709654780229557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149276107139769853486371 16723914160709654780229557)
            ·
              refine ⟨1567866952566530135646521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16723914160709654780229557 1567866952566530135646521)
              ·
                refine ⟨1175900214424897601734891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567866952566530135646521 1175900214424897601734891)
                ·
                  refine ⟨1763850321637346402602337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175900214424897601734891 1763850321637346402602337)
                  ·
                    refine ⟨1322887741228009801951753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763850321637346402602337 1322887741228009801951753)
                    ·
                      refine ⟨992165805921007351463815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322887741228009801951753 992165805921007351463815)
                      ·
                        rfl

theorem cell23_1932236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1932236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932236 prefixEnd_1932236 := by exact prefixLift 1932236
  have htrace : WordTrace (prefixWord ++ tailWord_1932236) baseStart_1932236 baseEnd_1932236 := by
    simpa [prefixWord, tailWord_1932236, baseEnd_1932236] using wordTrace_append hprefix tailTrace_1932236
  have hstable : (prefixWord ++ tailWord_1932236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932236).length < 2 ^ (prefixWord ++ tailWord_1932236).sum := by decide
  have hdescent : baseEnd_1932236 < baseStart_1932236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932246 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1932246 : Nat := 118140960795 + 1932246 * 2 ^ 59
def prefixEnd_1932246 : Nat := 4983230072969 + 3 ^ 40 * 1932246 * 2
def baseEnd_1932246 : Nat := 330723646909184104112923

theorem tailTrace_1932246 : CollatzResearch.WordTrace tailWord_1932246 prefixEnd_1932246 330723646909184104112923 := by
  unfold tailWord_1932246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404675084863138636822537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46983200905206812126107061 4404675084863138636822537)
  ·
    refine ⟨3303506313647353977616903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4404675084863138636822537 3303506313647353977616903)
    ·
      refine ⟨4955259470471030966425355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303506313647353977616903 4955259470471030966425355)
      ·
        refine ⟨7432889205706546449638033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955259470471030966425355 7432889205706546449638033)
        ·
          refine ⟨5574666904279909837228525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7432889205706546449638033 5574666904279909837228525)
          ·
            refine ⟨2090500089104966188960697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5574666904279909837228525 2090500089104966188960697)
            ·
              refine ⟨1567875066828724641720523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090500089104966188960697 1567875066828724641720523)
              ·
                refine ⟨2351812600243086962580785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567875066828724641720523 2351812600243086962580785)
                ·
                  refine ⟨1763859450182315221935589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351812600243086962580785 1763859450182315221935589)
                  ·
                    refine ⟨330723646909184104112923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763859450182315221935589 330723646909184104112923)
                    ·
                      rfl

theorem cell23_1932246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1932246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932246 prefixEnd_1932246 := by exact prefixLift 1932246
  have htrace : WordTrace (prefixWord ++ tailWord_1932246) baseStart_1932246 baseEnd_1932246 := by
    simpa [prefixWord, tailWord_1932246, baseEnd_1932246] using wordTrace_append hprefix tailTrace_1932246
  have hstable : (prefixWord ++ tailWord_1932246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932246).length < 2 ^ (prefixWord ++ tailWord_1932246).sum := by decide
  have hdescent : baseEnd_1932246 < baseStart_1932246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932286 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1932286 : Nat := 118140960795 + 1932286 * 2 ^ 59
def prefixEnd_1932286 : Nat := 4983230072969 + 3 ^ 40 * 1932286 * 2
def baseEnd_1932286 : Nat := 992191479953732155838585

theorem tailTrace_1932286 : CollatzResearch.WordTrace tailWord_1932286 prefixEnd_1932286 992191479953732155838585 := by
  unfold tailWord_1932286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809532534708163127577089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46984173518443536680411141 8809532534708163127577089)
  ·
    refine ⟨6607149401031122345682817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8809532534708163127577089 6607149401031122345682817)
    ·
      refine ⟨4955362050773341759262113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6607149401031122345682817 4955362050773341759262113)
      ·
        refine ⟨3716521538080006319446585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4955362050773341759262113 3716521538080006319446585)
        ·
          refine ⟨2787391153560004739584939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716521538080006319446585 2787391153560004739584939)
          ·
            refine ⟨4181086730340007109377409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787391153560004739584939 4181086730340007109377409)
            ·
              refine ⟨3135815047755005332033057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181086730340007109377409 3135815047755005332033057)
              ·
                refine ⟨2351861285816253999024793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135815047755005332033057 2351861285816253999024793)
                ·
                  refine ⟨1763895964362190499268595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351861285816253999024793 1763895964362190499268595)
                  ·
                    refine ⟨2645843946543285748902893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1763895964362190499268595 2645843946543285748902893)
                    ·
                      refine ⟨992191479953732155838585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645843946543285748902893 992191479953732155838585)
                      ·
                        rfl

theorem cell23_1932286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1932286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932286 prefixEnd_1932286 := by exact prefixLift 1932286
  have htrace : WordTrace (prefixWord ++ tailWord_1932286) baseStart_1932286 baseEnd_1932286 := by
    simpa [prefixWord, tailWord_1932286, baseEnd_1932286] using wordTrace_append hprefix tailTrace_1932286
  have hstable : (prefixWord ++ tailWord_1932286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932286).length < 2 ^ (prefixWord ++ tailWord_1932286).sum := by decide
  have hdescent : baseEnd_1932286 < baseStart_1932286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932309 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_1932309 : Nat := 118140960795 + 1932309 * 2 ^ 59
def prefixEnd_1932309 : Nat := 4983230072969 + 3 ^ 40 * 1932309 * 2
def baseEnd_1932309 : Nat := 992203290008785565850979

theorem tailTrace_1932309 : CollatzResearch.WordTrace tailWord_1932309 prefixEnd_1932309 992203290008785565850979 := by
  unfold tailWord_1932309
  simp only [CollatzResearch.WordTrace]
  refine ⟨70477099156581979948703981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46984732771054653299135987 70477099156581979948703981)
  ·
    refine ⟨26428912183718242480763993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70477099156581979948703981 26428912183718242480763993)
    ·
      refine ⟨19821684137788681860572995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26428912183718242480763993 19821684137788681860572995)
      ·
        refine ⟨29732526206683022790859493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19821684137788681860572995 29732526206683022790859493)
        ·
          refine ⟨5574848663753066773286155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29732526206683022790859493 5574848663753066773286155)
          ·
            refine ⟨8362272995629600159929233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574848663753066773286155 8362272995629600159929233)
            ·
              refine ⟨6271704746722200119946925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362272995629600159929233 6271704746722200119946925)
              ·
                refine ⟨2351889280020825044980097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6271704746722200119946925 2351889280020825044980097)
                ·
                  refine ⟨1763916960015618783735073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351889280020825044980097 1763916960015618783735073)
                  ·
                    refine ⟨1322937720011714087801305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763916960015618783735073 1322937720011714087801305)
                    ·
                      refine ⟨992203290008785565850979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1322937720011714087801305 992203290008785565850979)
                      ·
                        rfl

theorem cell23_1932309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_1932309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932309 prefixEnd_1932309 := by exact prefixLift 1932309
  have htrace : WordTrace (prefixWord ++ tailWord_1932309) baseStart_1932309 baseEnd_1932309 := by
    simpa [prefixWord, tailWord_1932309, baseEnd_1932309] using wordTrace_append hprefix tailTrace_1932309
  have hstable : (prefixWord ++ tailWord_1932309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932309).length < 2 ^ (prefixWord ++ tailWord_1932309).sum := by decide
  have hdescent : baseEnd_1932309 < baseStart_1932309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932342 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1932342 : Nat := 118140960795 + 1932342 * 2 ^ 59
def prefixEnd_1932342 : Nat := 4983230072969 + 3 ^ 40 * 1932342 * 2
def baseEnd_1932342 : Nat := 992220234870383936738327

theorem tailTrace_1932342 : CollatzResearch.WordTrace tailWord_1932342 prefixEnd_1932342 992220234870383936738327 := by
  unfold tailWord_1932342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404893922841401661540955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46985535176974951056436853 4404893922841401661540955)
  ·
    refine ⟨6607340884262102492311433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4404893922841401661540955 6607340884262102492311433)
    ·
      refine ⟨4955505663196576869233575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6607340884262102492311433 4955505663196576869233575)
      ·
        refine ⟨7433258494794865303850363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955505663196576869233575 7433258494794865303850363)
        ·
          refine ⟨11149887742192297955775545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433258494794865303850363 11149887742192297955775545)
          ·
            refine ⟨8362415806644223466831659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11149887742192297955775545 8362415806644223466831659)
            ·
              refine ⟨12543623709966335200247489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362415806644223466831659 12543623709966335200247489)
              ·
                refine ⟨9407717782474751400185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12543623709966335200247489 9407717782474751400185617)
                ·
                  refine ⟨7055788336856063550139213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407717782474751400185617 7055788336856063550139213)
                  ·
                    refine ⟨2645920626321023831302205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7055788336856063550139213 2645920626321023831302205)
                    ·
                      refine ⟨992220234870383936738327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645920626321023831302205 992220234870383936738327)
                      ·
                        rfl

theorem cell23_1932342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1932342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932342 prefixEnd_1932342 := by exact prefixLift 1932342
  have htrace : WordTrace (prefixWord ++ tailWord_1932342) baseStart_1932342 baseEnd_1932342 := by
    simpa [prefixWord, tailWord_1932342, baseEnd_1932342] using wordTrace_append hprefix tailTrace_1932342
  have hstable : (prefixWord ++ tailWord_1932342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932342).length < 2 ^ (prefixWord ++ tailWord_1932342).sum := by decide
  have hdescent : baseEnd_1932342 < baseStart_1932342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932378 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1932378 : Nat := 118140960795 + 1932378 * 2 ^ 59
def prefixEnd_1932378 : Nat := 4983230072969 + 3 ^ 40 * 1932378 * 2
def baseEnd_1932378 : Nat := 992238720173945795888161

theorem tailTrace_1932378 : CollatzResearch.WordTrace tailWord_1932378 prefixEnd_1932378 992238720173945795888161 := by
  unfold tailWord_1932378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619903948333001183241447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46986410528888003155310525 17619903948333001183241447)
  ·
    refine ⟨26429855922499501774862171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619903948333001183241447 26429855922499501774862171)
    ·
      refine ⟨39644783883749252662293257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26429855922499501774862171 39644783883749252662293257)
      ·
        refine ⟨29733587912811939496719943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39644783883749252662293257 29733587912811939496719943)
        ·
          refine ⟨44600381869217909245079915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29733587912811939496719943 44600381869217909245079915)
          ·
            refine ⟨66900572803826863867619873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44600381869217909245079915 66900572803826863867619873)
            ·
              refine ⟨50175429602870147900714905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66900572803826863867619873 50175429602870147900714905)
              ·
                refine ⟨37631572202152610925536179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50175429602870147900714905 37631572202152610925536179)
                ·
                  refine ⟨56447358303228916388304269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37631572202152610925536179 56447358303228916388304269)
                  ·
                    refine ⟨21167759363710843645614101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56447358303228916388304269 21167759363710843645614101)
                    ·
                      refine ⟨992238720173945795888161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21167759363710843645614101 992238720173945795888161)
                      ·
                        rfl

theorem cell23_1932378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1932378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932378 prefixEnd_1932378 := by exact prefixLift 1932378
  have htrace : WordTrace (prefixWord ++ tailWord_1932378) baseStart_1932378 baseEnd_1932378 := by
    simpa [prefixWord, tailWord_1932378, baseEnd_1932378] using wordTrace_append hprefix tailTrace_1932378
  have hstable : (prefixWord ++ tailWord_1932378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932378).length < 2 ^ (prefixWord ++ tailWord_1932378).sum := by decide
  have hdescent : baseEnd_1932378 < baseStart_1932378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932385 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1932385 : Nat := 118140960795 + 1932385 * 2 ^ 59
def prefixEnd_1932385 : Nat := 4983230072969 + 3 ^ 40 * 1932385 * 2
def baseEnd_1932385 : Nat := 992242314538527268500629

theorem tailTrace_1932385 : CollatzResearch.WordTrace tailWord_1932385 prefixEnd_1932385 992242314538527268500629 := by
  unfold tailWord_1932385
  simp only [CollatzResearch.WordTrace]
  refine ⟨70479871104306644928470609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46986580736204429952313739 70479871104306644928470609)
  ·
    refine ⟨52859903328229983696352957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70479871104306644928470609 52859903328229983696352957)
    ·
      refine ⟨19822463748086243886132359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52859903328229983696352957 19822463748086243886132359)
      ·
        refine ⟨29733695622129365829198539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19822463748086243886132359 29733695622129365829198539)
        ·
          refine ⟨44600543433194048743797809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29733695622129365829198539 44600543433194048743797809)
          ·
            refine ⟨33450407574895536557848357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44600543433194048743797809 33450407574895536557848357)
            ·
              refine ⟨6271951420292913104596567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33450407574895536557848357 6271951420292913104596567)
              ·
                refine ⟨9407927130439369656894851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271951420292913104596567 9407927130439369656894851)
                ·
                  refine ⟨14111890695659054485342277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407927130439369656894851 14111890695659054485342277)
                  ·
                    refine ⟨2645979505436072716001677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14111890695659054485342277 2645979505436072716001677)
                    ·
                      refine ⟨992242314538527268500629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2645979505436072716001677 992242314538527268500629)
                      ·
                        rfl

theorem cell23_1932385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1932385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932385 prefixEnd_1932385 := by exact prefixLift 1932385
  have htrace : WordTrace (prefixWord ++ tailWord_1932385) baseStart_1932385 baseEnd_1932385 := by
    simpa [prefixWord, tailWord_1932385, baseEnd_1932385] using wordTrace_append hprefix tailTrace_1932385
  have hstable : (prefixWord ++ tailWord_1932385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932385).length < 2 ^ (prefixWord ++ tailWord_1932385).sum := by decide
  have hdescent : baseEnd_1932385 < baseStart_1932385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932402 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1932402 : Nat := 118140960795 + 1932402 * 2 ^ 59
def prefixEnd_1932402 : Nat := 4983230072969 + 3 ^ 40 * 1932402 * 2
def baseEnd_1932402 : Nat := 992251043709653701988051

theorem tailTrace_1932402 : CollatzResearch.WordTrace tailWord_1932402 prefixEnd_1932402 992251043709653701988051 := by
  unfold tailWord_1932402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620122786311264207959865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46986994096830037887892973 17620122786311264207959865)
  ·
    refine ⟨13215092089733448155969899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17620122786311264207959865 13215092089733448155969899)
    ·
      refine ⟨19822638134600172233954849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215092089733448155969899 19822638134600172233954849)
      ·
        refine ⟨14866978600950129175466137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19822638134600172233954849 14866978600950129175466137)
        ·
          refine ⟨11150233950712596881599603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14866978600950129175466137 11150233950712596881599603)
          ·
            refine ⟨16725350926068895322399405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11150233950712596881599603 16725350926068895322399405)
            ·
              refine ⟨6272006597275835745899777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16725350926068895322399405 6272006597275835745899777)
              ·
                refine ⟨4704004947956876809424833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272006597275835745899777 4704004947956876809424833)
                ·
                  refine ⟨3528003710967657607068625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704004947956876809424833 3528003710967657607068625)
                  ·
                    refine ⟨2646002783225743205301469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528003710967657607068625 2646002783225743205301469)
                    ·
                      refine ⟨992251043709653701988051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646002783225743205301469 992251043709653701988051)
                      ·
                        rfl

theorem cell23_1932402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1932402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932402 prefixEnd_1932402 := by exact prefixLift 1932402
  have htrace : WordTrace (prefixWord ++ tailWord_1932402) baseStart_1932402 baseEnd_1932402 := by
    simpa [prefixWord, tailWord_1932402, baseEnd_1932402] using wordTrace_append hprefix tailTrace_1932402
  have hstable : (prefixWord ++ tailWord_1932402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932402).length < 2 ^ (prefixWord ++ tailWord_1932402).sum := by decide
  have hdescent : baseEnd_1932402 < baseStart_1932402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932408 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1932408 : Nat := 118140960795 + 1932408 * 2 ^ 59
def prefixEnd_1932408 : Nat := 4983230072969 + 3 ^ 40 * 1932408 * 2
def baseEnd_1932408 : Nat := 992254124593580678513023

theorem tailTrace_1932408 : CollatzResearch.WordTrace tailWord_1932408 prefixEnd_1932408 992254124593580678513023 := by
  unfold tailWord_1932408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35240354991611659928278939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46987139988815546571038585 35240354991611659928278939)
  ·
    refine ⟨52860532487417489892418409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35240354991611659928278939 52860532487417489892418409)
    ·
      refine ⟨39645399365563117419313807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52860532487417489892418409 39645399365563117419313807)
      ·
        refine ⟨59468099048344676128970711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39645399365563117419313807 59468099048344676128970711)
        ·
          refine ⟨89202148572517014193456067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59468099048344676128970711 89202148572517014193456067)
          ·
            refine ⟨133803222858775521290184101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89202148572517014193456067 133803222858775521290184101)
            ·
              refine ⟨25088104286020410241909519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133803222858775521290184101 25088104286020410241909519)
              ·
                refine ⟨37632156429030615362864279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25088104286020410241909519 37632156429030615362864279)
                ·
                  refine ⟨56448234643545923044296419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37632156429030615362864279 56448234643545923044296419)
                  ·
                    refine ⟨84672351965318884566444629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56448234643545923044296419 84672351965318884566444629)
                    ·
                      refine ⟨992254124593580678513023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84672351965318884566444629 992254124593580678513023)
                      ·
                        rfl

theorem cell23_1932408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1932408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932408 prefixEnd_1932408 := by exact prefixLift 1932408
  have htrace : WordTrace (prefixWord ++ tailWord_1932408) baseStart_1932408 baseEnd_1932408 := by
    simpa [prefixWord, tailWord_1932408, baseEnd_1932408] using wordTrace_append hprefix tailTrace_1932408
  have hstable : (prefixWord ++ tailWord_1932408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932408).length < 2 ^ (prefixWord ++ tailWord_1932408).sum := by decide
  have hdescent : baseEnd_1932408 < baseStart_1932408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932409 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_1932409 : Nat := 118140960795 + 1932409 * 2 ^ 59
def prefixEnd_1932409 : Nat := 4983230072969 + 3 ^ 40 * 1932409 * 2
def baseEnd_1932409 : Nat := 330751546024745058200173

theorem tailTrace_1932409 : CollatzResearch.WordTrace tailWord_1932409 prefixEnd_1932409 330751546024745058200173 := by
  unfold tailWord_1932409
  simp only [CollatzResearch.WordTrace]
  refine ⟨70480746456219697027344281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46987164304146464684896187 70480746456219697027344281)
  ·
    refine ⟨52860559842164772770508211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70480746456219697027344281 52860559842164772770508211)
    ·
      refine ⟨79290839763247159155762317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52860559842164772770508211 79290839763247159155762317)
      ·
        refine ⟨29734064911217684683410869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79290839763247159155762317 29734064911217684683410869)
        ·
          refine ⟨2787568585426657939069769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29734064911217684683410869 2787568585426657939069769)
          ·
            refine ⟨2090676439069993454302327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787568585426657939069769 2090676439069993454302327)
            ·
              refine ⟨3136014658604990181453491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090676439069993454302327 3136014658604990181453491)
              ·
                refine ⟨4704021987907485272180237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136014658604990181453491 4704021987907485272180237)
                ·
                  refine ⟨1764008245465306977067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4704021987907485272180237 1764008245465306977067589)
                  ·
                    refine ⟨330751546024745058200173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1764008245465306977067589 330751546024745058200173)
                    ·
                      rfl

theorem cell23_1932409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_1932409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932409 prefixEnd_1932409 := by exact prefixLift 1932409
  have htrace : WordTrace (prefixWord ++ tailWord_1932409) baseStart_1932409 baseEnd_1932409 := by
    simpa [prefixWord, tailWord_1932409, baseEnd_1932409] using wordTrace_append hprefix tailTrace_1932409
  have hstable : (prefixWord ++ tailWord_1932409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932409).length < 2 ^ (prefixWord ++ tailWord_1932409).sum := by decide
  have hdescent : baseEnd_1932409 < baseStart_1932409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932466 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_1932466 : Nat := 118140960795 + 1932466 * 2 ^ 59
def prefixEnd_1932466 : Nat := 4983230072969 + 3 ^ 40 * 1932466 * 2
def baseEnd_1932466 : Nat := 992283906471541451587757

theorem tailTrace_1932466 : CollatzResearch.WordTrace tailWord_1932466 prefixEnd_1932466 992283906471541451587757 := by
  unfold tailWord_1932466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620706354253298940542313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46988550278008797174779501 17620706354253298940542313)
  ·
    refine ⟨13215529765689974205406735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17620706354253298940542313 13215529765689974205406735)
    ·
      refine ⟨19823294648534961308110103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215529765689974205406735 19823294648534961308110103)
      ·
        refine ⟨29734941972802441962165155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823294648534961308110103 29734941972802441962165155)
        ·
          refine ⟨44602412959203662943247733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29734941972802441962165155 44602412959203662943247733)
          ·
            refine ⟨4181476214925343400929475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44602412959203662943247733 4181476214925343400929475)
            ·
              refine ⟨6272214322388015101394213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181476214925343400929475 6272214322388015101394213)
              ·
                refine ⟨1176040185447752831511415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6272214322388015101394213 1176040185447752831511415)
                ·
                  refine ⟨1764060278171629247267123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176040185447752831511415 1764060278171629247267123)
                  ·
                    refine ⟨2646090417257443870900685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764060278171629247267123 2646090417257443870900685)
                    ·
                      refine ⟨992283906471541451587757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646090417257443870900685 992283906471541451587757)
                      ·
                        rfl

theorem cell23_1932466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_1932466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932466 prefixEnd_1932466 := by exact prefixLift 1932466
  have htrace : WordTrace (prefixWord ++ tailWord_1932466) baseStart_1932466 baseEnd_1932466 := by
    simpa [prefixWord, tailWord_1932466, baseEnd_1932466] using wordTrace_append hprefix tailTrace_1932466
  have hstable : (prefixWord ++ tailWord_1932466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932466).length < 2 ^ (prefixWord ++ tailWord_1932466).sum := by decide
  have hdescent : baseEnd_1932466 < baseStart_1932466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932493 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1932493 : Nat := 118140960795 + 1932493 * 2 ^ 59
def prefixEnd_1932493 : Nat := 4983230072969 + 3 ^ 40 * 1932493 * 2
def baseEnd_1932493 : Nat := 992297770449212845950133

theorem tailTrace_1932493 : CollatzResearch.WordTrace tailWord_1932493 prefixEnd_1932493 992297770449212845950133 := by
  unfold tailWord_1932493
  simp only [CollatzResearch.WordTrace]
  refine ⟨70483810187915379373402133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46989206791943586248934755 70483810187915379373402133)
  ·
    refine ⟨3303928602558533408128225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70483810187915379373402133 3303928602558533408128225)
    ·
      refine ⟨2477946451918900056096169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3303928602558533408128225 2477946451918900056096169)
      ·
        refine ⟨1858459838939175042072127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477946451918900056096169 1858459838939175042072127)
        ·
          refine ⟨2787689758408762563108191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858459838939175042072127 2787689758408762563108191)
          ·
            refine ⟨4181534637613143844662287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787689758408762563108191 4181534637613143844662287)
            ·
              refine ⟨6272301956419715766993431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181534637613143844662287 6272301956419715766993431)
              ·
                refine ⟨9408452934629573650490147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272301956419715766993431 9408452934629573650490147)
                ·
                  refine ⟨14112679401944360475735221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408452934629573650490147 14112679401944360475735221)
                  ·
                    refine ⟨1323063693932283794600177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14112679401944360475735221 1323063693932283794600177)
                    ·
                      refine ⟨992297770449212845950133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323063693932283794600177 992297770449212845950133)
                      ·
                        rfl

theorem cell23_1932493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1932493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932493 prefixEnd_1932493 := by exact prefixLift 1932493
  have htrace : WordTrace (prefixWord ++ tailWord_1932493) baseStart_1932493 baseEnd_1932493 := by
    simpa [prefixWord, tailWord_1932493, baseEnd_1932493] using wordTrace_append hprefix tailTrace_1932493
  have hstable : (prefixWord ++ tailWord_1932493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932493).length < 2 ^ (prefixWord ++ tailWord_1932493).sum := by decide
  have hdescent : baseEnd_1932493 < baseStart_1932493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932500 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1932500 : Nat := 118140960795 + 1932500 * 2 ^ 59
def prefixEnd_1932500 : Nat := 4983230072969 + 3 ^ 40 * 1932500 * 2
def baseEnd_1932500 : Nat := 992301364813794318562601

theorem tailTrace_1932500 : CollatzResearch.WordTrace tailWord_1932500 prefixEnd_1932500 992301364813794318562601 := by
  unfold tailWord_1932500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35242032749445009784453477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46989376999260013045937969 35242032749445009784453477)
  ·
    refine ⟨6607881140520939334585027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35242032749445009784453477 6607881140520939334585027)
    ·
      refine ⟨9911821710781409001877541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607881140520939334585027 9911821710781409001877541)
      ·
        refine ⟨1858466570771514187852039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9911821710781409001877541 1858466570771514187852039)
        ·
          refine ⟨2787699856157271281778059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858466570771514187852039 2787699856157271281778059)
          ·
            refine ⟨4181549784235906922667089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787699856157271281778059 4181549784235906922667089)
            ·
              refine ⟨3136162338176930192000317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181549784235906922667089 3136162338176930192000317)
              ·
                refine ⟨1176060876816348822000119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136162338176930192000317 1176060876816348822000119)
                ·
                  refine ⟨1764091315224523233000179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176060876816348822000119 1764091315224523233000179)
                  ·
                    refine ⟨2646136972836784849500269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764091315224523233000179 2646136972836784849500269)
                    ·
                      refine ⟨992301364813794318562601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646136972836784849500269 992301364813794318562601)
                      ·
                        rfl

theorem cell23_1932500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1932500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932500 prefixEnd_1932500 := by exact prefixLift 1932500
  have htrace : WordTrace (prefixWord ++ tailWord_1932500) baseStart_1932500 baseEnd_1932500 := by
    simpa [prefixWord, tailWord_1932500, baseEnd_1932500] using wordTrace_append hprefix tailTrace_1932500
  have hstable : (prefixWord ++ tailWord_1932500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932500).length < 2 ^ (prefixWord ++ tailWord_1932500).sum := by decide
  have hdescent : baseEnd_1932500 < baseStart_1932500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932546 : List Nat := [3, 4, 1, 1, 3, 2, 2, 7]
def baseStart_1932546 : Nat := 118140960795 + 1932546 * 2 ^ 59
def prefixEnd_1932546 : Nat := 4983230072969 + 3 ^ 40 * 1932546 * 2
def baseEnd_1932546 : Nat := 36752777219403745873607

theorem tailTrace_1932546 : CollatzResearch.WordTrace tailWord_1932546 prefixEnd_1932546 36752777219403745873607 := by
  unfold tailWord_1932546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621435814180842356270373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46990495504482246283387661 17621435814180842356270373)
  ·
    refine ⟨3304019215158907941800695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17621435814180842356270373 3304019215158907941800695)
    ·
      refine ⟨4956028822738361912701043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3304019215158907941800695 4956028822738361912701043)
      ·
        refine ⟨7434043234107542869051565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956028822738361912701043 7434043234107542869051565)
        ·
          refine ⟨2787766212790328575894337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7434043234107542869051565 2787766212790328575894337)
          ·
            refine ⟨2090824659592746431920753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787766212790328575894337 2090824659592746431920753)
            ·
              refine ⟨1568118494694559823940565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090824659592746431920753 1568118494694559823940565)
              ·
                refine ⟨36752777219403745873607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1568118494694559823940565 36752777219403745873607)
                ·
                  rfl

theorem cell23_1932546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_1932546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932546 prefixEnd_1932546 := by exact prefixLift 1932546
  have htrace : WordTrace (prefixWord ++ tailWord_1932546) baseStart_1932546 baseEnd_1932546 := by
    simpa [prefixWord, tailWord_1932546, baseEnd_1932546] using wordTrace_append hprefix tailTrace_1932546
  have hstable : (prefixWord ++ tailWord_1932546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932546).length < 2 ^ (prefixWord ++ tailWord_1932546).sum := by decide
  have hdescent : baseEnd_1932546 < baseStart_1932546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932574 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1932574 : Nat := 118140960795 + 1932574 * 2 ^ 59
def prefixEnd_1932574 : Nat := 4983230072969 + 3 ^ 40 * 1932574 * 2
def baseEnd_1932574 : Nat := 992339362382227029037261

theorem tailTrace_1932574 : CollatzResearch.WordTrace tailWord_1932574 prefixEnd_1932574 992339362382227029037261 := by
  unfold tailWord_1932574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810845562577741275887597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46991176333747953471400517 8810845562577741275887597)
  ·
    refine ⟨3304067085966652978457849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8810845562577741275887597 3304067085966652978457849)
    ·
      refine ⟨2478050314474989733843387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3304067085966652978457849 2478050314474989733843387)
      ·
        refine ⟨3717075471712484600765081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478050314474989733843387 3717075471712484600765081)
        ·
          refine ⟨2787806603784363450573811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717075471712484600765081 2787806603784363450573811)
          ·
            refine ⟨4181709905676545175860717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787806603784363450573811 4181709905676545175860717)
            ·
              refine ⟨1568141214628704440947769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4181709905676545175860717 1568141214628704440947769)
              ·
                refine ⟨1176105910971528330710827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568141214628704440947769 1176105910971528330710827)
                ·
                  refine ⟨1764158866457292496066241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176105910971528330710827 1764158866457292496066241)
                  ·
                    refine ⟨1323119149842969372049681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764158866457292496066241 1323119149842969372049681)
                    ·
                      refine ⟨992339362382227029037261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323119149842969372049681 992339362382227029037261)
                      ·
                        rfl

theorem cell23_1932574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1932574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932574 prefixEnd_1932574 := by exact prefixLift 1932574
  have htrace : WordTrace (prefixWord ++ tailWord_1932574) baseStart_1932574 baseEnd_1932574 := by
    simpa [prefixWord, tailWord_1932574, baseEnd_1932574] using wordTrace_append hprefix tailTrace_1932574
  have hstable : (prefixWord ++ tailWord_1932574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932574).length < 2 ^ (prefixWord ++ tailWord_1932574).sum := by decide
  have hdescent : baseEnd_1932574 < baseStart_1932574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932596 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_1932596 : Nat := 118140960795 + 1932596 * 2 ^ 59
def prefixEnd_1932596 : Nat := 4983230072969 + 3 ^ 40 * 1932596 * 2
def baseEnd_1932596 : Nat := 992350658956625942962159

theorem tailTrace_1932596 : CollatzResearch.WordTrace tailWord_1932596 prefixEnd_1932596 992350658956625942962159 := by
  unfold tailWord_1932596
  simp only [CollatzResearch.WordTrace]
  refine ⟨35243783453271113982200821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46991711271028151976267761 35243783453271113982200821)
  ·
    refine ⟨3304104698744166935831327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35243783453271113982200821 3304104698744166935831327)
    ·
      refine ⟨4956157048116250403746991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3304104698744166935831327 4956157048116250403746991)
      ·
        refine ⟨7434235572174375605620487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956157048116250403746991 7434235572174375605620487)
        ·
          refine ⟨11151353358261563408430731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434235572174375605620487 11151353358261563408430731)
          ·
            refine ⟨16727030037392345112646097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151353358261563408430731 16727030037392345112646097)
            ·
              refine ⟨12545272528044258834484573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16727030037392345112646097 12545272528044258834484573)
              ·
                refine ⟨4704477198016597062931715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12545272528044258834484573 4704477198016597062931715)
                ·
                  refine ⟨7056715797024895594397573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704477198016597062931715 7056715797024895594397573)
                  ·
                    refine ⟨1323134211942167923949545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056715797024895594397573 1323134211942167923949545)
                    ·
                      refine ⟨992350658956625942962159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323134211942167923949545 992350658956625942962159)
                      ·
                        rfl

theorem cell23_1932596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_1932596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932596 prefixEnd_1932596 := by exact prefixLift 1932596
  have htrace : WordTrace (prefixWord ++ tailWord_1932596) baseStart_1932596 baseEnd_1932596 := by
    simpa [prefixWord, tailWord_1932596, baseEnd_1932596] using wordTrace_append hprefix tailTrace_1932596
  have hstable : (prefixWord ++ tailWord_1932596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932596).length < 2 ^ (prefixWord ++ tailWord_1932596).sum := by decide
  have hdescent : baseEnd_1932596 < baseStart_1932596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932632 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_1932632 : Nat := 118140960795 + 1932632 * 2 ^ 59
def prefixEnd_1932632 : Nat := 4983230072969 + 3 ^ 40 * 1932632 * 2
def baseEnd_1932632 : Nat := 330789714753395934037331

theorem tailTrace_1932632 : CollatzResearch.WordTrace tailWord_1932632 prefixEnd_1932632 330789714753395934037331 := by
  unfold tailWord_1932632
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244439967205903056356075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46992586622941204075141433 35244439967205903056356075)
  ·
    refine ⟨52866659950808854584534113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35244439967205903056356075 52866659950808854584534113)
    ·
      refine ⟨39649994963106640938400585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52866659950808854584534113 39649994963106640938400585)
      ·
        refine ⟨29737496222329980703800439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39649994963106640938400585 29737496222329980703800439)
        ·
          refine ⟨44606244333494971055700659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29737496222329980703800439 44606244333494971055700659)
          ·
            refine ⟨66909366500242456583550989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44606244333494971055700659 66909366500242456583550989)
            ·
              refine ⟨25091012437590921218831621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66909366500242456583550989 25091012437590921218831621)
              ·
                refine ⟨4704564832048297728530929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25091012437590921218831621 4704564832048297728530929)
                ·
                  refine ⟨3528423624036223296398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704564832048297728530929 3528423624036223296398197)
                  ·
                    refine ⟨330789714753395934037331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3528423624036223296398197 330789714753395934037331)
                    ·
                      rfl

theorem cell23_1932632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_1932632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932632 prefixEnd_1932632 := by exact prefixLift 1932632
  have htrace : WordTrace (prefixWord ++ tailWord_1932632) baseStart_1932632 baseEnd_1932632 := by
    simpa [prefixWord, tailWord_1932632, baseEnd_1932632] using wordTrace_append hprefix tailTrace_1932632
  have hstable : (prefixWord ++ tailWord_1932632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932632).length < 2 ^ (prefixWord ++ tailWord_1932632).sum := by decide
  have hdescent : baseEnd_1932632 < baseStart_1932632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932669 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_1932669 : Nat := 118140960795 + 1932669 * 2 ^ 59
def prefixEnd_1932669 : Nat := 4983230072969 + 3 ^ 40 * 1932669 * 2
def baseEnd_1932669 : Nat := 992388143044404157349323

theorem tailTrace_1932669 : CollatzResearch.WordTrace tailWord_1932669 prefixEnd_1932669 992388143044404157349323 := by
  unfold tailWord_1932669
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490229435277761431809061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46993486290185174287872707 70490229435277761431809061)
  ·
    refine ⟨13216918019114580268464199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70490229435277761431809061 13216918019114580268464199)
    ·
      refine ⟨19825377028671870402696299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216918019114580268464199 19825377028671870402696299)
      ·
        refine ⟨29738065543007805604044449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19825377028671870402696299 29738065543007805604044449)
        ·
          refine ⟨22303549157255854203033337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29738065543007805604044449 22303549157255854203033337)
          ·
            refine ⟨16727661867941890652275003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22303549157255854203033337 16727661867941890652275003)
            ·
              refine ⟨25091492801912835978412505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727661867941890652275003 25091492801912835978412505)
              ·
                refine ⟨18818619601434626983809379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25091492801912835978412505 18818619601434626983809379)
                ·
                  refine ⟨28227929402151940475714069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18818619601434626983809379 28227929402151940475714069)
                  ·
                    refine ⟨1323184190725872209799097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28227929402151940475714069 1323184190725872209799097)
                    ·
                      refine ⟨992388143044404157349323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323184190725872209799097 992388143044404157349323)
                      ·
                        rfl

theorem cell23_1932669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_1932669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932669 prefixEnd_1932669 := by exact prefixLift 1932669
  have htrace : WordTrace (prefixWord ++ tailWord_1932669) baseStart_1932669 baseEnd_1932669 := by
    simpa [prefixWord, tailWord_1932669, baseEnd_1932669] using wordTrace_append hprefix tailTrace_1932669
  have hstable : (prefixWord ++ tailWord_1932669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932669).length < 2 ^ (prefixWord ++ tailWord_1932669).sum := by decide
  have hdescent : baseEnd_1932669 < baseStart_1932669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932670 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1932670 : Nat := 118140960795 + 1932670 * 2 ^ 59
def prefixEnd_1932670 : Nat := 4983230072969 + 3 ^ 40 * 1932670 * 2
def baseEnd_1932670 : Nat := 110265406280562072604091

theorem tailTrace_1932670 : CollatzResearch.WordTrace tailWord_1932670 prefixEnd_1932670 110265406280562072604091 := by
  unfold tailWord_1932670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811283238534267325324433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46993510605516092401730309 8811283238534267325324433)
  ·
    refine ⟨6608462428900700493993325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8811283238534267325324433 6608462428900700493993325)
    ·
      refine ⟨2478173410837762685247497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6608462428900700493993325 2478173410837762685247497)
      ·
        refine ⟨1858630058128322013935623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2478173410837762685247497 1858630058128322013935623)
        ·
          refine ⟨2787945087192483020903435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858630058128322013935623 2787945087192483020903435)
          ·
            refine ⟨4181917630788724531355153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787945087192483020903435 4181917630788724531355153)
            ·
              refine ⟨3136438223091543398516365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181917630788724531355153 3136438223091543398516365)
              ·
                refine ⟨1176164333659328774443637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136438223091543398516365 1176164333659328774443637)
                ·
                  refine ⟨110265406280562072604091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176164333659328774443637 110265406280562072604091)
                  ·
                    rfl

theorem cell23_1932670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1932670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932670 prefixEnd_1932670 := by exact prefixLift 1932670
  have htrace : WordTrace (prefixWord ++ tailWord_1932670) baseStart_1932670 baseEnd_1932670 := by
    simpa [prefixWord, tailWord_1932670, baseEnd_1932670] using wordTrace_append hprefix tailTrace_1932670
  have hstable : (prefixWord ++ tailWord_1932670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932670).length < 2 ^ (prefixWord ++ tailWord_1932670).sum := by decide
  have hdescent : baseEnd_1932670 < baseStart_1932670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932739 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 1, 5]
def baseStart_1932739 : Nat := 118140960795 + 1932739 * 2 ^ 59
def prefixEnd_1932739 : Nat := 4983230072969 + 3 ^ 40 * 1932739 * 2
def baseEnd_1932739 : Nat := 330808028896739627824667

theorem tailTrace_1932739 : CollatzResearch.WordTrace tailWord_1932739 prefixEnd_1932739 330808028896739627824667 := by
  unfold tailWord_1932739
  simp only [CollatzResearch.WordTrace]
  refine ⟨70492782545024163386857271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46995188363349442257904847 70492782545024163386857271)
  ·
    refine ⟨105739173817536245080285907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70492782545024163386857271 105739173817536245080285907)
    ·
      refine ⟨158608760726304367620428861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105739173817536245080285907 158608760726304367620428861)
      ·
        refine ⟨59478285272364137857660823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158608760726304367620428861 59478285272364137857660823)
        ·
          refine ⟨89217427908546206786491235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59478285272364137857660823 89217427908546206786491235)
          ·
            refine ⟨133826141862819310179736853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89217427908546206786491235 133826141862819310179736853)
            ·
              refine ⟨6273100399819655164675165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133826141862819310179736853 6273100399819655164675165)
              ·
                refine ⟨2352412649932370686753187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6273100399819655164675165 2352412649932370686753187)
                ·
                  refine ⟨3528618974898556030129781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352412649932370686753187 3528618974898556030129781)
                  ·
                    refine ⟨330808028896739627824667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3528618974898556030129781 330808028896739627824667)
                    ·
                      rfl

theorem cell23_1932739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 5].length) (baseStart_1932739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932739 prefixEnd_1932739 := by exact prefixLift 1932739
  have htrace : WordTrace (prefixWord ++ tailWord_1932739) baseStart_1932739 baseEnd_1932739 := by
    simpa [prefixWord, tailWord_1932739, baseEnd_1932739] using wordTrace_append hprefix tailTrace_1932739
  have hstable : (prefixWord ++ tailWord_1932739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932739).length < 2 ^ (prefixWord ++ tailWord_1932739).sum := by decide
  have hdescent : baseEnd_1932739 < baseStart_1932739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932746 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_1932746 : Nat := 118140960795 + 1932746 * 2 ^ 59
def prefixEnd_1932746 : Nat := 4983230072969 + 3 ^ 40 * 1932746 * 2
def baseEnd_1932746 : Nat := 992427681054800356086469

theorem tailTrace_1932746 : CollatzResearch.WordTrace tailWord_1932746 prefixEnd_1932746 992427681054800356086469 := by
  unfold tailWord_1932746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623259463999700895590523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46995358570665869054908061 17623259463999700895590523)
  ·
    refine ⟨26434889195999551343385785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17623259463999700895590523 26434889195999551343385785)
    ·
      refine ⟨19826166896999663507539339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26434889195999551343385785 19826166896999663507539339)
      ·
        refine ⟨29739250345499495261309009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19826166896999663507539339 29739250345499495261309009)
        ·
          refine ⟨22304437759124621445981757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29739250345499495261309009 22304437759124621445981757)
          ·
            refine ⟨8364164159671733042243159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22304437759124621445981757 8364164159671733042243159)
            ·
              refine ⟨12546246239507599563364739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364164159671733042243159 12546246239507599563364739)
              ·
                refine ⟨18819369359261399345047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546246239507599563364739 18819369359261399345047109)
                ·
                  refine ⟨3528631754861512377196333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18819369359261399345047109 3528631754861512377196333)
                  ·
                    refine ⟨1323236908073067141448625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3528631754861512377196333 1323236908073067141448625)
                    ·
                      refine ⟨992427681054800356086469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323236908073067141448625 992427681054800356086469)
                      ·
                        rfl

theorem cell23_1932746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_1932746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932746 prefixEnd_1932746 := by exact prefixLift 1932746
  have htrace : WordTrace (prefixWord ++ tailWord_1932746) baseStart_1932746 baseEnd_1932746 := by
    simpa [prefixWord, tailWord_1932746, baseEnd_1932746] using wordTrace_append hprefix tailTrace_1932746
  have hstable : (prefixWord ++ tailWord_1932746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932746).length < 2 ^ (prefixWord ++ tailWord_1932746).sum := by decide
  have hdescent : baseEnd_1932746 < baseStart_1932746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932752 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_1932752 : Nat := 118140960795 + 1932752 * 2 ^ 59
def prefixEnd_1932752 : Nat := 4983230072969 + 3 ^ 40 * 1932752 * 2
def baseEnd_1932752 : Nat := 330810253979575777537147

theorem tailTrace_1932752 : CollatzResearch.WordTrace tailWord_1932752 prefixEnd_1932752 330810253979575777537147 := by
  unfold tailWord_1932752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246628346988533303540255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46995504462651377738053673 35246628346988533303540255)
  ·
    refine ⟨52869942520482799955310383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246628346988533303540255 52869942520482799955310383)
    ·
      refine ⟨79304913780724199932965575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52869942520482799955310383 79304913780724199932965575)
      ·
        refine ⟨118957370671086299899448363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79304913780724199932965575 118957370671086299899448363)
        ·
          refine ⟨178436056006629449849172545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118957370671086299899448363 178436056006629449849172545)
          ·
            refine ⟨133827042004972087386879409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178436056006629449849172545 133827042004972087386879409)
            ·
              refine ⟨100370281503729065540159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133827042004972087386879409 100370281503729065540159557)
              ·
                refine ⟨18819427781949199788779917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100370281503729065540159557 18819427781949199788779917)
                ·
                  refine ⟨7057285418230949920792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18819427781949199788779917 7057285418230949920792469)
                  ·
                    refine ⟨330810253979575777537147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7057285418230949920792469 330810253979575777537147)
                    ·
                      rfl

theorem cell23_1932752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_1932752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932752 prefixEnd_1932752 := by exact prefixLift 1932752
  have htrace : WordTrace (prefixWord ++ tailWord_1932752) baseStart_1932752 baseEnd_1932752 := by
    simpa [prefixWord, tailWord_1932752, baseEnd_1932752] using wordTrace_append hprefix tailTrace_1932752
  have hstable : (prefixWord ++ tailWord_1932752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932752).length < 2 ^ (prefixWord ++ tailWord_1932752).sum := by decide
  have hdescent : baseEnd_1932752 < baseStart_1932752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932773 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_1932773 : Nat := 118140960795 + 1932773 * 2 ^ 59
def prefixEnd_1932773 : Nat := 4983230072969 + 3 ^ 40 * 1932773 * 2
def baseEnd_1932773 : Nat := 330813848344157250149615

theorem tailTrace_1932773 : CollatzResearch.WordTrace tailWord_1932773 prefixEnd_1932773 330813848344157250149615 := by
  unfold tailWord_1932773
  simp only [CollatzResearch.WordTrace]
  refine ⟨70494022626900987193594973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46996015084600658129063315 70494022626900987193594973)
  ·
    refine ⟨26435258485087870197598115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70494022626900987193594973 26435258485087870197598115)
    ·
      refine ⟨39652887727631805296397173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26435258485087870197598115 39652887727631805296397173)
      ·
        refine ⟨3717458224465481746537235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39652887727631805296397173 3717458224465481746537235)
        ·
          refine ⟨5576187336698222619805853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717458224465481746537235 5576187336698222619805853)
          ·
            refine ⟨2091070251261833482427195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5576187336698222619805853 2091070251261833482427195)
            ·
              refine ⟨3136605376892750223640793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091070251261833482427195 3136605376892750223640793)
              ·
                refine ⟨2352454032669562667730595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136605376892750223640793 2352454032669562667730595)
                ·
                  refine ⟨3528681049004344001595893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352454032669562667730595 3528681049004344001595893)
                  ·
                    refine ⟨330813848344157250149615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3528681049004344001595893 330813848344157250149615)
                    ·
                      rfl

theorem cell23_1932773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_1932773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932773 prefixEnd_1932773 := by exact prefixLift 1932773
  have htrace : WordTrace (prefixWord ++ tailWord_1932773) baseStart_1932773 baseEnd_1932773 := by
    simpa [prefixWord, tailWord_1932773, baseEnd_1932773] using wordTrace_append hprefix tailTrace_1932773
  have hstable : (prefixWord ++ tailWord_1932773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932773).length < 2 ^ (prefixWord ++ tailWord_1932773).sum := by decide
  have hdescent : baseEnd_1932773 < baseStart_1932773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932786 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1932786 : Nat := 118140960795 + 1932786 * 2 ^ 59
def prefixEnd_1932786 : Nat := 4983230072969 + 3 ^ 40 * 1932786 * 2
def baseEnd_1932786 : Nat := 330816073426993399862095

theorem tailTrace_1932786 : CollatzResearch.WordTrace tailWord_1932786 prefixEnd_1932786 330816073426993399862095 := by
  unfold tailWord_1932786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623624193963472603454553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46996331183902593609212141 17623624193963472603454553)
  ·
    refine ⟨13217718145472604452590915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17623624193963472603454553 13217718145472604452590915)
    ·
      refine ⟨19826577218208906678886373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13217718145472604452590915 19826577218208906678886373)
      ·
        refine ⟨3717483228414170002291195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19826577218208906678886373 3717483228414170002291195)
        ·
          refine ⟨5576224842621255003436793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717483228414170002291195 5576224842621255003436793)
          ·
            refine ⟨4182168631965941252577595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5576224842621255003436793 4182168631965941252577595)
            ·
              refine ⟨6273252947948911878866393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182168631965941252577595 6273252947948911878866393)
              ·
                refine ⟨4704939710961683909149795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6273252947948911878866393 4704939710961683909149795)
                ·
                  refine ⟨7057409566442525863724693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704939710961683909149795 7057409566442525863724693)
                  ·
                    refine ⟨330816073426993399862095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7057409566442525863724693 330816073426993399862095)
                    ·
                      rfl

theorem cell23_1932786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1932786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932786 prefixEnd_1932786 := by exact prefixLift 1932786
  have htrace : WordTrace (prefixWord ++ tailWord_1932786) baseStart_1932786 baseEnd_1932786 := by
    simpa [prefixWord, tailWord_1932786, baseEnd_1932786] using wordTrace_append hprefix tailTrace_1932786
  have hstable : (prefixWord ++ tailWord_1932786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932786).length < 2 ^ (prefixWord ++ tailWord_1932786).sum := by decide
  have hdescent : baseEnd_1932786 < baseStart_1932786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932796 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1932796 : Nat := 118140960795 + 1932796 * 2 ^ 59
def prefixEnd_1932796 : Nat := 4983230072969 + 3 ^ 40 * 1932796 * 2
def baseEnd_1932796 : Nat := 992453355087525160461239

theorem tailTrace_1932796 : CollatzResearch.WordTrace tailWord_1932796 prefixEnd_1932796 992453355087525160461239 := by
  unfold tailWord_1932796
  simp only [CollatzResearch.WordTrace]
  refine ⟨35247430752908831060841121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46996574337211774747788161 35247430752908831060841121)
  ·
    refine ⟨26435573064681623295630841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35247430752908831060841121 26435573064681623295630841)
    ·
      refine ⟨19826679798511217471723131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26435573064681623295630841 19826679798511217471723131)
      ·
        refine ⟨29740019697766826207584697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19826679798511217471723131 29740019697766826207584697)
        ·
          refine ⟨22305014773325119655688523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29740019697766826207584697 22305014773325119655688523)
          ·
            refine ⟨33457522159987679483532785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305014773325119655688523 33457522159987679483532785)
            ·
              refine ⟨25093141619990759612649589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33457522159987679483532785 25093141619990759612649589)
              ·
                refine ⟨2352482026874133713685899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25093141619990759612649589 2352482026874133713685899)
                ·
                  refine ⟨3528723040311200570528849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352482026874133713685899 3528723040311200570528849)
                  ·
                    refine ⟨2646542280233400427896637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528723040311200570528849 2646542280233400427896637)
                    ·
                      refine ⟨992453355087525160461239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646542280233400427896637 992453355087525160461239)
                      ·
                        rfl

theorem cell23_1932796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1932796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932796 prefixEnd_1932796 := by exact prefixLift 1932796
  have htrace : WordTrace (prefixWord ++ tailWord_1932796) baseStart_1932796 baseEnd_1932796 := by
    simpa [prefixWord, tailWord_1932796, baseEnd_1932796] using wordTrace_append hprefix tailTrace_1932796
  have hstable : (prefixWord ++ tailWord_1932796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932796).length < 2 ^ (prefixWord ++ tailWord_1932796).sum := by decide
  have hdescent : baseEnd_1932796 < baseStart_1932796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
