import V185TrunkScan23Chunk0543

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3216835 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3]
def baseStart_3216835 : Nat := 118140960795 + 3216835 * 2 ^ 59
def prefixEnd_3216835 : Nat := 4983230072969 + 3 ^ 40 * 3216835 * 2
def baseEnd_3216835 : Nat := 1651782541206026851968551

theorem tailTrace_3216835 : CollatzResearch.WordTrace tailWord_3216835 prefixEnd_3216835 1651782541206026851968551 := by
  unfold tailWord_3216835
  simp only [CollatzResearch.WordTrace]
  refine ⟨117327611300963661523803959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78218407533975774349202639 117327611300963661523803959)
  ·
    refine ⟨175991416951445492285705939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117327611300963661523803959 175991416951445492285705939)
    ·
      refine ⟨263987125427168238428558909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175991416951445492285705939 263987125427168238428558909)
      ·
        refine ⟨98995172035188089410709591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263987125427168238428558909 98995172035188089410709591)
        ·
          refine ⟨148492758052782134116064387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98995172035188089410709591 148492758052782134116064387)
          ·
            refine ⟨222739137079173201174096581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148492758052782134116064387 222739137079173201174096581)
            ·
              refine ⟨41763588202344975220143109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222739137079173201174096581 41763588202344975220143109)
              ·
                refine ⟨7830672787939682853776833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41763588202344975220143109 7830672787939682853776833)
                ·
                  refine ⟨5873004590954762140332625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830672787939682853776833 5873004590954762140332625)
                  ·
                    refine ⟨4404753443216071605249469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873004590954762140332625 4404753443216071605249469)
                    ·
                      refine ⟨1651782541206026851968551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404753443216071605249469 1651782541206026851968551)
                      ·
                        rfl

theorem cell23_3216835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_3216835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216835 prefixEnd_3216835 := by exact prefixLift 3216835
  have htrace : WordTrace (prefixWord ++ tailWord_3216835) baseStart_3216835 baseEnd_3216835 := by
    simpa [prefixWord, tailWord_3216835, baseEnd_3216835] using wordTrace_append hprefix tailTrace_3216835
  have hstable : (prefixWord ++ tailWord_3216835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216835).length < 2 ^ (prefixWord ++ tailWord_3216835).sum := by decide
  have hdescent : baseEnd_3216835 < baseStart_3216835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216842 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3216842 : Nat := 118140960795 + 3216842 * 2 ^ 59
def prefixEnd_3216842 : Nat := 4983230072969 + 3 ^ 40 * 3216842 * 2
def baseEnd_3216842 : Nat := 550595378523536108193673

theorem tailTrace_3216842 : CollatzResearch.WordTrace tailWord_3216842 prefixEnd_3216842 550595378523536108193673 := by
  unfold tailWord_3216842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331966652984575429827195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78218577741292201146205853 29331966652984575429827195)
  ·
    refine ⟨43997949979476863144740793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29331966652984575429827195 43997949979476863144740793)
    ·
      refine ⟨32998462484607647358555595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43997949979476863144740793 32998462484607647358555595)
      ·
        refine ⟨49497693726911471037833393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32998462484607647358555595 49497693726911471037833393)
        ·
          refine ⟨37123270295183603278375045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49497693726911471037833393 37123270295183603278375045)
          ·
            refine ⟨6960613180346925614695321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37123270295183603278375045 6960613180346925614695321)
            ·
              refine ⟨5220459885260194211021491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960613180346925614695321 5220459885260194211021491)
              ·
                refine ⟨7830689827890291316532237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220459885260194211021491 7830689827890291316532237)
                ·
                  refine ⟨2936508685458859243699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7830689827890291316532237 2936508685458859243699589)
                  ·
                    refine ⟨550595378523536108193673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936508685458859243699589 550595378523536108193673)
                    ·
                      rfl

theorem cell23_3216842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3216842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216842 prefixEnd_3216842 := by exact prefixLift 3216842
  have htrace : WordTrace (prefixWord ++ tailWord_3216842) baseStart_3216842 baseEnd_3216842 := by
    simpa [prefixWord, tailWord_3216842, baseEnd_3216842] using wordTrace_append hprefix tailTrace_3216842
  have hstable : (prefixWord ++ tailWord_3216842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216842).length < 2 ^ (prefixWord ++ tailWord_3216842).sum := by decide
  have hdescent : baseEnd_3216842 < baseStart_3216842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216868 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3216868 : Nat := 118140960795 + 3216868 * 2 ^ 59
def prefixEnd_3216868 : Nat := 4983230072969 + 3 ^ 40 * 3216868 * 2
def baseEnd_3216868 : Nat := 550599828689208407618633

theorem tailTrace_3216868 : CollatzResearch.WordTrace tailWord_3216868 prefixEnd_3216868 550599828689208407618633 := by
  unfold tailWord_3216868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664407454922054079877629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78219209939896072106503505 58664407454922054079877629)
  ·
    refine ⟨21999152795595770279954111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58664407454922054079877629 21999152795595770279954111)
    ·
      refine ⟨32998729193393655419931167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21999152795595770279954111 32998729193393655419931167)
      ·
        refine ⟨49498093790090483129896751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32998729193393655419931167 49498093790090483129896751)
        ·
          refine ⟨74247140685135724694845127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49498093790090483129896751 74247140685135724694845127)
          ·
            refine ⟨111370711027703587042267691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74247140685135724694845127 111370711027703587042267691)
            ·
              refine ⟨167056066541555380563401537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111370711027703587042267691 167056066541555380563401537)
              ·
                refine ⟨125292049906166535422551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167056066541555380563401537 125292049906166535422551153)
                ·
                  refine ⟨93969037429624901566913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125292049906166535422551153 93969037429624901566913365)
                  ·
                    refine ⟨550599828689208407618633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 93969037429624901566913365 550599828689208407618633)
                    ·
                      rfl

theorem cell23_3216868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3216868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216868 prefixEnd_3216868 := by exact prefixLift 3216868
  have htrace : WordTrace (prefixWord ++ tailWord_3216868) baseStart_3216868 baseEnd_3216868 := by
    simpa [prefixWord, tailWord_3216868, baseEnd_3216868] using wordTrace_append hprefix tailTrace_3216868
  have hstable : (prefixWord ++ tailWord_3216868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216868).length < 2 ^ (prefixWord ++ tailWord_3216868).sum := by decide
  have hdescent : baseEnd_3216868 < baseStart_3216868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216892 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_3216892 : Nat := 118140960795 + 3216892 * 2 ^ 59
def prefixEnd_3216892 : Nat := 4983230072969 + 3 ^ 40 * 3216892 * 2
def baseEnd_3216892 : Nat := 1651811809603333128955789

theorem tailTrace_3216892 : CollatzResearch.WordTrace tailWord_3216892 prefixEnd_3216892 1651811809603333128955789 := by
  unfold tailWord_3216892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664845130878580129314465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78219793507838106839085953 58664845130878580129314465)
  ·
    refine ⟨43998633848158935096985849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58664845130878580129314465 43998633848158935096985849)
    ·
      refine ⟨32998975386119201322739387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43998633848158935096985849 32998975386119201322739387)
      ·
        refine ⟨49498463079178801984109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32998975386119201322739387 49498463079178801984109081)
        ·
          refine ⟨37123847309384101488081811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49498463079178801984109081 37123847309384101488081811)
          ·
            refine ⟨55685770964076152232122717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37123847309384101488081811 55685770964076152232122717)
            ·
              refine ⟨20882164111528557087046019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55685770964076152232122717 20882164111528557087046019)
              ·
                refine ⟨31323246167292835630569029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20882164111528557087046019 31323246167292835630569029)
                ·
                  refine ⟨5873108656367406680731693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31323246167292835630569029 5873108656367406680731693)
                  ·
                    refine ⟨2202415746137777505274385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5873108656367406680731693 2202415746137777505274385)
                    ·
                      refine ⟨1651811809603333128955789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202415746137777505274385 1651811809603333128955789)
                      ·
                        rfl

theorem cell23_3216892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_3216892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216892 prefixEnd_3216892 := by exact prefixLift 3216892
  have htrace : WordTrace (prefixWord ++ tailWord_3216892) baseStart_3216892 baseEnd_3216892 := by
    simpa [prefixWord, tailWord_3216892, baseEnd_3216892] using wordTrace_append hprefix tailTrace_3216892
  have hstable : (prefixWord ++ tailWord_3216892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216892).length < 2 ^ (prefixWord ++ tailWord_3216892).sum := by decide
  have hdescent : baseEnd_3216892 < baseStart_3216892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216905 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_3216905 : Nat := 118140960795 + 3216905 * 2 ^ 59
def prefixEnd_3216905 : Nat := 4983230072969 + 3 ^ 40 * 3216905 * 2
def baseEnd_3216905 : Nat := 1651818484851841578093229

theorem tailTrace_3216905 : CollatzResearch.WordTrace tailWord_3216905 prefixEnd_3216905 1651818484851841578093229 := by
  unfold tailWord_3216905
  simp only [CollatzResearch.WordTrace]
  refine ⟨117330164410710063478852169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78220109607140042319234779 117330164410710063478852169)
  ·
    refine ⟨87997623308032547609139127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117330164410710063478852169 87997623308032547609139127)
    ·
      refine ⟨131996434962048821413708691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87997623308032547609139127 131996434962048821413708691)
      ·
        refine ⟨197994652443073232120563037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131996434962048821413708691 197994652443073232120563037)
        ·
          refine ⟨74247994666152462045211139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197994652443073232120563037 74247994666152462045211139)
          ·
            refine ⟨111371991999228693067816709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74247994666152462045211139 111371991999228693067816709)
            ·
              refine ⟨20882248499855379950215633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111371991999228693067816709 20882248499855379950215633)
              ·
                refine ⟨15661686374891534962661725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20882248499855379950215633 15661686374891534962661725)
                ·
                  refine ⟨5873132390584325610998147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15661686374891534962661725 5873132390584325610998147)
                  ·
                    refine ⟨8809698585876488416497221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5873132390584325610998147 8809698585876488416497221)
                    ·
                      refine ⟨1651818484851841578093229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8809698585876488416497221 1651818484851841578093229)
                      ·
                        rfl

theorem cell23_3216905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_3216905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216905 prefixEnd_3216905 := by exact prefixLift 3216905
  have htrace : WordTrace (prefixWord ++ tailWord_3216905) baseStart_3216905 baseEnd_3216905 := by
    simpa [prefixWord, tailWord_3216905, baseEnd_3216905] using wordTrace_append hprefix tailTrace_3216905
  have hstable : (prefixWord ++ tailWord_3216905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216905).length < 2 ^ (prefixWord ++ tailWord_3216905).sum := by decide
  have hdescent : baseEnd_3216905 < baseStart_3216905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216936 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3216936 : Nat := 118140960795 + 3216936 * 2 ^ 59
def prefixEnd_3216936 : Nat := 4983230072969 + 3 ^ 40 * 3216936 * 2
def baseEnd_3216936 : Nat := 550611467584043652268529

theorem tailTrace_3216936 : CollatzResearch.WordTrace tailWord_3216936 prefixEnd_3216936 550611467584043652268529 := by
  unfold tailWord_3216936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665647536798877886615331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78220863382398503848820441 58665647536798877886615331)
  ·
    refine ⟨87998471305198316829922997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58665647536798877886615331 87998471305198316829922997)
    ·
      refine ⟨8249856684862342202805281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87998471305198316829922997 8249856684862342202805281)
      ·
        refine ⟨6187392513646756652103961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249856684862342202805281 6187392513646756652103961)
        ·
          refine ⟨4640544385235067489077971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187392513646756652103961 4640544385235067489077971)
          ·
            refine ⟨6960816577852601233616957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640544385235067489077971 6960816577852601233616957)
            ·
              refine ⟨2610306216694725462606359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6960816577852601233616957 2610306216694725462606359)
              ·
                refine ⟨3915459325042088193909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610306216694725462606359 3915459325042088193909539)
                ·
                  refine ⟨5873188987563132290864309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915459325042088193909539 5873188987563132290864309)
                  ·
                    refine ⟨550611467584043652268529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5873188987563132290864309 550611467584043652268529)
                    ·
                      rfl

theorem cell23_3216936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3216936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216936 prefixEnd_3216936 := by exact prefixLift 3216936
  have htrace : WordTrace (prefixWord ++ tailWord_3216936) baseStart_3216936 baseEnd_3216936 := by
    simpa [prefixWord, tailWord_3216936, baseEnd_3216936] using wordTrace_append hprefix tailTrace_3216936
  have hstable : (prefixWord ++ tailWord_3216936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216936).length < 2 ^ (prefixWord ++ tailWord_3216936).sum := by decide
  have hdescent : baseEnd_3216936 < baseStart_3216936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216949 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3216949 : Nat := 118140960795 + 3216949 * 2 ^ 59
def prefixEnd_3216949 : Nat := 4983230072969 + 3 ^ 40 * 3216949 * 2
def baseEnd_3216949 : Nat := 550613692666879801981009

theorem tailTrace_3216949 : CollatzResearch.WordTrace tailWord_3216949 prefixEnd_3216949 550613692666879801981009 := by
  unfold tailWord_3216949
  simp only [CollatzResearch.WordTrace]
  refine ⟨117331769222550658993453901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78221179481700439328969267 117331769222550658993453901)
  ·
    refine ⟨43999413458456497122545213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117331769222550658993453901 43999413458456497122545213)
    ·
      refine ⟨16499780046921186420954455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43999413458456497122545213 16499780046921186420954455)
      ·
        refine ⟨24749670070381779631431683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16499780046921186420954455 24749670070381779631431683)
        ·
          refine ⟨37124505105572669447147525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24749670070381779631431683 37124505105572669447147525)
          ·
            refine ⟨6960844707294875521340161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37124505105572669447147525 6960844707294875521340161)
            ·
              refine ⟨5220633530471156641005121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960844707294875521340161 5220633530471156641005121)
              ·
                refine ⟨3915475147853367480753841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220633530471156641005121 3915475147853367480753841)
                ·
                  refine ⟨2936606360890025610565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915475147853367480753841 2936606360890025610565381)
                  ·
                    refine ⟨550613692666879801981009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936606360890025610565381 550613692666879801981009)
                    ·
                      rfl

theorem cell23_3216949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3216949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216949 prefixEnd_3216949 := by exact prefixLift 3216949
  have htrace : WordTrace (prefixWord ++ tailWord_3216949) baseStart_3216949 baseEnd_3216949 := by
    simpa [prefixWord, tailWord_3216949, baseEnd_3216949] using wordTrace_append hprefix tailTrace_3216949
  have hstable : (prefixWord ++ tailWord_3216949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216949).length < 2 ^ (prefixWord ++ tailWord_3216949).sum := by decide
  have hdescent : baseEnd_3216949 < baseStart_3216949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216966 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3216966 : Nat := 118140960795 + 3216966 * 2 ^ 59
def prefixEnd_3216966 : Nat := 4983230072969 + 3 ^ 40 * 3216966 * 2
def baseEnd_3216966 : Nat := 550616602390588613143483

theorem tailTrace_3216966 : CollatzResearch.WordTrace tailWord_3216966 prefixEnd_3216966 550616602390588613143483 := by
  unfold tailWord_3216966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666637164484033465525711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78221592842326047264548501 3666637164484033465525711)
  ·
    refine ⟨5499955746726050198288567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666637164484033465525711 5499955746726050198288567)
    ·
      refine ⟨8249933620089075297432851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499955746726050198288567 8249933620089075297432851)
      ·
        refine ⟨12374900430133612946149277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249933620089075297432851 12374900430133612946149277)
        ·
          refine ⟨4640587661300104854805979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12374900430133612946149277 4640587661300104854805979)
          ·
            refine ⟨6960881491950157282208969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640587661300104854805979 6960881491950157282208969)
            ·
              refine ⟨5220661118962617961656727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960881491950157282208969 5220661118962617961656727)
              ·
                refine ⟨7830991678443926942485091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220661118962617961656727 7830991678443926942485091)
                ·
                  refine ⟨11746487517665890413727637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830991678443926942485091 11746487517665890413727637)
                  ·
                    refine ⟨550616602390588613143483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11746487517665890413727637 550616602390588613143483)
                    ·
                      rfl

theorem cell23_3216966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3216966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216966 prefixEnd_3216966 := by exact prefixLift 3216966
  have htrace : WordTrace (prefixWord ++ tailWord_3216966) baseStart_3216966 baseEnd_3216966 := by
    simpa [prefixWord, tailWord_3216966, baseEnd_3216966] using wordTrace_append hprefix tailTrace_3216966
  have hstable : (prefixWord ++ tailWord_3216966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216966).length < 2 ^ (prefixWord ++ tailWord_3216966).sum := by decide
  have hdescent : baseEnd_3216966 < baseStart_3216966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216972 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3216972 : Nat := 118140960795 + 3216972 * 2 ^ 59
def prefixEnd_3216972 : Nat := 4983230072969 + 3 ^ 40 * 3216972 * 2
def baseEnd_3216972 : Nat := 1651852888055692815955421

theorem tailTrace_3216972 : CollatzResearch.WordTrace tailWord_3216972 prefixEnd_3216972 1651852888055692815955421 := by
  unfold tailWord_3216972
  simp only [CollatzResearch.WordTrace]
  refine ⟨58666304050733666960770585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78221738734311555947694113 58666304050733666960770585)
  ·
    refine ⟨43999728038050250220577939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58666304050733666960770585 43999728038050250220577939)
    ·
      refine ⟨65999592057075375330866909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43999728038050250220577939 65999592057075375330866909)
      ·
        refine ⟨24749847021403265749075091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65999592057075375330866909 24749847021403265749075091)
        ·
          refine ⟨37124770532104898623612637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24749847021403265749075091 37124770532104898623612637)
          ·
            refine ⟨13921788949539336983854739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37124770532104898623612637 13921788949539336983854739)
            ·
              refine ⟨20882683424309005475782109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13921788949539336983854739 20882683424309005475782109)
              ·
                refine ⟨7831006284115877053418291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20882683424309005475782109 7831006284115877053418291)
                ·
                  refine ⟨11746509426173815580127437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831006284115877053418291 11746509426173815580127437)
                  ·
                    refine ⟨4404941034815180842547789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11746509426173815580127437 4404941034815180842547789)
                    ·
                      refine ⟨1651852888055692815955421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404941034815180842547789 1651852888055692815955421)
                      ·
                        rfl

theorem cell23_3216972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3216972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216972 prefixEnd_3216972 := by exact prefixLift 3216972
  have htrace : WordTrace (prefixWord ++ tailWord_3216972) baseStart_3216972 baseEnd_3216972 := by
    simpa [prefixWord, tailWord_3216972, baseEnd_3216972] using wordTrace_append hprefix tailTrace_3216972
  have hstable : (prefixWord ++ tailWord_3216972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216972).length < 2 ^ (prefixWord ++ tailWord_3216972).sum := by decide
  have hdescent : baseEnd_3216972 < baseStart_3216972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216973 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3216973 : Nat := 118140960795 + 3216973 * 2 ^ 59
def prefixEnd_3216973 : Nat := 4983230072969 + 3 ^ 40 * 3216973 * 2
def baseEnd_3216973 : Nat := 1651853401536347312042917

theorem tailTrace_3216973 : CollatzResearch.WordTrace tailWord_3216973 prefixEnd_3216973 1651853401536347312042917 := by
  unfold tailWord_3216973
  simp only [CollatzResearch.WordTrace]
  refine ⟨117332644574463711092327573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78221763049642474061551715 117332644574463711092327573)
  ·
    refine ⟨5499967714427986457452855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117332644574463711092327573 5499967714427986457452855)
    ·
      refine ⟨8249951571641979686179283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499967714427986457452855 8249951571641979686179283)
      ·
        refine ⟨12374927357462969529268925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249951571641979686179283 12374927357462969529268925)
        ·
          refine ⟨4640597759048613573475847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12374927357462969529268925 4640597759048613573475847)
          ·
            refine ⟨6960896638572920360213771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640597759048613573475847 6960896638572920360213771)
            ·
              refine ⟨10441344957859380540320657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960896638572920360213771 10441344957859380540320657)
              ·
                refine ⟨7831008718394535405240493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10441344957859380540320657 7831008718394535405240493)
                ·
                  refine ⟨2936628269397950776965185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7831008718394535405240493 2936628269397950776965185)
                  ·
                    refine ⟨2202471202048463082723889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936628269397950776965185 2202471202048463082723889)
                    ·
                      refine ⟨1651853401536347312042917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202471202048463082723889 1651853401536347312042917)
                      ·
                        rfl

theorem cell23_3216973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3216973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216973 prefixEnd_3216973 := by exact prefixLift 3216973
  have htrace : WordTrace (prefixWord ++ tailWord_3216973) baseStart_3216973 baseEnd_3216973 := by
    simpa [prefixWord, tailWord_3216973, baseEnd_3216973] using wordTrace_append hprefix tailTrace_3216973
  have hstable : (prefixWord ++ tailWord_3216973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216973).length < 2 ^ (prefixWord ++ tailWord_3216973).sum := by decide
  have hdescent : baseEnd_3216973 < baseStart_3216973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217006 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3217006 : Nat := 118140960795 + 3217006 * 2 ^ 59
def prefixEnd_3217006 : Nat := 4983230072969 + 3 ^ 40 * 3217006 * 2
def baseEnd_3217006 : Nat := 1651870346397945682930265

theorem tailTrace_3217006 : CollatzResearch.WordTrace tailWord_3217006 prefixEnd_3217006 1651870346397945682930265 := by
  unfold tailWord_3217006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666731022918019716034859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78222565455562771818852581 14666731022918019716034859)
  ·
    refine ⟨22000096534377029574052289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14666731022918019716034859 22000096534377029574052289)
    ·
      refine ⟨16500072400782772180539217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22000096534377029574052289 16500072400782772180539217)
      ·
        refine ⟨12375054300587079135404413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16500072400782772180539217 12375054300587079135404413)
        ·
          refine ⟨4640645362720154675776655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12375054300587079135404413 4640645362720154675776655)
          ·
            refine ⟨6960968044080232013664983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640645362720154675776655 6960968044080232013664983)
            ·
              refine ⟨10441452066120348020497475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960968044080232013664983 10441452066120348020497475)
              ·
                refine ⟨15662178099180522030746213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441452066120348020497475 15662178099180522030746213)
                ·
                  refine ⟨2936658393596347880764915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15662178099180522030746213 2936658393596347880764915)
                  ·
                    refine ⟨4404987590394521821147373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2936658393596347880764915 4404987590394521821147373)
                    ·
                      refine ⟨1651870346397945682930265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404987590394521821147373 1651870346397945682930265)
                      ·
                        rfl

theorem cell23_3217006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3217006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217006 prefixEnd_3217006 := by exact prefixLift 3217006
  have htrace : WordTrace (prefixWord ++ tailWord_3217006) baseStart_3217006 baseEnd_3217006 := by
    simpa [prefixWord, tailWord_3217006, baseEnd_3217006] using wordTrace_append hprefix tailTrace_3217006
  have hstable : (prefixWord ++ tailWord_3217006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217006).length < 2 ^ (prefixWord ++ tailWord_3217006).sum := by decide
  have hdescent : baseEnd_3217006 < baseStart_3217006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3217015 : Nat := 118140960795 + 3217015 * 2 ^ 59
def prefixEnd_3217015 : Nat := 4983230072969 + 3 ^ 40 * 3217015 * 2
def baseEnd_3217015 : Nat := 1651874967723836147717723

theorem tailTrace_3217015 : CollatzResearch.WordTrace tailWord_3217015 prefixEnd_3217015 1651874967723836147717723 := by
  unfold tailWord_3217015
  simp only [CollatzResearch.WordTrace]
  refine ⟨117334176440311552265356499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78222784293541034843570999 117334176440311552265356499)
  ·
    refine ⟨176001264660467328398034749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117334176440311552265356499 176001264660467328398034749)
    ·
      refine ⟨66000474247675248149263031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176001264660467328398034749 66000474247675248149263031)
      ·
        refine ⟨99000711371512872223894547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66000474247675248149263031 99000711371512872223894547)
        ·
          refine ⟨148501067057269308335841821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99000711371512872223894547 148501067057269308335841821)
          ·
            refine ⟨55687900146475990625940683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148501067057269308335841821 55687900146475990625940683)
            ·
              refine ⟨83531850219713985938911025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55687900146475990625940683 83531850219713985938911025)
              ·
                refine ⟨62648887664785489454183269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83531850219713985938911025 62648887664785489454183269)
                ·
                  refine ⟨11746666437147279272659363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62648887664785489454183269 11746666437147279272659363)
                  ·
                    refine ⟨17619999655720918908989045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11746666437147279272659363 17619999655720918908989045)
                    ·
                      refine ⟨1651874967723836147717723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17619999655720918908989045 1651874967723836147717723)
                      ·
                        rfl

theorem cell23_3217015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3217015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217015 prefixEnd_3217015 := by exact prefixLift 3217015
  have htrace : WordTrace (prefixWord ++ tailWord_3217015) baseStart_3217015 baseEnd_3217015 := by
    simpa [prefixWord, tailWord_3217015, baseEnd_3217015] using wordTrace_append hprefix tailTrace_3217015
  have hstable : (prefixWord ++ tailWord_3217015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217015).length < 2 ^ (prefixWord ++ tailWord_3217015).sum := by decide
  have hdescent : baseEnd_3217015 < baseStart_3217015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217035 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 7]
def baseStart_3217035 : Nat := 118140960795 + 3217035 * 2 ^ 59
def prefixEnd_3217035 : Nat := 4983230072969 + 3 ^ 40 * 3217035 * 2
def baseEnd_3217035 : Nat := 183542804148547341051959

theorem tailTrace_3217035 : CollatzResearch.WordTrace tailWord_3217035 prefixEnd_3217035 183542804148547341051959 := by
  unfold tailWord_3217035
  simp only [CollatzResearch.WordTrace]
  refine ⟨117334905900239095681084559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78223270600159397120723039 117334905900239095681084559)
  ·
    refine ⟨176002358850358643521626839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117334905900239095681084559 176002358850358643521626839)
    ·
      refine ⟨264003538275537965282440259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176002358850358643521626839 264003538275537965282440259)
      ·
        refine ⟨396005307413306947923660389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264003538275537965282440259 396005307413306947923660389)
        ·
          refine ⟨74250995139995052735686323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 396005307413306947923660389 74250995139995052735686323)
          ·
            refine ⟨111376492709992579103529485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74250995139995052735686323 111376492709992579103529485)
            ·
              refine ⟨41766184766247217163823557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111376492709992579103529485 41766184766247217163823557)
              ·
                refine ⟨7831159643671353218216917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41766184766247217163823557 7831159643671353218216917)
                ·
                  refine ⟨183542804148547341051959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7831159643671353218216917 183542804148547341051959)
                  ·
                    rfl

theorem cell23_3217035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 7].length) (baseStart_3217035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217035 prefixEnd_3217035 := by exact prefixLift 3217035
  have htrace : WordTrace (prefixWord ++ tailWord_3217035) baseStart_3217035 baseEnd_3217035 := by
    simpa [prefixWord, tailWord_3217035, baseEnd_3217035] using wordTrace_append hprefix tailTrace_3217035
  have hstable : (prefixWord ++ tailWord_3217035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217035).length < 2 ^ (prefixWord ++ tailWord_3217035).sum := by decide
  have hdescent : baseEnd_3217035 < baseStart_3217035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217092 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3217092 : Nat := 118140960795 + 3217092 * 2 ^ 59
def prefixEnd_3217092 : Nat := 4983230072969 + 3 ^ 40 * 3217092 * 2
def baseEnd_3217092 : Nat := 1651914505734232346454869

theorem tailTrace_3217092 : CollatzResearch.WordTrace tailWord_3217092 prefixEnd_3217092 1651914505734232346454869 := by
  unfold tailWord_3217092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58668492430516297207954765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78224656574021729610606353 58668492430516297207954765)
  ·
    refine ⟨22000684661443611452983037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58668492430516297207954765 22000684661443611452983037)
    ·
      refine ⟨8250256748041354294868639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22000684661443611452983037 8250256748041354294868639)
      ·
        refine ⟨12375385122062031442302959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8250256748041354294868639 12375385122062031442302959)
        ·
          refine ⟨18563077683093047163454439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375385122062031442302959 18563077683093047163454439)
          ·
            refine ⟨27844616524639570745181659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18563077683093047163454439 27844616524639570745181659)
            ·
              refine ⟨41766924786959356117772489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27844616524639570745181659 41766924786959356117772489)
              ·
                refine ⟨31325193590219517088329367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41766924786959356117772489 31325193590219517088329367)
                ·
                  refine ⟨46987790385329275632494051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31325193590219517088329367 46987790385329275632494051)
                  ·
                    refine ⟨70481685577993913448741077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46987790385329275632494051 70481685577993913448741077)
                    ·
                      refine ⟨1651914505734232346454869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70481685577993913448741077 1651914505734232346454869)
                      ·
                        rfl

theorem cell23_3217092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3217092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217092 prefixEnd_3217092 := by exact prefixLift 3217092
  have htrace : WordTrace (prefixWord ++ tailWord_3217092) baseStart_3217092 baseEnd_3217092 := by
    simpa [prefixWord, tailWord_3217092, baseEnd_3217092] using wordTrace_append hprefix tailTrace_3217092
  have hstable : (prefixWord ++ tailWord_3217092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217092).length < 2 ^ (prefixWord ++ tailWord_3217092).sum := by decide
  have hdescent : baseEnd_3217092 < baseStart_3217092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217119 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 4, 2]
def baseStart_3217119 : Nat := 118140960795 + 3217119 * 2 ^ 59
def prefixEnd_3217119 : Nat := 4983230072969 + 3 ^ 40 * 3217119 * 2
def baseEnd_3217119 : Nat := 1651928369711903740817245

theorem tailTrace_3217119 : CollatzResearch.WordTrace tailWord_3217119 prefixEnd_3217119 1651928369711903740817245 := by
  unfold tailWord_3217119
  simp only [CollatzResearch.WordTrace]
  refine ⟨117337969631934778027142411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78225313087956518684761607 117337969631934778027142411)
  ·
    refine ⟨176006954447902167040713617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117337969631934778027142411 176006954447902167040713617)
    ·
      refine ⟨132005215835926625280535213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176006954447902167040713617 132005215835926625280535213)
      ·
        refine ⟨49501955938472484480200705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132005215835926625280535213 49501955938472484480200705)
        ·
          refine ⟨37126466953854363360150529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49501955938472484480200705 37126466953854363360150529)
          ·
            refine ⟨27844850215390772520112897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37126466953854363360150529 27844850215390772520112897)
            ·
              refine ⟨20883637661543079390084673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27844850215390772520112897 20883637661543079390084673)
              ·
                refine ⟨15662728246157309542563505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20883637661543079390084673 15662728246157309542563505)
                ·
                  refine ⟨11747046184617982156922629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15662728246157309542563505 11747046184617982156922629)
                  ·
                    refine ⟨2202571159615871654422993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11747046184617982156922629 2202571159615871654422993)
                    ·
                      refine ⟨1651928369711903740817245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202571159615871654422993 1651928369711903740817245)
                      ·
                        rfl

theorem cell23_3217119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_3217119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217119 prefixEnd_3217119 := by exact prefixLift 3217119
  have htrace : WordTrace (prefixWord ++ tailWord_3217119) baseStart_3217119 baseEnd_3217119 := by
    simpa [prefixWord, tailWord_3217119, baseEnd_3217119] using wordTrace_append hprefix tailTrace_3217119
  have hstable : (prefixWord ++ tailWord_3217119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217119).length < 2 ^ (prefixWord ++ tailWord_3217119).sum := by decide
  have hdescent : baseEnd_3217119 < baseStart_3217119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217152 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_3217152 : Nat := 118140960795 + 3217152 * 2 ^ 59
def prefixEnd_3217152 : Nat := 4983230072969 + 3 ^ 40 * 3217152 * 2
def baseEnd_3217152 : Nat := 1651945314573502111704593

theorem tailTrace_3217152 : CollatzResearch.WordTrace tailWord_3217152 prefixEnd_3217152 1651945314573502111704593 := by
  unfold tailWord_3217152
  simp only [CollatzResearch.WordTrace]
  refine ⟨58669586620407612331546855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78226115493876816442062473 58669586620407612331546855)
  ·
    refine ⟨88004379930611418497320283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58669586620407612331546855 88004379930611418497320283)
    ·
      refine ⟨132006569895917127745980425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88004379930611418497320283 132006569895917127745980425)
      ·
        refine ⟨99004927421937845809485319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132006569895917127745980425 99004927421937845809485319)
        ·
          refine ⟨148507391132906768714227979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99004927421937845809485319 148507391132906768714227979)
          ·
            refine ⟨222761086699360153071341969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148507391132906768714227979 222761086699360153071341969)
            ·
              refine ⟨167070815024520114803506477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222761086699360153071341969 167070815024520114803506477)
              ·
                refine ⟨62651555634195043051314929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167070815024520114803506477 62651555634195043051314929)
                ·
                  refine ⟨46988666725646282288486197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62651555634195043051314929 46988666725646282288486197)
                  ·
                    refine ⟨4405187505529338964545581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46988666725646282288486197 4405187505529338964545581)
                    ·
                      refine ⟨1651945314573502111704593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405187505529338964545581 1651945314573502111704593)
                      ·
                        rfl

theorem cell23_3217152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_3217152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217152 prefixEnd_3217152 := by exact prefixLift 3217152
  have htrace : WordTrace (prefixWord ++ tailWord_3217152) baseStart_3217152 baseEnd_3217152 := by
    simpa [prefixWord, tailWord_3217152, baseEnd_3217152] using wordTrace_append hprefix tailTrace_3217152
  have hstable : (prefixWord ++ tailWord_3217152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217152).length < 2 ^ (prefixWord ++ tailWord_3217152).sum := by decide
  have hdescent : baseEnd_3217152 < baseStart_3217152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217156 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3217156 : Nat := 118140960795 + 3217156 * 2 ^ 59
def prefixEnd_3217156 : Nat := 4983230072969 + 3 ^ 40 * 3217156 * 2
def baseEnd_3217156 : Nat := 1651947368496120096054575

theorem tailTrace_3217156 : CollatzResearch.WordTrace tailWord_3217156 prefixEnd_3217156 1651947368496120096054575 := by
  unfold tailWord_3217156
  simp only [CollatzResearch.WordTrace]
  refine ⟨58669659566400366673119661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78226212755200488897492881 58669659566400366673119661)
  ·
    refine ⟨22001122337400137502419873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58669659566400366673119661 22001122337400137502419873)
    ·
      refine ⟨16500841753050103126814905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22001122337400137502419873 16500841753050103126814905)
      ·
        refine ⟨12375631314787577345111179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16500841753050103126814905 12375631314787577345111179)
        ·
          refine ⟨18563446972181366017666769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375631314787577345111179 18563446972181366017666769)
          ·
            refine ⟨13922585229136024513250077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18563446972181366017666769 13922585229136024513250077)
            ·
              refine ⟨5220969460926009192468779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13922585229136024513250077 5220969460926009192468779)
              ·
                refine ⟨7831454191389013788703169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220969460926009192468779 7831454191389013788703169)
                ·
                  refine ⟨5873590643541760341527377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7831454191389013788703169 5873590643541760341527377)
                  ·
                    refine ⟨4405192982656320256145533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873590643541760341527377 4405192982656320256145533)
                    ·
                      refine ⟨1651947368496120096054575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405192982656320256145533 1651947368496120096054575)
                      ·
                        rfl

theorem cell23_3217156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3217156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217156 prefixEnd_3217156 := by exact prefixLift 3217156
  have htrace : WordTrace (prefixWord ++ tailWord_3217156) baseStart_3217156 baseEnd_3217156 := by
    simpa [prefixWord, tailWord_3217156, baseEnd_3217156] using wordTrace_append hprefix tailTrace_3217156
  have hstable : (prefixWord ++ tailWord_3217156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217156).length < 2 ^ (prefixWord ++ tailWord_3217156).sum := by decide
  have hdescent : baseEnd_3217156 < baseStart_3217156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217169 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_3217169 : Nat := 118140960795 + 3217169 * 2 ^ 59
def prefixEnd_3217169 : Nat := 4983230072969 + 3 ^ 40 * 3217169 * 2
def baseEnd_3217169 : Nat := 1651954043744628545192015

theorem tailTrace_3217169 : CollatzResearch.WordTrace tailWord_3217169 prefixEnd_3217169 1651954043744628545192015 := by
  unfold tailWord_3217169
  simp only [CollatzResearch.WordTrace]
  refine ⟨117339793281753636566462561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78226528854502424377641707 117339793281753636566462561)
  ·
    refine ⟨88004844961315227424846921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117339793281753636566462561 88004844961315227424846921)
    ·
      refine ⟨66003633720986420568635191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88004844961315227424846921 66003633720986420568635191)
      ·
        refine ⟨99005450581479630852952787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66003633720986420568635191 99005450581479630852952787)
        ·
          refine ⟨148508175872219446279429181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99005450581479630852952787 148508175872219446279429181)
          ·
            refine ⟨55690565952082292354785943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148508175872219446279429181 55690565952082292354785943)
            ·
              refine ⟨83535848928123438532178915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55690565952082292354785943 83535848928123438532178915)
              ·
                refine ⟨125303773392185157798268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83535848928123438532178915 125303773392185157798268373)
                ·
                  refine ⟨2936807188879339635896915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125303773392185157798268373 2936807188879339635896915)
                  ·
                    refine ⟨4405210783319009453845373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2936807188879339635896915 4405210783319009453845373)
                    ·
                      refine ⟨1651954043744628545192015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405210783319009453845373 1651954043744628545192015)
                      ·
                        rfl

theorem cell23_3217169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_3217169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217169 prefixEnd_3217169 := by exact prefixLift 3217169
  have htrace : WordTrace (prefixWord ++ tailWord_3217169) baseStart_3217169 baseEnd_3217169 := by
    simpa [prefixWord, tailWord_3217169, baseEnd_3217169] using wordTrace_append hprefix tailTrace_3217169
  have hstable : (prefixWord ++ tailWord_3217169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217169).length < 2 ^ (prefixWord ++ tailWord_3217169).sum := by decide
  have hdescent : baseEnd_3217169 < baseStart_3217169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217219 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 4, 4]
def baseStart_3217219 : Nat := 118140960795 + 3217219 * 2 ^ 59
def prefixEnd_3217219 : Nat := 4983230072969 + 3 ^ 40 * 3217219 * 2
def baseEnd_3217219 : Nat := 550659905925784449855595

theorem tailTrace_3217219 : CollatzResearch.WordTrace tailWord_3217219 prefixEnd_3217219 550659905925784449855595 := by
  unfold tailWord_3217219
  simp only [CollatzResearch.WordTrace]
  refine ⟨117341616931572495105782711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78227744621048330070521807 117341616931572495105782711)
  ·
    refine ⟨176012425397358742658674067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117341616931572495105782711 176012425397358742658674067)
    ·
      refine ⟨264018638096038113988011101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176012425397358742658674067 264018638096038113988011101)
      ·
        refine ⟨99006989286014292745504163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264018638096038113988011101 99006989286014292745504163)
        ·
          refine ⟨148510483929021439118256245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99006989286014292745504163 148510483929021439118256245)
          ·
            refine ⟨13922857868345759917336523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148510483929021439118256245 13922857868345759917336523)
            ·
              refine ⟨20884286802518639876004785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13922857868345759917336523 20884286802518639876004785)
              ·
                refine ⟨15663215101888979907003589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20884286802518639876004785 15663215101888979907003589)
                ·
                  refine ⟨2936852831604183732563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15663215101888979907003589 2936852831604183732563173)
                  ·
                    refine ⟨550659905925784449855595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936852831604183732563173 550659905925784449855595)
                    ·
                      rfl

theorem cell23_3217219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 4].length) (baseStart_3217219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217219 prefixEnd_3217219 := by exact prefixLift 3217219
  have htrace : WordTrace (prefixWord ++ tailWord_3217219) baseStart_3217219 baseEnd_3217219 := by
    simpa [prefixWord, tailWord_3217219, baseEnd_3217219] using wordTrace_append hprefix tailTrace_3217219
  have hstable : (prefixWord ++ tailWord_3217219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217219).length < 2 ^ (prefixWord ++ tailWord_3217219).sum := by decide
  have hdescent : baseEnd_3217219 < baseStart_3217219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217236 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3217236 : Nat := 118140960795 + 3217236 * 2 ^ 59
def prefixEnd_3217236 : Nat := 4983230072969 + 3 ^ 40 * 3217236 * 2
def baseEnd_3217236 : Nat := 550662815649493261018069

theorem tailTrace_3217236 : CollatzResearch.WordTrace tailWord_3217236 prefixEnd_3217236 550662815649493261018069 := by
  unfold tailWord_3217236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671118486255453504575781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78228157981673938006101041 58671118486255453504575781)
  ·
    refine ⟨11000834716172897532107959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58671118486255453504575781 11000834716172897532107959)
    ·
      refine ⟨16501252074259346298161939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11000834716172897532107959 16501252074259346298161939)
      ·
        refine ⟨24751878111389019447242909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501252074259346298161939 24751878111389019447242909)
        ·
          refine ⟨9281954291770882292716091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24751878111389019447242909 9281954291770882292716091)
          ·
            refine ⟨13922931437656323439074137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281954291770882292716091 13922931437656323439074137)
            ·
              refine ⟨10442198578242242579305603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13922931437656323439074137 10442198578242242579305603)
              ·
                refine ⟨15663297867363363868958405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10442198578242242579305603 15663297867363363868958405)
                ·
                  refine ⟨2936868350130630725429701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15663297867363363868958405 2936868350130630725429701)
                  ·
                    refine ⟨550662815649493261018069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936868350130630725429701 550662815649493261018069)
                    ·
                      rfl

theorem cell23_3217236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3217236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217236 prefixEnd_3217236 := by exact prefixLift 3217236
  have htrace : WordTrace (prefixWord ++ tailWord_3217236) baseStart_3217236 baseEnd_3217236 := by
    simpa [prefixWord, tailWord_3217236, baseEnd_3217236] using wordTrace_append hprefix tailTrace_3217236
  have hstable : (prefixWord ++ tailWord_3217236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217236).length < 2 ^ (prefixWord ++ tailWord_3217236).sum := by decide
  have hdescent : baseEnd_3217236 < baseStart_3217236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217259 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3]
def baseStart_3217259 : Nat := 118140960795 + 3217259 * 2 ^ 59
def prefixEnd_3217259 : Nat := 4983230072969 + 3 ^ 40 * 3217259 * 2
def baseEnd_3217259 : Nat := 1652000257003533193066601

theorem tailTrace_3217259 : CollatzResearch.WordTrace tailWord_3217259 prefixEnd_3217259 1652000257003533193066601 := by
  unfold tailWord_3217259
  simp only [CollatzResearch.WordTrace]
  refine ⟨117343075851427581937238831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78228717234285054624825887 117343075851427581937238831)
  ·
    refine ⟨176014613777141372905858247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117343075851427581937238831 176014613777141372905858247)
    ·
      refine ⟨264021920665712059358787371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176014613777141372905858247 264021920665712059358787371)
      ·
        refine ⟨396032880998568089038181057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264021920665712059358787371 396032880998568089038181057)
        ·
          refine ⟨297024660748926066778635793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396032880998568089038181057 297024660748926066778635793)
          ·
            refine ⟨222768495561694550083976845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297024660748926066778635793 222768495561694550083976845)
            ·
              refine ⟨83538185835635456281491317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222768495561694550083976845 83538185835635456281491317)
              ·
                refine ⟨7831704922090824026389811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83538185835635456281491317 7831704922090824026389811)
                ·
                  refine ⟨11747557383136236039584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831704922090824026389811 11747557383136236039584717)
                  ·
                    refine ⟨4405334018676088514844269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11747557383136236039584717 4405334018676088514844269)
                    ·
                      refine ⟨1652000257003533193066601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405334018676088514844269 1652000257003533193066601)
                      ·
                        rfl

theorem cell23_3217259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].length) (baseStart_3217259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217259 prefixEnd_3217259 := by exact prefixLift 3217259
  have htrace : WordTrace (prefixWord ++ tailWord_3217259) baseStart_3217259 baseEnd_3217259 := by
    simpa [prefixWord, tailWord_3217259, baseEnd_3217259] using wordTrace_append hprefix tailTrace_3217259
  have hstable : (prefixWord ++ tailWord_3217259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217259).length < 2 ^ (prefixWord ++ tailWord_3217259).sum := by decide
  have hdescent : baseEnd_3217259 < baseStart_3217259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217272 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3217272 : Nat := 118140960795 + 3217272 * 2 ^ 59
def prefixEnd_3217272 : Nat := 4983230072969 + 3 ^ 40 * 3217272 * 2
def baseEnd_3217272 : Nat := 1652006932252041642204041

theorem tailTrace_3217272 : CollatzResearch.WordTrace tailWord_3217272 prefixEnd_3217272 1652006932252041642204041 := by
  unfold tailWord_3217272
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671775000190242578731035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78229033333586990104974713 58671775000190242578731035)
  ·
    refine ⟨88007662500285363868096553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58671775000190242578731035 88007662500285363868096553)
    ·
      refine ⟨66005746875214022901072415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88007662500285363868096553 66005746875214022901072415)
      ·
        refine ⟨99008620312821034351608623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66005746875214022901072415 99008620312821034351608623)
        ·
          refine ⟨148512930469231551527412935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99008620312821034351608623 148512930469231551527412935)
          ·
            refine ⟨222769395703847327291119403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148512930469231551527412935 222769395703847327291119403)
            ·
              refine ⟨334154093555770990936679105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222769395703847327291119403 334154093555770990936679105)
              ·
                refine ⟨250615570166828243202509329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334154093555770990936679105 250615570166828243202509329)
                ·
                  refine ⟨187961677625121182401881997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250615570166828243202509329 187961677625121182401881997)
                  ·
                    refine ⟨70485629109420443400705749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187961677625121182401881997 70485629109420443400705749)
                    ·
                      refine ⟨1652006932252041642204041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70485629109420443400705749 1652006932252041642204041)
                      ·
                        rfl

theorem cell23_3217272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3217272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217272 prefixEnd_3217272 := by exact prefixLift 3217272
  have htrace : WordTrace (prefixWord ++ tailWord_3217272) baseStart_3217272 baseEnd_3217272 := by
    simpa [prefixWord, tailWord_3217272, baseEnd_3217272] using wordTrace_append hprefix tailTrace_3217272
  have hstable : (prefixWord ++ tailWord_3217272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217272).length < 2 ^ (prefixWord ++ tailWord_3217272).sum := by decide
  have hdescent : baseEnd_3217272 < baseStart_3217272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217294 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3217294 : Nat := 118140960795 + 3217294 * 2 ^ 59
def prefixEnd_3217294 : Nat := 4983230072969 + 3 ^ 40 * 3217294 * 2
def baseEnd_3217294 : Nat := 1652018228826440556128941

theorem tailTrace_3217294 : CollatzResearch.WordTrace tailWord_3217294 prefixEnd_3217294 1652018228826440556128941 := by
  unfold tailWord_3217294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668044050787597864345367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78229568270867188609841957 14668044050787597864345367)
  ·
    refine ⟨22002066076181396796518051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14668044050787597864345367 22002066076181396796518051)
    ·
      refine ⟨33003099114272095194777077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22002066076181396796518051 33003099114272095194777077)
      ·
        refine ⟨3094040541963008924510351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33003099114272095194777077 3094040541963008924510351)
        ·
          refine ⟨4641060812944513386765527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094040541963008924510351 4641060812944513386765527)
          ·
            refine ⟨6961591219416770080148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641060812944513386765527 6961591219416770080148291)
            ·
              refine ⟨10442386829125155120222437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961591219416770080148291 10442386829125155120222437)
              ·
                refine ⟨1957947530460966585041707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10442386829125155120222437 1957947530460966585041707)
                ·
                  refine ⟨2936921295691449877562561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957947530460966585041707 2936921295691449877562561)
                  ·
                    refine ⟨2202690971768587408171921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936921295691449877562561 2202690971768587408171921)
                    ·
                      refine ⟨1652018228826440556128941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202690971768587408171921 1652018228826440556128941)
                      ·
                        rfl

theorem cell23_3217294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3217294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217294 prefixEnd_3217294 := by exact prefixLift 3217294
  have htrace : WordTrace (prefixWord ++ tailWord_3217294) baseStart_3217294 baseEnd_3217294 := by
    simpa [prefixWord, tailWord_3217294, baseEnd_3217294] using wordTrace_append hprefix tailTrace_3217294
  have hstable : (prefixWord ++ tailWord_3217294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217294).length < 2 ^ (prefixWord ++ tailWord_3217294).sum := by decide
  have hdescent : baseEnd_3217294 < baseStart_3217294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217309 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3217309 : Nat := 118140960795 + 3217309 * 2 ^ 59
def prefixEnd_3217309 : Nat := 4983230072969 + 3 ^ 40 * 3217309 * 2
def baseEnd_3217309 : Nat := 550675310345419332480457

theorem tailTrace_3217309 : CollatzResearch.WordTrace tailWord_3217309 prefixEnd_3217309 550675310345419332480457 := by
  unfold tailWord_3217309
  simp only [CollatzResearch.WordTrace]
  refine ⟨117344899501246440476558981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78229933000830960317705987 117344899501246440476558981)
  ·
    refine ⟨22002168656483707589354809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117344899501246440476558981 22002168656483707589354809)
    ·
      refine ⟨16501626492362780692016107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22002168656483707589354809 16501626492362780692016107)
      ·
        refine ⟨24752439738544171038024161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501626492362780692016107 24752439738544171038024161)
        ·
          refine ⟨18564329803908128278518121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24752439738544171038024161 18564329803908128278518121)
          ·
            refine ⟨13923247352931096208888591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18564329803908128278518121 13923247352931096208888591)
            ·
              refine ⟨20884871029396644313332887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923247352931096208888591 20884871029396644313332887)
              ·
                refine ⟨31327306544094966469999331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20884871029396644313332887 31327306544094966469999331)
                ·
                  refine ⟨46990959816142449704998997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31327306544094966469999331 46990959816142449704998997)
                  ·
                    refine ⟨550675310345419332480457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46990959816142449704998997 550675310345419332480457)
                    ·
                      rfl

theorem cell23_3217309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3217309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217309 prefixEnd_3217309 := by exact prefixLift 3217309
  have htrace : WordTrace (prefixWord ++ tailWord_3217309) baseStart_3217309 baseEnd_3217309 := by
    simpa [prefixWord, tailWord_3217309, baseEnd_3217309] using wordTrace_append hprefix tailTrace_3217309
  have hstable : (prefixWord ++ tailWord_3217309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217309).length < 2 ^ (prefixWord ++ tailWord_3217309).sum := by decide
  have hdescent : baseEnd_3217309 < baseStart_3217309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217333 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_3217333 : Nat := 118140960795 + 3217333 * 2 ^ 59
def prefixEnd_3217333 : Nat := 4983230072969 + 3 ^ 40 * 3217333 * 2
def baseEnd_3217333 : Nat := 1652038254571965903541261

theorem tailTrace_3217333 : CollatzResearch.WordTrace tailWord_3217333 prefixEnd_3217333 1652038254571965903541261 := by
  unfold tailWord_3217333
  simp only [CollatzResearch.WordTrace]
  refine ⟨117345774853159492575432653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78230516568772995050288435 117345774853159492575432653)
  ·
    refine ⟨44004665569934809715787245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117345774853159492575432653 44004665569934809715787245)
    ·
      refine ⟨16501749588725553643420217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44004665569934809715787245 16501749588725553643420217)
      ·
        refine ⟨12376312191544165232565163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16501749588725553643420217 12376312191544165232565163)
        ·
          refine ⟨18564468287316247848847745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12376312191544165232565163 18564468287316247848847745)
          ·
            refine ⟨13923351215487185886635809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18564468287316247848847745 13923351215487185886635809)
            ·
              refine ⟨10442513411615389414976857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13923351215487185886635809 10442513411615389414976857)
              ·
                refine ⟨7831885058711542061232643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10442513411615389414976857 7831885058711542061232643)
                ·
                  refine ⟨11747827588067313091848965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831885058711542061232643 11747827588067313091848965)
                  ·
                    refine ⟨2202717672762621204721681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11747827588067313091848965 2202717672762621204721681)
                    ·
                      refine ⟨1652038254571965903541261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202717672762621204721681 1652038254571965903541261)
                      ·
                        rfl

theorem cell23_3217333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_3217333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217333 prefixEnd_3217333 := by exact prefixLift 3217333
  have htrace : WordTrace (prefixWord ++ tailWord_3217333) baseStart_3217333 baseEnd_3217333 := by
    simpa [prefixWord, tailWord_3217333, baseEnd_3217333] using wordTrace_append hprefix tailTrace_3217333
  have hstable : (prefixWord ++ tailWord_3217333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217333).length < 2 ^ (prefixWord ++ tailWord_3217333).sum := by decide
  have hdescent : baseEnd_3217333 < baseStart_3217333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217356 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 7]
def baseStart_3217356 : Nat := 118140960795 + 3217356 * 2 ^ 59
def prefixEnd_3217356 : Nat := 4983230072969 + 3 ^ 40 * 3217356 * 2
def baseEnd_3217356 : Nat := 183561118291891034839295

theorem tailTrace_3217356 : CollatzResearch.WordTrace tailWord_3217356 prefixEnd_3217356 183561118291891034839295 := by
  unfold tailWord_3217356
  simp only [CollatzResearch.WordTrace]
  refine ⟨58673306866038083751759961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78231075821384111669013281 58673306866038083751759961)
  ·
    refine ⟨44004980149528562813819971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58673306866038083751759961 44004980149528562813819971)
    ·
      refine ⟨66007470224292844220729957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44004980149528562813819971 66007470224292844220729957)
      ·
        refine ⟨12376400667054908291386867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66007470224292844220729957 12376400667054908291386867)
        ·
          refine ⟨18564601000582362437080301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12376400667054908291386867 18564601000582362437080301)
          ·
            refine ⟨6961725375218385913905113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18564601000582362437080301 6961725375218385913905113)
            ·
              refine ⟨5221294031413789435428835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6961725375218385913905113 5221294031413789435428835)
              ·
                refine ⟨7831941047120684153143253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221294031413789435428835 7831941047120684153143253)
                ·
                  refine ⟨183561118291891034839295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7831941047120684153143253 183561118291891034839295)
                  ·
                    rfl

theorem cell23_3217356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_3217356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217356 prefixEnd_3217356 := by exact prefixLift 3217356
  have htrace : WordTrace (prefixWord ++ tailWord_3217356) baseStart_3217356 baseEnd_3217356 := by
    simpa [prefixWord, tailWord_3217356, baseEnd_3217356] using wordTrace_append hprefix tailTrace_3217356
  have hstable : (prefixWord ++ tailWord_3217356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217356).length < 2 ^ (prefixWord ++ tailWord_3217356).sum := by decide
  have hdescent : baseEnd_3217356 < baseStart_3217356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217376 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2]
def baseStart_3217376 : Nat := 118140960795 + 3217376 * 2 ^ 59
def prefixEnd_3217376 : Nat := 4983230072969 + 3 ^ 40 * 3217376 * 2
def baseEnd_3217376 : Nat := 1652060334240109235303563

theorem tailTrace_3217376 : CollatzResearch.WordTrace tailWord_3217376 prefixEnd_3217376 1652060334240109235303563 := by
  unfold tailWord_3217376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58673671596001855459623991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78231562128002473946165321 58673671596001855459623991)
  ·
    refine ⟨88010507394002783189435987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58673671596001855459623991 88010507394002783189435987)
    ·
      refine ⟨132015761091004174784153981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88010507394002783189435987 132015761091004174784153981)
      ·
        refine ⟨49505910409126565544057743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132015761091004174784153981 49505910409126565544057743)
        ·
          refine ⟨74258865613689848316086615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49505910409126565544057743 74258865613689848316086615)
          ·
            refine ⟨111388298420534772474129923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74258865613689848316086615 111388298420534772474129923)
            ·
              refine ⟨167082447630802158711194885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111388298420534772474129923 167082447630802158711194885)
              ·
                refine ⟨31327958930775404758349041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167082447630802158711194885 31327958930775404758349041)
                ·
                  refine ⟨23495969198081553568761781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31327958930775404758349041 23495969198081553568761781)
                  ·
                    refine ⟨2202747112320145647071417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23495969198081553568761781 2202747112320145647071417)
                    ·
                      refine ⟨1652060334240109235303563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202747112320145647071417 1652060334240109235303563)
                      ·
                        rfl

theorem cell23_3217376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_3217376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217376 prefixEnd_3217376 := by exact prefixLift 3217376
  have htrace : WordTrace (prefixWord ++ tailWord_3217376) baseStart_3217376 baseEnd_3217376 := by
    simpa [prefixWord, tailWord_3217376, baseEnd_3217376] using wordTrace_append hprefix tailTrace_3217376
  have hstable : (prefixWord ++ tailWord_3217376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217376).length < 2 ^ (prefixWord ++ tailWord_3217376).sum := by decide
  have hdescent : baseEnd_3217376 < baseStart_3217376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217386 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3217386 : Nat := 118140960795 + 3217386 * 2 ^ 59
def prefixEnd_3217386 : Nat := 4983230072969 + 3 ^ 40 * 3217386 * 2
def baseEnd_3217386 : Nat := 550688489682218065392839

theorem tailTrace_3217386 : CollatzResearch.WordTrace tailWord_3217386 prefixEnd_3217386 550688489682218065392839 := by
  unfold tailWord_3217386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29336926980491870656778003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78231805281311655084741341 29336926980491870656778003)
  ·
    refine ⟨44005390470737805985167005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29336926980491870656778003 44005390470737805985167005)
    ·
      refine ⟨16502021426526677244437627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44005390470737805985167005 16502021426526677244437627)
      ·
        refine ⟨24753032139790015866656441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16502021426526677244437627 24753032139790015866656441)
        ·
          refine ⟨18564774104842511899992331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24753032139790015866656441 18564774104842511899992331)
          ·
            refine ⟨27847161157263767849988497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18564774104842511899992331 27847161157263767849988497)
            ·
              refine ⟨20885370867947825887491373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27847161157263767849988497 20885370867947825887491373)
              ·
                refine ⟨7832014075480434707809265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20885370867947825887491373 7832014075480434707809265)
                ·
                  refine ⟨5874010556610326030856949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832014075480434707809265 5874010556610326030856949)
                  ·
                    refine ⟨550688489682218065392839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5874010556610326030856949 550688489682218065392839)
                    ·
                      rfl

theorem cell23_3217386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3217386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217386 prefixEnd_3217386 := by exact prefixLift 3217386
  have htrace : WordTrace (prefixWord ++ tailWord_3217386) baseStart_3217386 baseEnd_3217386 := by
    simpa [prefixWord, tailWord_3217386, baseEnd_3217386] using wordTrace_append hprefix tailTrace_3217386
  have hstable : (prefixWord ++ tailWord_3217386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217386).length < 2 ^ (prefixWord ++ tailWord_3217386).sum := by decide
  have hdescent : baseEnd_3217386 < baseStart_3217386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217390 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3217390 : Nat := 118140960795 + 3217390 * 2 ^ 59
def prefixEnd_3217390 : Nat := 4983230072969 + 3 ^ 40 * 3217390 * 2
def baseEnd_3217390 : Nat := 183563058107696908947611

theorem tailTrace_3217390 : CollatzResearch.WordTrace tailWord_3217390 prefixEnd_3217390 183563058107696908947611 := by
  unfold tailWord_3217390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668481726744123913782203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78231902542635327540171749 14668481726744123913782203)
  ·
    refine ⟨22002722590116185870673305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14668481726744123913782203 22002722590116185870673305)
    ·
      refine ⟨16502041942587139403004979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22002722590116185870673305 16502041942587139403004979)
      ·
        refine ⟨24753062913880709104507469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16502041942587139403004979 24753062913880709104507469)
        ·
          refine ⟨9282398592705265914190301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24753062913880709104507469 9282398592705265914190301)
          ·
            refine ⟨3480899472264474717821363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9282398592705265914190301 3480899472264474717821363)
            ·
              refine ⟨5221349208396712076732045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480899472264474717821363 5221349208396712076732045)
              ·
                refine ⟨1958005953148767028774517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221349208396712076732045 1958005953148767028774517)
                ·
                  refine ⟨183563058107696908947611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958005953148767028774517 183563058107696908947611)
                  ·
                    rfl

theorem cell23_3217390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3217390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217390 prefixEnd_3217390 := by exact prefixLift 3217390
  have htrace : WordTrace (prefixWord ++ tailWord_3217390) baseStart_3217390 baseEnd_3217390 := by
    simpa [prefixWord, tailWord_3217390, baseEnd_3217390] using wordTrace_append hprefix tailTrace_3217390
  have hstable : (prefixWord ++ tailWord_3217390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217390).length < 2 ^ (prefixWord ++ tailWord_3217390).sum := by decide
  have hdescent : baseEnd_3217390 < baseStart_3217390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217443 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3]
def baseStart_3217443 : Nat := 118140960795 + 3217443 * 2 ^ 59
def prefixEnd_3217443 : Nat := 4983230072969 + 3 ^ 40 * 3217443 * 2
def baseEnd_3217443 : Nat := 1652094737443960473165755

theorem tailTrace_3217443 : CollatzResearch.WordTrace tailWord_3217443 prefixEnd_3217443 1652094737443960473165755 := by
  unfold tailWord_3217443
  simp only [CollatzResearch.WordTrace]
  refine ⟨117349786882760981361936983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78233191255173987574624655 117349786882760981361936983)
  ·
    refine ⟨176024680324141472042905475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117349786882760981361936983 176024680324141472042905475)
    ·
      refine ⟨264037020486212208064358213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176024680324141472042905475 264037020486212208064358213)
      ·
        refine ⟨49506941341164789012067165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264037020486212208064358213 49506941341164789012067165)
        ·
          refine ⟨18565103002936795879525187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49506941341164789012067165 18565103002936795879525187)
          ·
            refine ⟨27847654504405193819287781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565103002936795879525187 27847654504405193819287781)
            ·
              refine ⟨5221435219575973841116459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27847654504405193819287781 5221435219575973841116459)
              ·
                refine ⟨7832152829363960761674689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221435219575973841116459 7832152829363960761674689)
                ·
                  refine ⟨5874114622022970571256017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832152829363960761674689 5874114622022970571256017)
                  ·
                    refine ⟨4405585966517227928442013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874114622022970571256017 4405585966517227928442013)
                    ·
                      refine ⟨1652094737443960473165755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405585966517227928442013 1652094737443960473165755)
                      ·
                        rfl

theorem cell23_3217443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_3217443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217443 prefixEnd_3217443 := by exact prefixLift 3217443
  have htrace : WordTrace (prefixWord ++ tailWord_3217443) baseStart_3217443 baseEnd_3217443 := by
    simpa [prefixWord, tailWord_3217443, baseEnd_3217443] using wordTrace_append hprefix tailTrace_3217443
  have hstable : (prefixWord ++ tailWord_3217443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217443).length < 2 ^ (prefixWord ++ tailWord_3217443).sum := by decide
  have hdescent : baseEnd_3217443 < baseStart_3217443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217494 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3217494 : Nat := 118140960795 + 3217494 * 2 ^ 59
def prefixEnd_3217494 : Nat := 4983230072969 + 3 ^ 40 * 3217494 * 2
def baseEnd_3217494 : Nat := 1652120924957339773628021

theorem tailTrace_3217494 : CollatzResearch.WordTrace tailWord_3217494 prefixEnd_3217494 1652120924957339773628021 := by
  unfold tailWord_3217494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334477937848513567002721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78234431337050811381362357 7334477937848513567002721)
  ·
    refine ⟨5500858453386385175252041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334477937848513567002721 5500858453386385175252041)
    ·
      refine ⟨4125643840039788881439031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5500858453386385175252041 4125643840039788881439031)
      ·
        refine ⟨6188465760059683322158547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125643840039788881439031 6188465760059683322158547)
        ·
          refine ⟨9282698640089524983237821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188465760059683322158547 9282698640089524983237821)
          ·
            refine ⟨3481011990033571868714183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9282698640089524983237821 3481011990033571868714183)
            ·
              refine ⟨5221517985050357803071275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481011990033571868714183 5221517985050357803071275)
              ·
                refine ⟨7832276977575536704606913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221517985050357803071275 7832276977575536704606913)
                ·
                  refine ⟨5874207733181652528455185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832276977575536704606913 5874207733181652528455185)
                  ·
                    refine ⟨4405655799886239396341389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874207733181652528455185 4405655799886239396341389)
                    ·
                      refine ⟨1652120924957339773628021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405655799886239396341389 1652120924957339773628021)
                      ·
                        rfl

theorem cell23_3217494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3217494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217494 prefixEnd_3217494 := by exact prefixLift 3217494
  have htrace : WordTrace (prefixWord ++ tailWord_3217494) baseStart_3217494 baseEnd_3217494 := by
    simpa [prefixWord, tailWord_3217494, baseEnd_3217494] using wordTrace_append hprefix tailTrace_3217494
  have hstable : (prefixWord ++ tailWord_3217494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217494).length < 2 ^ (prefixWord ++ tailWord_3217494).sum := by decide
  have hdescent : baseEnd_3217494 < baseStart_3217494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217500 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3217500 : Nat := 118140960795 + 3217500 * 2 ^ 59
def prefixEnd_3217500 : Nat := 4983230072969 + 3 ^ 40 * 3217500 * 2
def baseEnd_3217500 : Nat := 1652124005841266750152993

theorem tailTrace_3217500 : CollatzResearch.WordTrace tailWord_3217500 prefixEnd_3217500 1652124005841266750152993 := by
  unfold tailWord_3217500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58675932921777240048380977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78234577229036320064507969 58675932921777240048380977)
  ·
    refine ⟨44006949691332930036285733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58675932921777240048380977 44006949691332930036285733)
    ·
      refine ⟨8251303067124924381803575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44006949691332930036285733 8251303067124924381803575)
      ·
        refine ⟨12376954600687386572705363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8251303067124924381803575 12376954600687386572705363)
        ·
          refine ⟨18565431901031079859058045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12376954600687386572705363 18565431901031079859058045)
          ·
            refine ⟨6962036962886654947146767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18565431901031079859058045 6962036962886654947146767)
            ·
              refine ⟨10443055444329982420720151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962036962886654947146767 10443055444329982420720151)
              ·
                refine ⟨15664583166494973631080227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443055444329982420720151 15664583166494973631080227)
                ·
                  refine ⟨23496874749742460446620341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664583166494973631080227 23496874749742460446620341)
                  ·
                    refine ⟨2202832007788355666870657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23496874749742460446620341 2202832007788355666870657)
                    ·
                      refine ⟨1652124005841266750152993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202832007788355666870657 1652124005841266750152993)
                      ·
                        rfl

theorem cell23_3217500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3217500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217500 prefixEnd_3217500 := by exact prefixLift 3217500
  have htrace : WordTrace (prefixWord ++ tailWord_3217500) baseStart_3217500 baseEnd_3217500 := by
    simpa [prefixWord, tailWord_3217500, baseEnd_3217500] using wordTrace_append hprefix tailTrace_3217500
  have hstable : (prefixWord ++ tailWord_3217500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217500).length < 2 ^ (prefixWord ++ tailWord_3217500).sum := by decide
  have hdescent : baseEnd_3217500 < baseStart_3217500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217513 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_3217513 : Nat := 118140960795 + 3217513 * 2 ^ 59
def prefixEnd_3217513 : Nat := 4983230072969 + 3 ^ 40 * 3217513 * 2
def baseEnd_3217513 : Nat := 1652130681089775199290433

theorem tailTrace_3217513 : CollatzResearch.WordTrace tailWord_3217513 prefixEnd_3217513 1652130681089775199290433 := by
  unfold tailWord_3217513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117352339992507383316985193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78234893328338255544656795 117352339992507383316985193)
  ·
    refine ⟨88014254994380537487738895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117352339992507383316985193 88014254994380537487738895)
    ·
      refine ⟨132021382491570806231608343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88014254994380537487738895 132021382491570806231608343)
      ·
        refine ⟨198032073737356209347412515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132021382491570806231608343 198032073737356209347412515)
        ·
          refine ⟨297048110606034314021118773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198032073737356209347412515 297048110606034314021118773)
          ·
            refine ⟨27848260369315716939479885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297048110606034314021118773 27848260369315716939479885)
            ·
              refine ⟨10443097638493393852304957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27848260369315716939479885 10443097638493393852304957)
              ·
                refine ⟨3916161614435022694614359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10443097638493393852304957 3916161614435022694614359)
                ·
                  refine ⟨5874242421652534041921539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916161614435022694614359 5874242421652534041921539)
                  ·
                    refine ⟨8811363632478801062882309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5874242421652534041921539 8811363632478801062882309)
                    ·
                      refine ⟨1652130681089775199290433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8811363632478801062882309 1652130681089775199290433)
                      ·
                        rfl

theorem cell23_3217513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_3217513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217513 prefixEnd_3217513 := by exact prefixLift 3217513
  have htrace : WordTrace (prefixWord ++ tailWord_3217513) baseStart_3217513 baseEnd_3217513 := by
    simpa [prefixWord, tailWord_3217513, baseEnd_3217513] using wordTrace_append hprefix tailTrace_3217513
  have hstable : (prefixWord ++ tailWord_3217513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217513).length < 2 ^ (prefixWord ++ tailWord_3217513).sum := by decide
  have hdescent : baseEnd_3217513 < baseStart_3217513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217533 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_3217533 : Nat := 118140960795 + 3217533 * 2 ^ 59
def prefixEnd_3217533 : Nat := 4983230072969 + 3 ^ 40 * 3217533 * 2
def baseEnd_3217533 : Nat := 1652140950702865121040341

theorem tailTrace_3217533 : CollatzResearch.WordTrace tailWord_3217533 prefixEnd_3217533 1652140950702865121040341 := by
  unfold tailWord_3217533
  simp only [CollatzResearch.WordTrace]
  refine ⟨117353069452434926732713253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78235379634956617821808835 117353069452434926732713253)
  ·
    refine ⟨22003700522331548762383735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117353069452434926732713253 22003700522331548762383735)
    ·
      refine ⟨33005550783497323143575603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22003700522331548762383735 33005550783497323143575603)
      ·
        refine ⟨49508326175245984715363405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33005550783497323143575603 49508326175245984715363405)
        ·
          refine ⟨18565622315717244268261277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49508326175245984715363405 18565622315717244268261277)
          ·
            refine ⟨6962108368393966600597979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18565622315717244268261277 6962108368393966600597979)
            ·
              refine ⟨10443162552590949900896969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962108368393966600597979 10443162552590949900896969)
              ·
                refine ⟨7832371914443212425672727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10443162552590949900896969 7832371914443212425672727)
                ·
                  refine ⟨11748557871664818638509091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832371914443212425672727 11748557871664818638509091)
                  ·
                    refine ⟨17622836807497227957763637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11748557871664818638509091 17622836807497227957763637)
                    ·
                      refine ⟨1652140950702865121040341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17622836807497227957763637 1652140950702865121040341)
                      ·
                        rfl

theorem cell23_3217533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_3217533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217533 prefixEnd_3217533 := by exact prefixLift 3217533
  have htrace : WordTrace (prefixWord ++ tailWord_3217533) baseStart_3217533 baseEnd_3217533 := by
    simpa [prefixWord, tailWord_3217533, baseEnd_3217533] using wordTrace_append hprefix tailTrace_3217533
  have hstable : (prefixWord ++ tailWord_3217533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217533).length < 2 ^ (prefixWord ++ tailWord_3217533).sum := by decide
  have hdescent : baseEnd_3217533 < baseStart_3217533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217543 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3217543 : Nat := 118140960795 + 3217543 * 2 ^ 59
def prefixEnd_3217543 : Nat := 4983230072969 + 3 ^ 40 * 3217543 * 2
def baseEnd_3217543 : Nat := 1652146085509410081915295

theorem tailTrace_3217543 : CollatzResearch.WordTrace tailWord_3217543 prefixEnd_3217543 1652146085509410081915295 := by
  unfold tailWord_3217543
  simp only [CollatzResearch.WordTrace]
  refine ⟨117353434182398698440577283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78235622788265798960384855 117353434182398698440577283)
  ·
    refine ⟨176030151273598047660865925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117353434182398698440577283 176030151273598047660865925)
    ·
      refine ⟨33005653363799633936412361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176030151273598047660865925 33005653363799633936412361)
      ·
        refine ⟨24754240022849725452309271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33005653363799633936412361 24754240022849725452309271)
        ·
          refine ⟨37131360034274588178463907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24754240022849725452309271 37131360034274588178463907)
          ·
            refine ⟨55697040051411882267695861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37131360034274588178463907 55697040051411882267695861)
            ·
              refine ⟨5221597504819863962596487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55697040051411882267695861 5221597504819863962596487)
              ·
                refine ⟨7832396257229795943894731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221597504819863962596487 7832396257229795943894731)
                ·
                  refine ⟨11748594385844693915842097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832396257229795943894731 11748594385844693915842097)
                  ·
                    refine ⟨8811445789383520436881573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748594385844693915842097 8811445789383520436881573)
                    ·
                      refine ⟨1652146085509410081915295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8811445789383520436881573 1652146085509410081915295)
                      ·
                        rfl

theorem cell23_3217543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3217543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217543 prefixEnd_3217543 := by exact prefixLift 3217543
  have htrace : WordTrace (prefixWord ++ tailWord_3217543) baseStart_3217543 baseEnd_3217543 := by
    simpa [prefixWord, tailWord_3217543, baseEnd_3217543] using wordTrace_append hprefix tailTrace_3217543
  have hstable : (prefixWord ++ tailWord_3217543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217543).length < 2 ^ (prefixWord ++ tailWord_3217543).sum := by decide
  have hdescent : baseEnd_3217543 < baseStart_3217543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217563 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 3]
def baseStart_3217563 : Nat := 118140960795 + 3217563 * 2 ^ 59
def prefixEnd_3217563 : Nat := 4983230072969 + 3 ^ 40 * 3217563 * 2
def baseEnd_3217563 : Nat := 1652156355122500003665203

theorem tailTrace_3217563 : CollatzResearch.WordTrace tailWord_3217563 prefixEnd_3217563 1652156355122500003665203 := by
  unfold tailWord_3217563
  simp only [CollatzResearch.WordTrace]
  refine ⟨117354163642326241856305343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78236109094884161237536895 117354163642326241856305343)
  ·
    refine ⟨176031245463489362784458015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117354163642326241856305343 176031245463489362784458015)
    ·
      refine ⟨264046868195234044176687023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176031245463489362784458015 264046868195234044176687023)
      ·
        refine ⟨396070302292851066265030535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264046868195234044176687023 396070302292851066265030535)
        ·
          refine ⟨594105453439276599397545803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396070302292851066265030535 594105453439276599397545803)
          ·
            refine ⟨891158180158914899096318705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594105453439276599397545803 891158180158914899096318705)
            ·
              refine ⟨668368635119186174322239029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891158180158914899096318705 668368635119186174322239029)
              ·
                refine ⟨62659559542423703842709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 668368635119186174322239029 62659559542423703842709909)
                ·
                  refine ⟨2937166853551111117627027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62659559542423703842709909 2937166853551111117627027)
                  ·
                    refine ⟨4405750280326666676440541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937166853551111117627027 4405750280326666676440541)
                    ·
                      refine ⟨1652156355122500003665203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405750280326666676440541 1652156355122500003665203)
                      ·
                        rfl

theorem cell23_3217563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 3].length) (baseStart_3217563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217563 prefixEnd_3217563 := by exact prefixLift 3217563
  have htrace : WordTrace (prefixWord ++ tailWord_3217563) baseStart_3217563 baseEnd_3217563 := by
    simpa [prefixWord, tailWord_3217563, baseEnd_3217563] using wordTrace_append hprefix tailTrace_3217563
  have hstable : (prefixWord ++ tailWord_3217563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217563).length < 2 ^ (prefixWord ++ tailWord_3217563).sum := by decide
  have hdescent : baseEnd_3217563 < baseStart_3217563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217601 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3217601 : Nat := 118140960795 + 3217601 * 2 ^ 59
def prefixEnd_3217601 : Nat := 4983230072969 + 3 ^ 40 * 3217601 * 2
def baseEnd_3217601 : Nat := 1652175867387370854990029

theorem tailTrace_3217601 : CollatzResearch.WordTrace tailWord_3217601 prefixEnd_3217601 1652175867387370854990029 := by
  unfold tailWord_3217601
  simp only [CollatzResearch.WordTrace]
  refine ⟨117355549616188574346188657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78237033077459049564125771 117355549616188574346188657)
  ·
    refine ⟨88016662212141430759641493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117355549616188574346188657 88016662212141430759641493)
    ·
      refine ⟨4125781041194129566858195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88016662212141430759641493 4125781041194129566858195)
      ·
        refine ⟨6188671561791194350287293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125781041194129566858195 6188671561791194350287293)
        ·
          refine ⟨2320751835671697881357735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6188671561791194350287293 2320751835671697881357735)
          ·
            refine ⟨3481127753507546822036603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320751835671697881357735 3481127753507546822036603)
            ·
              refine ⟨5221691630261320233054905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481127753507546822036603 5221691630261320233054905)
              ·
                refine ⟨3916268722695990174791179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221691630261320233054905 3916268722695990174791179)
                ·
                  refine ⟨5874403084043985262186769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916268722695990174791179 5874403084043985262186769)
                  ·
                    refine ⟨4405802313032988946640077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874403084043985262186769 4405802313032988946640077)
                    ·
                      refine ⟨1652175867387370854990029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4405802313032988946640077 1652175867387370854990029)
                      ·
                        rfl

theorem cell23_3217601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3217601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217601 prefixEnd_3217601 := by exact prefixLift 3217601
  have htrace : WordTrace (prefixWord ++ tailWord_3217601) baseStart_3217601 baseEnd_3217601 := by
    simpa [prefixWord, tailWord_3217601, baseEnd_3217601] using wordTrace_append hprefix tailTrace_3217601
  have hstable : (prefixWord ++ tailWord_3217601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217601).length < 2 ^ (prefixWord ++ tailWord_3217601).sum := by decide
  have hdescent : baseEnd_3217601 < baseStart_3217601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217624 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_3217624 : Nat := 118140960795 + 3217624 * 2 ^ 59
def prefixEnd_3217624 : Nat := 4983230072969 + 3 ^ 40 * 3217624 * 2
def baseEnd_3217624 : Nat := 1652187677442424265002423

theorem tailTrace_3217624 : CollatzResearch.WordTrace tailWord_3217624 prefixEnd_3217624 1652187677442424265002423 := by
  unfold tailWord_3217624
  simp only [CollatzResearch.WordTrace]
  refine ⟨58678194247552624637137963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78237592330070166182850617 58678194247552624637137963)
  ·
    refine ⟨88017291371328936955706945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58678194247552624637137963 88017291371328936955706945)
    ·
      refine ⟨66012968528496702716780209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88017291371328936955706945 66012968528496702716780209)
      ·
        refine ⟨49509726396372527037585157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66012968528496702716780209 49509726396372527037585157)
        ·
          refine ⟨9283073699319848819547217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49509726396372527037585157 9283073699319848819547217)
          ·
            refine ⟨6962305274489886614660413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9283073699319848819547217 6962305274489886614660413)
            ·
              refine ⟨2610864477933707480497655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6962305274489886614660413 2610864477933707480497655)
              ·
                refine ⟨3916296716900561220746483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610864477933707480497655 3916296716900561220746483)
                ·
                  refine ⟨5874445075350841831119725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916296716900561220746483 5874445075350841831119725)
                  ·
                    refine ⟨2202916903256565686669897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5874445075350841831119725 2202916903256565686669897)
                    ·
                      refine ⟨1652187677442424265002423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202916903256565686669897 1652187677442424265002423)
                      ·
                        rfl

theorem cell23_3217624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_3217624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217624 prefixEnd_3217624 := by exact prefixLift 3217624
  have htrace : WordTrace (prefixWord ++ tailWord_3217624) baseStart_3217624 baseEnd_3217624 := by
    simpa [prefixWord, tailWord_3217624, baseEnd_3217624] using wordTrace_append hprefix tailTrace_3217624
  have hstable : (prefixWord ++ tailWord_3217624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217624).length < 2 ^ (prefixWord ++ tailWord_3217624).sum := by decide
  have hdescent : baseEnd_3217624 < baseStart_3217624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217633 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3217633 : Nat := 118140960795 + 3217633 * 2 ^ 59
def prefixEnd_3217633 : Nat := 4983230072969 + 3 ^ 40 * 3217633 * 2
def baseEnd_3217633 : Nat := 1652192298768314729789881

theorem tailTrace_3217633 : CollatzResearch.WordTrace tailWord_3217633 prefixEnd_3217633 1652192298768314729789881 := by
  unfold tailWord_3217633
  simp only [CollatzResearch.WordTrace]
  refine ⟨117356716752072643811353553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78237811168048429207569035 117356716752072643811353553)
  ·
    refine ⟨88017537564054482858515165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117356716752072643811353553 88017537564054482858515165)
    ·
      refine ⟨33006576586520431071943187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88017537564054482858515165 33006576586520431071943187)
      ·
        refine ⟨49509864879780646607914781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33006576586520431071943187 49509864879780646607914781)
        ·
          refine ⟨18566199329917742477968043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49509864879780646607914781 18566199329917742477968043)
          ·
            refine ⟨27849298994876613716952065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18566199329917742477968043 27849298994876613716952065)
            ·
              refine ⟨20886974246157460287714049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27849298994876613716952065 20886974246157460287714049)
              ·
                refine ⟨15665230684618095215785537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20886974246157460287714049 15665230684618095215785537)
                ·
                  refine ⟨11748923013463571411839153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15665230684618095215785537 11748923013463571411839153)
                  ·
                    refine ⟨8811692260097678558879365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748923013463571411839153 8811692260097678558879365)
                    ·
                      refine ⟨1652192298768314729789881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8811692260097678558879365 1652192298768314729789881)
                      ·
                        rfl

theorem cell23_3217633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3217633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217633 prefixEnd_3217633 := by exact prefixLift 3217633
  have htrace : WordTrace (prefixWord ++ tailWord_3217633) baseStart_3217633 baseEnd_3217633 := by
    simpa [prefixWord, tailWord_3217633, baseEnd_3217633] using wordTrace_append hprefix tailTrace_3217633
  have hstable : (prefixWord ++ tailWord_3217633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217633).length < 2 ^ (prefixWord ++ tailWord_3217633).sum := by decide
  have hdescent : baseEnd_3217633 < baseStart_3217633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217650 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3217650 : Nat := 118140960795 + 3217650 * 2 ^ 59
def prefixEnd_3217650 : Nat := 4983230072969 + 3 ^ 40 * 3217650 * 2
def baseEnd_3217650 : Nat := 1652201027939441163277303

theorem tailTrace_3217650 : CollatzResearch.WordTrace tailWord_3217650 prefixEnd_3217650 1652201027939441163277303 := by
  unfold tailWord_3217650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339334198252763928680601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78238224528674037143148269 29339334198252763928680601)
  ·
    refine ⟨22004500648689572946510451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29339334198252763928680601 22004500648689572946510451)
    ·
      refine ⟨33006750973034359419765677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22004500648689572946510451 33006750973034359419765677)
      ·
        refine ⟨12377531614887884782412129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33006750973034359419765677 12377531614887884782412129)
        ·
          refine ⟨9283148711165913586809097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12377531614887884782412129 9283148711165913586809097)
          ·
            refine ⟨6962361533374435190106823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9283148711165913586809097 6962361533374435190106823)
            ·
              refine ⟨10443542300061652785160235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962361533374435190106823 10443542300061652785160235)
              ·
                refine ⟨15665313450092479177740353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443542300061652785160235 15665313450092479177740353)
                ·
                  refine ⟨11748985087569359383305265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15665313450092479177740353 11748985087569359383305265)
                  ·
                    refine ⟨8811738815677019537478949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748985087569359383305265 8811738815677019537478949)
                    ·
                      refine ⟨1652201027939441163277303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8811738815677019537478949 1652201027939441163277303)
                      ·
                        rfl

theorem cell23_3217650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3217650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217650 prefixEnd_3217650 := by exact prefixLift 3217650
  have htrace : WordTrace (prefixWord ++ tailWord_3217650) baseStart_3217650 baseEnd_3217650 := by
    simpa [prefixWord, tailWord_3217650, baseEnd_3217650] using wordTrace_append hprefix tailTrace_3217650
  have hstable : (prefixWord ++ tailWord_3217650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217650).length < 2 ^ (prefixWord ++ tailWord_3217650).sum := by decide
  have hdescent : baseEnd_3217650 < baseStart_3217650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217654 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3217654 : Nat := 118140960795 + 3217654 * 2 ^ 59
def prefixEnd_3217654 : Nat := 4983230072969 + 3 ^ 40 * 3217654 * 2
def baseEnd_3217654 : Nat := 1652203081862059147627285

theorem tailTrace_3217654 : CollatzResearch.WordTrace tailWord_3217654 prefixEnd_3217654 1652203081862059147627285 := by
  unfold tailWord_3217654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334842667812285274866751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78238321789997709598578677 7334842667812285274866751)
  ·
    refine ⟨11002264001718427912300127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7334842667812285274866751 11002264001718427912300127)
    ·
      refine ⟨16503396002577641868450191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11002264001718427912300127 16503396002577641868450191)
      ·
        refine ⟨24755094003866462802675287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503396002577641868450191 24755094003866462802675287)
        ·
          refine ⟨37132641005799694204012931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24755094003866462802675287 37132641005799694204012931)
          ·
            refine ⟨55698961508699541306019397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37132641005799694204012931 55698961508699541306019397)
            ·
              refine ⟨10443555282881163994878637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55698961508699541306019397 10443555282881163994878637)
              ·
                refine ⟨3916333231080436498079489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10443555282881163994878637 3916333231080436498079489)
                ·
                  refine ⟨2937249923310327373559617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916333231080436498079489 2937249923310327373559617)
                  ·
                    refine ⟨2202937442482745530169713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2937249923310327373559617 2202937442482745530169713)
                    ·
                      refine ⟨1652203081862059147627285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202937442482745530169713 1652203081862059147627285)
                      ·
                        rfl

theorem cell23_3217654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3217654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217654 prefixEnd_3217654 := by exact prefixLift 3217654
  have htrace : WordTrace (prefixWord ++ tailWord_3217654) baseStart_3217654 baseEnd_3217654 := by
    simpa [prefixWord, tailWord_3217654, baseEnd_3217654] using wordTrace_append hprefix tailTrace_3217654
  have hstable : (prefixWord ++ tailWord_3217654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217654).length < 2 ^ (prefixWord ++ tailWord_3217654).sum := by decide
  have hdescent : baseEnd_3217654 < baseStart_3217654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217673 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_3217673 : Nat := 118140960795 + 3217673 * 2 ^ 59
def prefixEnd_3217673 : Nat := 4983230072969 + 3 ^ 40 * 3217673 * 2
def baseEnd_3217673 : Nat := 550737612664831524429899

theorem tailTrace_3217673 : CollatzResearch.WordTrace tailWord_3217673 prefixEnd_3217673 550737612664831524429899 := by
  unfold tailWord_3217673
  simp only [CollatzResearch.WordTrace]
  refine ⟨117358175671927730642809673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78238783781285153761873115 117358175671927730642809673)
  ·
    refine ⟨88018631753945797982107255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117358175671927730642809673 88018631753945797982107255)
    ·
      refine ⟨132027947630918696973160883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88018631753945797982107255 132027947630918696973160883)
      ·
        refine ⟨198041921446378045459741325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132027947630918696973160883 198041921446378045459741325)
        ·
          refine ⟨74265720542391767047402997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198041921446378045459741325 74265720542391767047402997)
          ·
            refine ⟨6962411300849228160694031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74265720542391767047402997 6962411300849228160694031)
            ·
              refine ⟨10443616951273842241041047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962411300849228160694031 10443616951273842241041047)
              ·
                refine ⟨15665425426910763361561571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443616951273842241041047 15665425426910763361561571)
                ·
                  refine ⟨23498138140366145042342357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15665425426910763361561571 23498138140366145042342357)
                  ·
                    refine ⟨550737612664831524429899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23498138140366145042342357 550737612664831524429899)
                    ·
                      rfl

theorem cell23_3217673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_3217673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217673 prefixEnd_3217673 := by exact prefixLift 3217673
  have htrace : WordTrace (prefixWord ++ tailWord_3217673) baseStart_3217673 baseEnd_3217673 := by
    simpa [prefixWord, tailWord_3217673, baseEnd_3217673] using wordTrace_append hprefix tailTrace_3217673
  have hstable : (prefixWord ++ tailWord_3217673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217673).length < 2 ^ (prefixWord ++ tailWord_3217673).sum := by decide
  have hdescent : baseEnd_3217673 < baseStart_3217673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217694 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3217694 : Nat := 118140960795 + 3217694 * 2 ^ 59
def prefixEnd_3217694 : Nat := 4983230072969 + 3 ^ 40 * 3217694 * 2
def baseEnd_3217694 : Nat := 183580402343137665680789

theorem tailTrace_3217694 : CollatzResearch.WordTrace tailWord_3217694 prefixEnd_3217694 183580402343137665680789 := by
  unfold tailWord_3217694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669867700606456403665517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78239294403234434152882757 14669867700606456403665517)
  ·
    refine ⟨5501200387727421151374569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14669867700606456403665517 5501200387727421151374569)
    ·
      refine ⟨4125900290795565863530927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5501200387727421151374569 4125900290795565863530927)
      ·
        refine ⟨6188850436193348795296391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125900290795565863530927 6188850436193348795296391)
        ·
          refine ⟨9283275654290023192944587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188850436193348795296391 9283275654290023192944587)
          ·
            refine ⟨13924913481435034789416881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283275654290023192944587 13924913481435034789416881)
            ·
              refine ⟨10443685111076276092062661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13924913481435034789416881 10443685111076276092062661)
              ·
                refine ⟨1958190958326801767261749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10443685111076276092062661 1958190958326801767261749)
                ·
                  refine ⟨183580402343137665680789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958190958326801767261749 183580402343137665680789)
                  ·
                    rfl

theorem cell23_3217694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3217694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217694 prefixEnd_3217694 := by exact prefixLift 3217694
  have htrace : WordTrace (prefixWord ++ tailWord_3217694) baseStart_3217694 baseEnd_3217694 := by
    simpa [prefixWord, tailWord_3217694, baseEnd_3217694] using wordTrace_append hprefix tailTrace_3217694
  have hstable : (prefixWord ++ tailWord_3217694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217694).length < 2 ^ (prefixWord ++ tailWord_3217694).sum := by decide
  have hdescent : baseEnd_3217694 < baseStart_3217694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217720 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_3217720 : Nat := 118140960795 + 3217720 * 2 ^ 59
def prefixEnd_3217720 : Nat := 4983230072969 + 3 ^ 40 * 3217720 * 2
def baseEnd_3217720 : Nat := 550745657195085296467327

theorem tailTrace_3217720 : CollatzResearch.WordTrace tailWord_3217720 prefixEnd_3217720 550745657195085296467327 := by
  unfold tailWord_3217720
  simp only [CollatzResearch.WordTrace]
  refine ⟨58679944951378728834885307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78239926601838305113180409 58679944951378728834885307)
  ·
    refine ⟨88019917427068093252327961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58679944951378728834885307 88019917427068093252327961)
    ·
      refine ⟨66014938070301069939245971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88019917427068093252327961 66014938070301069939245971)
      ·
        refine ⟨99022407105451604908868957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66014938070301069939245971 99022407105451604908868957)
        ·
          refine ⟨37133402664544351840825859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99022407105451604908868957 37133402664544351840825859)
          ·
            refine ⟨55700103996816527761238789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37133402664544351840825859 55700103996816527761238789)
            ·
              refine ⟨10443769499403098955232273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55700103996816527761238789 10443769499403098955232273)
              ·
                refine ⟨7832827124552324216424205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10443769499403098955232273 7832827124552324216424205)
                ·
                  refine ⟨2937310171707121581159077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7832827124552324216424205 2937310171707121581159077)
                  ·
                    refine ⟨550745657195085296467327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937310171707121581159077 550745657195085296467327)
                    ·
                      rfl

theorem cell23_3217720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_3217720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217720 prefixEnd_3217720 := by exact prefixLift 3217720
  have htrace : WordTrace (prefixWord ++ tailWord_3217720) baseStart_3217720 baseEnd_3217720 := by
    simpa [prefixWord, tailWord_3217720, baseEnd_3217720] using wordTrace_append hprefix tailTrace_3217720
  have hstable : (prefixWord ++ tailWord_3217720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217720).length < 2 ^ (prefixWord ++ tailWord_3217720).sum := by decide
  have hdescent : baseEnd_3217720 < baseStart_3217720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217767 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 6]
def baseStart_3217767 : Nat := 118140960795 + 3217767 * 2 ^ 59
def prefixEnd_3217767 : Nat := 4983230072969 + 3 ^ 40 * 3217767 * 2
def baseEnd_3217767 : Nat := 183584567241779689501585

theorem tailTrace_3217767 : CollatzResearch.WordTrace tailWord_3217767 prefixEnd_3217767 183584567241779689501585 := by
  unfold tailWord_3217767
  simp only [CollatzResearch.WordTrace]
  refine ⟨117361604133587184696731555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78241069422391456464487703 117361604133587184696731555)
  ·
    refine ⟨176042406200380777045097333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117361604133587184696731555 176042406200380777045097333)
    ·
      refine ⟨16503975581285697847977875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176042406200380777045097333 16503975581285697847977875)
      ·
        refine ⟨24755963371928546771966813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503975581285697847977875 24755963371928546771966813)
        ·
          refine ⟨9283486264473205039487555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24755963371928546771966813 9283486264473205039487555)
          ·
            refine ⟨13925229396709807559231333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283486264473205039487555 13925229396709807559231333)
            ·
              refine ⟨2610980511883088917355875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13925229396709807559231333 2610980511883088917355875)
              ·
                refine ⟨3916470767824633376033813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610980511883088917355875 3916470767824633376033813)
                ·
                  refine ⟨183584567241779689501585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3916470767824633376033813 183584567241779689501585)
                  ·
                    rfl

theorem cell23_3217767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 6].length) (baseStart_3217767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217767 prefixEnd_3217767 := by exact prefixLift 3217767
  have htrace : WordTrace (prefixWord ++ tailWord_3217767) baseStart_3217767 baseEnd_3217767 := by
    simpa [prefixWord, tailWord_3217767, baseEnd_3217767] using wordTrace_append hprefix tailTrace_3217767
  have hstable : (prefixWord ++ tailWord_3217767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217767).length < 2 ^ (prefixWord ++ tailWord_3217767).sum := by decide
  have hdescent : baseEnd_3217767 < baseStart_3217767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217787 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 2, 3, 2]
def baseStart_3217787 : Nat := 118140960795 + 3217787 * 2 ^ 59
def prefixEnd_3217787 : Nat := 4983230072969 + 3 ^ 40 * 3217787 * 2
def baseEnd_3217787 : Nat := 1652271374789107127264173

theorem tailTrace_3217787 : CollatzResearch.WordTrace tailWord_3217787 prefixEnd_3217787 1652271374789107127264173 := by
  unfold tailWord_3217787
  simp only [CollatzResearch.WordTrace]
  refine ⟨117362333593514728112459615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78241555729009818741639743 117362333593514728112459615)
  ·
    refine ⟨176043500390272092168689423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117362333593514728112459615 176043500390272092168689423)
    ·
      refine ⟨264065250585408138253034135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176043500390272092168689423 264065250585408138253034135)
      ·
        refine ⟨396097875878112207379551203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264065250585408138253034135 396097875878112207379551203)
        ·
          refine ⟨594146813817168311069326805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396097875878112207379551203 594146813817168311069326805)
          ·
            refine ⟨13925315948839882290687347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 594146813817168311069326805 13925315948839882290687347)
            ·
              refine ⟨20887973923259823436031021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925315948839882290687347 20887973923259823436031021)
              ·
                refine ⟨7832990221222433788511633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20887973923259823436031021 7832990221222433788511633)
                ·
                  refine ⟨5874742665916825341383725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832990221222433788511633 5874742665916825341383725)
                  ·
                    refine ⟨2203028499718809503018897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5874742665916825341383725 2203028499718809503018897)
                    ·
                      refine ⟨1652271374789107127264173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203028499718809503018897 1652271374789107127264173)
                      ·
                        rfl

theorem cell23_3217787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3, 2].length) (baseStart_3217787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217787 prefixEnd_3217787 := by exact prefixLift 3217787
  have htrace : WordTrace (prefixWord ++ tailWord_3217787) baseStart_3217787 baseEnd_3217787 := by
    simpa [prefixWord, tailWord_3217787, baseEnd_3217787] using wordTrace_append hprefix tailTrace_3217787
  have hstable : (prefixWord ++ tailWord_3217787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217787).length < 2 ^ (prefixWord ++ tailWord_3217787).sum := by decide
  have hdescent : baseEnd_3217787 < baseStart_3217787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217827 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 2, 4]
def baseStart_3217827 : Nat := 118140960795 + 3217827 * 2 ^ 59
def prefixEnd_3217827 : Nat := 4983230072969 + 3 ^ 40 * 3217827 * 2
def baseEnd_3217827 : Nat := 550763971338428990254663

theorem tailTrace_3217827 : CollatzResearch.WordTrace tailWord_3217827 prefixEnd_3217827 550763971338428990254663 := by
  unfold tailWord_3217827
  simp only [CollatzResearch.WordTrace]
  refine ⟨117363792513369814943915735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78242528342246543295943823 117363792513369814943915735)
  ·
    refine ⟨176045688770054722415873603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117363792513369814943915735 176045688770054722415873603)
    ·
      refine ⟨264068533155082083623810405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176045688770054722415873603 264068533155082083623810405)
      ·
        refine ⟨49512849966577890679464451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264068533155082083623810405 49512849966577890679464451)
        ·
          refine ⟨74269274949866836019196677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49512849966577890679464451 74269274949866836019196677)
          ·
            refine ⟨13925489053100031753599377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74269274949866836019196677 13925489053100031753599377)
            ·
              refine ⟨10444116789825023815199533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13925489053100031753599377 10444116789825023815199533)
              ·
                refine ⟨3916543796184383930699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10444116789825023815199533 3916543796184383930699825)
                ·
                  refine ⟨2937407847138287948024869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916543796184383930699825 2937407847138287948024869)
                  ·
                    refine ⟨550763971338428990254663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937407847138287948024869 550763971338428990254663)
                    ·
                      rfl

theorem cell23_3217827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 4].length) (baseStart_3217827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217827 prefixEnd_3217827 := by exact prefixLift 3217827
  have htrace : WordTrace (prefixWord ++ tailWord_3217827) baseStart_3217827 baseEnd_3217827 := by
    simpa [prefixWord, tailWord_3217827, baseEnd_3217827] using wordTrace_append hprefix tailTrace_3217827
  have hstable : (prefixWord ++ tailWord_3217827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217827).length < 2 ^ (prefixWord ++ tailWord_3217827).sum := by decide
  have hdescent : baseEnd_3217827 < baseStart_3217827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3217833 : Nat := 118140960795 + 3217833 * 2 ^ 59
def prefixEnd_3217833 : Nat := 4983230072969 + 3 ^ 40 * 3217833 * 2
def baseEnd_3217833 : Nat := 1652294994899213947288961

theorem tailTrace_3217833 : CollatzResearch.WordTrace tailWord_3217833 prefixEnd_3217833 1652294994899213947288961 := by
  unfold tailWord_3217833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117364011351348077968634153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78242674234232051979089435 117364011351348077968634153)
  ·
    refine ⟨88023008513511058476475615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117364011351348077968634153 88023008513511058476475615)
    ·
      refine ⟨132034512770266587714713423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88023008513511058476475615 132034512770266587714713423)
      ·
        refine ⟨198051769155399881572070135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132034512770266587714713423 198051769155399881572070135)
        ·
          refine ⟨297077653733099822358105203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198051769155399881572070135 297077653733099822358105203)
          ·
            refine ⟨445616480599649733537157805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297077653733099822358105203 445616480599649733537157805)
            ·
              refine ⟨167106180224868650076434177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445616480599649733537157805 167106180224868650076434177)
              ·
                refine ⟨125329635168651487557325633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167106180224868650076434177 125329635168651487557325633)
                ·
                  refine ⟨93997226376488615667994225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125329635168651487557325633 93997226376488615667994225)
                  ·
                    refine ⟨70497919782366461750995669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93997226376488615667994225 70497919782366461750995669)
                    ·
                      refine ⟨1652294994899213947288961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70497919782366461750995669 1652294994899213947288961)
                      ·
                        rfl

theorem cell23_3217833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3217833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217833 prefixEnd_3217833 := by exact prefixLift 3217833
  have htrace : WordTrace (prefixWord ++ tailWord_3217833) baseStart_3217833 baseEnd_3217833 := by
    simpa [prefixWord, tailWord_3217833, baseEnd_3217833] using wordTrace_append hprefix tailTrace_3217833
  have hstable : (prefixWord ++ tailWord_3217833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217833).length < 2 ^ (prefixWord ++ tailWord_3217833).sum := by decide
  have hdescent : baseEnd_3217833 < baseStart_3217833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217907 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 4, 2]
def baseStart_3217907 : Nat := 118140960795 + 3217907 * 2 ^ 59
def prefixEnd_3217907 : Nat := 4983230072969 + 3 ^ 40 * 3217907 * 2
def baseEnd_3217907 : Nat := 1652332992467646657763621

theorem tailTrace_3217907 : CollatzResearch.WordTrace tailWord_3217907 prefixEnd_3217907 1652332992467646657763621 := by
  unfold tailWord_3217907
  simp only [CollatzResearch.WordTrace]
  refine ⟨117366710353079988606827975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78244473568719992404551983 117366710353079988606827975)
  ·
    refine ⟨176050065529619982910241963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117366710353079988606827975 176050065529619982910241963)
    ·
      refine ⟨264075098294429974365362945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176050065529619982910241963 264075098294429974365362945)
      ·
        refine ⟨198056323720822480774022209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264075098294429974365362945 198056323720822480774022209)
        ·
          refine ⟨148542242790616860580516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198056323720822480774022209 148542242790616860580516657)
          ·
            refine ⟨111406682092962645435387493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148542242790616860580516657 111406682092962645435387493)
            ·
              refine ⟨20888752892430496019135155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111406682092962645435387493 20888752892430496019135155)
              ·
                refine ⟨31333129338645744028702733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20888752892430496019135155 31333129338645744028702733)
                ·
                  refine ⟨11749923501992154010763525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31333129338645744028702733 11749923501992154010763525)
                  ·
                    refine ⟨2203110656623528877018161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11749923501992154010763525 2203110656623528877018161)
                    ·
                      refine ⟨1652332992467646657763621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203110656623528877018161 1652332992467646657763621)
                      ·
                        rfl

theorem cell23_3217907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4, 2].length) (baseStart_3217907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217907 prefixEnd_3217907 := by exact prefixLift 3217907
  have htrace : WordTrace (prefixWord ++ tailWord_3217907) baseStart_3217907 baseEnd_3217907 := by
    simpa [prefixWord, tailWord_3217907, baseEnd_3217907] using wordTrace_append hprefix tailTrace_3217907
  have hstable : (prefixWord ++ tailWord_3217907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217907).length < 2 ^ (prefixWord ++ tailWord_3217907).sum := by decide
  have hdescent : baseEnd_3217907 < baseStart_3217907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217941 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_3217941 : Nat := 118140960795 + 3217941 * 2 ^ 59
def prefixEnd_3217941 : Nat := 4983230072969 + 3 ^ 40 * 3217941 * 2
def baseEnd_3217941 : Nat := 1652350450809899524738465

theorem tailTrace_3217941 : CollatzResearch.WordTrace tailWord_3217941 prefixEnd_3217941 1652350450809899524738465 := by
  unfold tailWord_3217941
  simp only [CollatzResearch.WordTrace]
  refine ⟨117367950434956812413565677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78245300289971208275710451 117367950434956812413565677)
  ·
    refine ⟨44012981413108804655087129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117367950434956812413565677 44012981413108804655087129)
    ·
      refine ⟨33009736059831603491315347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44012981413108804655087129 33009736059831603491315347)
      ·
        refine ⟨49514604089747405236973021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33009736059831603491315347 49514604089747405236973021)
        ·
          refine ⟨18567976533655276963864883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49514604089747405236973021 18567976533655276963864883)
          ·
            refine ⟨27851964800482915445797325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18567976533655276963864883 27851964800482915445797325)
            ·
              refine ⟨10444486800181093292173997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27851964800482915445797325 10444486800181093292173997)
              ·
                refine ⟨3916682550067909984565249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10444486800181093292173997 3916682550067909984565249)
                ·
                  refine ⟨2937511912550932488423937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916682550067909984565249 2937511912550932488423937)
                  ·
                    refine ⟨2203133934413199366317953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2937511912550932488423937 2203133934413199366317953)
                    ·
                      refine ⟨1652350450809899524738465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203133934413199366317953 1652350450809899524738465)
                      ·
                        rfl

theorem cell23_3217941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_3217941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217941 prefixEnd_3217941 := by exact prefixLift 3217941
  have htrace : WordTrace (prefixWord ++ tailWord_3217941) baseStart_3217941 baseEnd_3217941 := by
    simpa [prefixWord, tailWord_3217941, baseEnd_3217941] using wordTrace_append hprefix tailTrace_3217941
  have hstable : (prefixWord ++ tailWord_3217941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217941).length < 2 ^ (prefixWord ++ tailWord_3217941).sum := by decide
  have hdescent : baseEnd_3217941 < baseStart_3217941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217967 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 5, 2]
def baseStart_3217967 : Nat := 118140960795 + 3217967 * 2 ^ 59
def prefixEnd_3217967 : Nat := 4983230072969 + 3 ^ 40 * 3217967 * 2
def baseEnd_3217967 : Nat := 1652363801306916423013345

theorem tailTrace_3217967 : CollatzResearch.WordTrace tailWord_3217967 prefixEnd_3217967 1652363801306916423013345 := by
  unfold tailWord_3217967
  simp only [CollatzResearch.WordTrace]
  refine ⟨117368898732862618854012155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78245932488575079236008103 117368898732862618854012155)
  ·
    refine ⟨176053348099293928281018233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117368898732862618854012155 176053348099293928281018233)
    ·
      refine ⟨132040011074470446210763675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176053348099293928281018233 132040011074470446210763675)
      ·
        refine ⟨198060016611705669316145513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132040011074470446210763675 198060016611705669316145513)
        ·
          refine ⟨148545012458779251987109135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198060016611705669316145513 148545012458779251987109135)
          ·
            refine ⟨222817518688168877980663703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148545012458779251987109135 222817518688168877980663703)
            ·
              refine ⟨334226278032253316970995555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222817518688168877980663703 334226278032253316970995555)
              ·
                refine ⟨501339417048379975456493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334226278032253316970995555 501339417048379975456493333)
                ·
                  refine ⟨23500285174142811349523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 501339417048379975456493333 23500285174142811349523125)
                  ·
                    refine ⟨2203151735075888564017793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23500285174142811349523125 2203151735075888564017793)
                    ·
                      refine ⟨1652363801306916423013345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203151735075888564017793 1652363801306916423013345)
                      ·
                        rfl

theorem cell23_3217967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5, 2].length) (baseStart_3217967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217967 prefixEnd_3217967 := by exact prefixLift 3217967
  have htrace : WordTrace (prefixWord ++ tailWord_3217967) baseStart_3217967 baseEnd_3217967 := by
    simpa [prefixWord, tailWord_3217967, baseEnd_3217967] using wordTrace_append hprefix tailTrace_3217967
  have hstable : (prefixWord ++ tailWord_3217967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217967).length < 2 ^ (prefixWord ++ tailWord_3217967).sum := by decide
  have hdescent : baseEnd_3217967 < baseStart_3217967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217977 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_3217977 : Nat := 118140960795 + 3217977 * 2 ^ 59
def prefixEnd_3217977 : Nat := 4983230072969 + 3 ^ 40 * 3217977 * 2
def baseEnd_3217977 : Nat := 550789645371153794629433

theorem tailTrace_3217977 : CollatzResearch.WordTrace tailWord_3217977 prefixEnd_3217977 550789645371153794629433 := by
  unfold tailWord_3217977
  simp only [CollatzResearch.WordTrace]
  refine ⟨117369263462826390561876185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78246175641884260374584123 117369263462826390561876185)
  ·
    refine ⟨88026947597119792921407139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117369263462826390561876185 88026947597119792921407139)
    ·
      refine ⟨132040421395679689382110709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88026947597119792921407139 132040421395679689382110709)
      ·
        refine ⟨12378789505844970879572879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132040421395679689382110709 12378789505844970879572879)
        ·
          refine ⟨18568184258767456319359319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378789505844970879572879 18568184258767456319359319)
          ·
            refine ⟨27852276388151184479038979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568184258767456319359319 27852276388151184479038979)
            ·
              refine ⟨41778414582226776718558469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27852276388151184479038979 41778414582226776718558469)
              ·
                refine ⟨7833452734167520634729713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41778414582226776718558469 7833452734167520634729713)
                ·
                  refine ⟨5875089550625640476047285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833452734167520634729713 5875089550625640476047285)
                  ·
                    refine ⟨550789645371153794629433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5875089550625640476047285 550789645371153794629433)
                    ·
                      rfl

theorem cell23_3217977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_3217977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217977 prefixEnd_3217977 := by exact prefixLift 3217977
  have htrace : WordTrace (prefixWord ++ tailWord_3217977) baseStart_3217977 baseEnd_3217977 := by
    simpa [prefixWord, tailWord_3217977, baseEnd_3217977] using wordTrace_append hprefix tailTrace_3217977
  have hstable : (prefixWord ++ tailWord_3217977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217977).length < 2 ^ (prefixWord ++ tailWord_3217977).sum := by decide
  have hdescent : baseEnd_3217977 < baseStart_3217977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217981 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 5]
def baseStart_3217981 : Nat := 118140960795 + 3217981 * 2 ^ 59
def prefixEnd_3217981 : Nat := 4983230072969 + 3 ^ 40 * 3217981 * 2
def baseEnd_3217981 : Nat := 183596776670675485359809

theorem tailTrace_3217981 : CollatzResearch.WordTrace tailWord_3217981 prefixEnd_3217981 183596776670675485359809 := by
  unfold tailWord_3217981
  simp only [CollatzResearch.WordTrace]
  refine ⟨117369409354811899245021797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78246272903207932830014531 117369409354811899245021797)
  ·
    refine ⟨22006764254027231108441587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117369409354811899245021797 22006764254027231108441587)
    ·
      refine ⟨33010146381040846662662381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22006764254027231108441587 33010146381040846662662381)
      ·
        refine ⟨12378804892890317498498393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33010146381040846662662381 12378804892890317498498393)
        ·
          refine ⟨9284103669667738123873795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12378804892890317498498393 9284103669667738123873795)
          ·
            refine ⟨13926155504501607185810693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9284103669667738123873795 13926155504501607185810693)
            ·
              refine ⟨2611154157094051347339505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13926155504501607185810693 2611154157094051347339505)
              ·
                refine ⟨1958365617820538510504629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611154157094051347339505 1958365617820538510504629)
                ·
                  refine ⟨183596776670675485359809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958365617820538510504629 183596776670675485359809)
                  ·
                    rfl

theorem cell23_3217981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_3217981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217981 prefixEnd_3217981 := by exact prefixLift 3217981
  have htrace : WordTrace (prefixWord ++ tailWord_3217981) baseStart_3217981 baseEnd_3217981 := by
    simpa [prefixWord, tailWord_3217981, baseEnd_3217981] using wordTrace_append hprefix tailTrace_3217981
  have hstable : (prefixWord ++ tailWord_3217981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217981).length < 2 ^ (prefixWord ++ tailWord_3217981).sum := by decide
  have hdescent : baseEnd_3217981 < baseStart_3217981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217988 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3217988 : Nat := 118140960795 + 3217988 * 2 ^ 59
def prefixEnd_3217988 : Nat := 4983230072969 + 3 ^ 40 * 3217988 * 2
def baseEnd_3217988 : Nat := 1652374584400660840850749

theorem tailTrace_3217988 : CollatzResearch.WordTrace tailWord_3217988 prefixEnd_3217988 1652374584400660840850749 := by
  unfold tailWord_3217988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58684832332893269720263309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78246443110524359627017745 58684832332893269720263309)
  ·
    refine ⟨22006812124834976145098741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58684832332893269720263309 22006812124834976145098741)
    ·
      refine ⟨2063138636703279013603007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22006812124834976145098741 2063138636703279013603007)
      ·
        refine ⟨3094707955054918520404511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063138636703279013603007 3094707955054918520404511)
        ·
          refine ⟨4642061932582377780606767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094707955054918520404511 4642061932582377780606767)
          ·
            refine ⟨6963092898873566670910151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642061932582377780606767 6963092898873566670910151)
            ·
              refine ⟨10444639348310350006365227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963092898873566670910151 10444639348310350006365227)
              ·
                refine ⟨15666959022465525009547841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10444639348310350006365227 15666959022465525009547841)
                ·
                  refine ⟨11750219266849143757160881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15666959022465525009547841 11750219266849143757160881)
                  ·
                    refine ⟨8812664450136857817870661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11750219266849143757160881 8812664450136857817870661)
                    ·
                      refine ⟨1652374584400660840850749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8812664450136857817870661 1652374584400660840850749)
                      ·
                        rfl

theorem cell23_3217988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3217988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3217988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3217988 prefixEnd_3217988 := by exact prefixLift 3217988
  have htrace : WordTrace (prefixWord ++ tailWord_3217988) baseStart_3217988 baseEnd_3217988 := by
    simpa [prefixWord, tailWord_3217988, baseEnd_3217988] using wordTrace_append hprefix tailTrace_3217988
  have hstable : (prefixWord ++ tailWord_3217988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217988).length < 2 ^ (prefixWord ++ tailWord_3217988).sum := by decide
  have hdescent : baseEnd_3217988 < baseStart_3217988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218041 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 1, 4]
def baseStart_3218041 : Nat := 118140960795 + 3218041 * 2 ^ 59
def prefixEnd_3218041 : Nat := 4983230072969 + 3 ^ 40 * 3218041 * 2
def baseEnd_3218041 : Nat := 550800599625116377829335

theorem tailTrace_3218041 : CollatzResearch.WordTrace tailWord_3218041 prefixEnd_3218041 550800599625116377829335 := by
  unfold tailWord_3218041
  simp only [CollatzResearch.WordTrace]
  refine ⟨117371597734594529492205977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78247731823063019661470651 117371597734594529492205977)
  ·
    refine ⟨88028698300945897119154483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117371597734594529492205977 88028698300945897119154483)
    ·
      refine ⟨132043047451418845678731725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88028698300945897119154483 132043047451418845678731725)
      ·
        refine ⟨49516142794282067129524397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132043047451418845678731725 49516142794282067129524397)
        ·
          refine ⟨18568553547855775173571649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49516142794282067129524397 18568553547855775173571649)
          ·
            refine ⟨13926415160891831380178737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18568553547855775173571649 13926415160891831380178737)
            ·
              refine ⟨10444811370668873535134053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13926415160891831380178737 10444811370668873535134053)
              ·
                refine ⟨1958402132000413787837635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10444811370668873535134053 1958402132000413787837635)
                ·
                  refine ⟨2937603198000620681756453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958402132000413787837635 2937603198000620681756453)
                  ·
                    refine ⟨550800599625116377829335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937603198000620681756453 550800599625116377829335)
                    ·
                      rfl

theorem cell23_3218041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_3218041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218041 prefixEnd_3218041 := by exact prefixLift 3218041
  have htrace : WordTrace (prefixWord ++ tailWord_3218041) baseStart_3218041 baseEnd_3218041 := by
    simpa [prefixWord, tailWord_3218041, baseEnd_3218041] using wordTrace_append hprefix tailTrace_3218041
  have hstable : (prefixWord ++ tailWord_3218041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218041).length < 2 ^ (prefixWord ++ tailWord_3218041).sum := by decide
  have hdescent : baseEnd_3218041 < baseStart_3218041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218084 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_3218084 : Nat := 118140960795 + 3218084 * 2 ^ 59
def prefixEnd_3218084 : Nat := 4983230072969 + 3 ^ 40 * 3218084 * 2
def baseEnd_3218084 : Nat := 550807959514497488416769

theorem tailTrace_3218084 : CollatzResearch.WordTrace tailWord_3218084 prefixEnd_3218084 550807959514497488416769 := by
  unfold tailWord_3218084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58686583036719373918010653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78248777382292498557347537 58686583036719373918010653)
  ·
    refine ⟨22007468638769765219253995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58686583036719373918010653 22007468638769765219253995)
    ·
      refine ⟨33011202958154647828880993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22007468638769765219253995 33011202958154647828880993)
      ·
        refine ⟨24758402218615985871660745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33011202958154647828880993 24758402218615985871660745)
        ·
          refine ⟨18568801663961989403745559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24758402218615985871660745 18568801663961989403745559)
          ·
            refine ⟨27853202495942984105618339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568801663961989403745559 27853202495942984105618339)
            ·
              refine ⟨41779803743914476158427509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27853202495942984105618339 41779803743914476158427509)
              ·
                refine ⟨3916856600991982139852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41779803743914476158427509 3916856600991982139852579)
                ·
                  refine ⟨5875284901487973209778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916856600991982139852579 5875284901487973209778869)
                  ·
                    refine ⟨550807959514497488416769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5875284901487973209778869 550807959514497488416769)
                    ·
                      rfl

theorem cell23_3218084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_3218084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218084 prefixEnd_3218084 := by exact prefixLift 3218084
  have htrace : WordTrace (prefixWord ++ tailWord_3218084) baseStart_3218084 baseEnd_3218084 := by
    simpa [prefixWord, tailWord_3218084, baseEnd_3218084] using wordTrace_append hprefix tailTrace_3218084
  have hstable : (prefixWord ++ tailWord_3218084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218084).length < 2 ^ (prefixWord ++ tailWord_3218084).sum := by decide
  have hdescent : baseEnd_3218084 < baseStart_3218084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218107 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3]
def baseStart_3218107 : Nat := 118140960795 + 3218107 * 2 ^ 59
def prefixEnd_3218107 : Nat := 4983230072969 + 3 ^ 40 * 3218107 * 2
def baseEnd_3218107 : Nat := 1652435688598545875262701

theorem tailTrace_3218107 : CollatzResearch.WordTrace tailWord_3218107 prefixEnd_3218107 1652435688598545875262701 := by
  unfold tailWord_3218107
  simp only [CollatzResearch.WordTrace]
  refine ⟨117374004952355422764108575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78249336634903615176072383 117374004952355422764108575)
  ·
    refine ⟨176061007428533134146162863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117374004952355422764108575 176061007428533134146162863)
    ·
      refine ⟨264091511142799701219244295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176061007428533134146162863 264091511142799701219244295)
      ·
        refine ⟨396137266714199551828866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264091511142799701219244295 396137266714199551828866443)
        ·
          refine ⟨594205900071299327743299665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396137266714199551828866443 594205900071299327743299665)
          ·
            refine ⟨445654425053474495807474749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594205900071299327743299665 445654425053474495807474749)
            ·
              refine ⟨167120409395052935927803031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445654425053474495807474749 167120409395052935927803031)
              ·
                refine ⟨250680614092579403891704547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167120409395052935927803031 250680614092579403891704547)
                ·
                  refine ⟨376020921138869105837556821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250680614092579403891704547 376020921138869105837556821)
                  ·
                    refine ⟨4406495169596122334033869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 376020921138869105837556821 4406495169596122334033869)
                    ·
                      refine ⟨1652435688598545875262701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406495169596122334033869 1652435688598545875262701)
                      ·
                        rfl

theorem cell23_3218107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].length) (baseStart_3218107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218107 prefixEnd_3218107 := by exact prefixLift 3218107
  have htrace : WordTrace (prefixWord ++ tailWord_3218107) baseStart_3218107 baseEnd_3218107 := by
    simpa [prefixWord, tailWord_3218107, baseEnd_3218107] using wordTrace_append hprefix tailTrace_3218107
  have hstable : (prefixWord ++ tailWord_3218107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218107).length < 2 ^ (prefixWord ++ tailWord_3218107).sum := by decide
  have hdescent : baseEnd_3218107 < baseStart_3218107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218154 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3218154 : Nat := 118140960795 + 3218154 * 2 ^ 59
def prefixEnd_3218154 : Nat := 4983230072969 + 3 ^ 40 * 3218154 * 2
def baseEnd_3218154 : Nat := 1652459822189307191374985

theorem tailTrace_3218154 : CollatzResearch.WordTrace tailWord_3218154 prefixEnd_3218154 1652459822189307191374985 := by
  unfold tailWord_3218154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343929795796287447767379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78250479455456766527379677 29343929795796287447767379)
  ·
    refine ⟨44015894693694431171651069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29343929795796287447767379 44015894693694431171651069)
    ·
      refine ⟨16505960510135411689369151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44015894693694431171651069 16505960510135411689369151)
      ·
        refine ⟨24758940765203117534053727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16505960510135411689369151 24758940765203117534053727)
        ·
          refine ⟨37138411147804676301080591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24758940765203117534053727 37138411147804676301080591)
          ·
            refine ⟨55707616721707014451620887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37138411147804676301080591 55707616721707014451620887)
            ·
              refine ⟨83561425082560521677431331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55707616721707014451620887 83561425082560521677431331)
              ·
                refine ⟨125342137623840782516146997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83561425082560521677431331 125342137623840782516146997)
                ·
                  refine ⟨11750825402235073360888781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125342137623840782516146997 11750825402235073360888781)
                  ·
                    refine ⟨4406559525838152510333293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11750825402235073360888781 4406559525838152510333293)
                    ·
                      refine ⟨1652459822189307191374985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406559525838152510333293 1652459822189307191374985)
                      ·
                        rfl

theorem cell23_3218154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3218154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218154 prefixEnd_3218154 := by exact prefixLift 3218154
  have htrace : WordTrace (prefixWord ++ tailWord_3218154) baseStart_3218154 baseEnd_3218154 := by
    simpa [prefixWord, tailWord_3218154, baseEnd_3218154] using wordTrace_append hprefix tailTrace_3218154
  have hstable : (prefixWord ++ tailWord_3218154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218154).length < 2 ^ (prefixWord ++ tailWord_3218154).sum := by decide
  have hdescent : baseEnd_3218154 < baseStart_3218154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218165 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3218165 : Nat := 118140960795 + 3218165 * 2 ^ 59
def prefixEnd_3218165 : Nat := 4983230072969 + 3 ^ 40 * 3218165 * 2
def baseEnd_3218165 : Nat := 550821823492168882779145

theorem tailTrace_3218165 : CollatzResearch.WordTrace tailWord_3218165 prefixEnd_3218165 550821823492168882779145 := by
  unfold tailWord_3218165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117376120386145298669719949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78250746924096865779813299 117376120386145298669719949)
  ·
    refine ⟨44016045144804487001144981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117376120386145298669719949 44016045144804487001144981)
    ·
      refine ⟨2063252116162710328178671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44016045144804487001144981 2063252116162710328178671)
      ·
        refine ⟨3094878174244065492268007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063252116162710328178671 3094878174244065492268007)
        ·
          refine ⟨4642317261366098238402011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094878174244065492268007 4642317261366098238402011)
          ·
            refine ⟨6963475892049147357603017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642317261366098238402011 6963475892049147357603017)
            ·
              refine ⟨5222606919036860518202263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6963475892049147357603017 5222606919036860518202263)
              ·
                refine ⟨7833910378555290777303395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222606919036860518202263 7833910378555290777303395)
                ·
                  refine ⟨11750865567832936165955093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833910378555290777303395 11750865567832936165955093)
                  ·
                    refine ⟨550821823492168882779145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11750865567832936165955093 550821823492168882779145)
                    ·
                      rfl

theorem cell23_3218165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3218165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218165 prefixEnd_3218165 := by exact prefixLift 3218165
  have htrace : WordTrace (prefixWord ++ tailWord_3218165) baseStart_3218165 baseEnd_3218165 := by
    simpa [prefixWord, tailWord_3218165, baseEnd_3218165] using wordTrace_append hprefix tailTrace_3218165
  have hstable : (prefixWord ++ tailWord_3218165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218165).length < 2 ^ (prefixWord ++ tailWord_3218165).sum := by decide
  have hdescent : baseEnd_3218165 < baseStart_3218165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218167 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3218167 : Nat := 118140960795 + 3218167 * 2 ^ 59
def prefixEnd_3218167 : Nat := 4983230072969 + 3 ^ 40 * 3218167 * 2
def baseEnd_3218167 : Nat := 1652466497437815640512425

theorem tailTrace_3218167 : CollatzResearch.WordTrace tailWord_3218167 prefixEnd_3218167 1652466497437815640512425 := by
  unfold tailWord_3218167
  simp only [CollatzResearch.WordTrace]
  refine ⟨117376193332138053011292755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78250795554758702007528503 117376193332138053011292755)
  ·
    refine ⟨176064289998207079516939133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117376193332138053011292755 176064289998207079516939133)
    ·
      refine ⟨66024108749327654818852175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176064289998207079516939133 66024108749327654818852175)
      ·
        refine ⟨99036163123991482228278263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66024108749327654818852175 99036163123991482228278263)
        ·
          refine ⟨148554244685987223342417395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99036163123991482228278263 148554244685987223342417395)
          ·
            refine ⟨222831367028980835013626093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148554244685987223342417395 222831367028980835013626093)
            ·
              refine ⟨83561762635867813130109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222831367028980835013626093 83561762635867813130109785)
              ·
                refine ⟨62671321976900859847582339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83561762635867813130109785 62671321976900859847582339)
                ·
                  refine ⟨94006982965351289771373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62671321976900859847582339 94006982965351289771373509)
                  ·
                    refine ⟨17626309306003366832132533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94006982965351289771373509 17626309306003366832132533)
                    ·
                      refine ⟨1652466497437815640512425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17626309306003366832132533 1652466497437815640512425)
                      ·
                        rfl

theorem cell23_3218167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3218167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218167 prefixEnd_3218167 := by exact prefixLift 3218167
  have htrace : WordTrace (prefixWord ++ tailWord_3218167) baseStart_3218167 baseEnd_3218167 := by
    simpa [prefixWord, tailWord_3218167, baseEnd_3218167] using wordTrace_append hprefix tailTrace_3218167
  have hstable : (prefixWord ++ tailWord_3218167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218167).length < 2 ^ (prefixWord ++ tailWord_3218167).sum := by decide
  have hdescent : baseEnd_3218167 < baseStart_3218167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218187 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 8]
def baseStart_3218187 : Nat := 118140960795 + 3218187 * 2 ^ 59
def prefixEnd_3218187 : Nat := 4983230072969 + 3 ^ 40 * 3218187 * 2
def baseEnd_3218187 : Nat := 550825589016968520754111

theorem tailTrace_3218187 : CollatzResearch.WordTrace tailWord_3218187 prefixEnd_3218187 550825589016968520754111 := by
  unfold tailWord_3218187
  simp only [CollatzResearch.WordTrace]
  refine ⟨117376922792065596427020815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78251281861377064284680543 117376922792065596427020815)
  ·
    refine ⟨176065384188098394640531223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117376922792065596427020815 176065384188098394640531223)
    ·
      refine ⟨264098076282147591960796835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176065384188098394640531223 264098076282147591960796835)
      ·
        refine ⟨396147114423221387941195253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264098076282147591960796835 396147114423221387941195253)
        ·
          refine ⟨37138791977177005119487055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 396147114423221387941195253 37138791977177005119487055)
          ·
            refine ⟨55708187965765507679230583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37138791977177005119487055 55708187965765507679230583)
            ·
              refine ⟨83562281948648261518845875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55708187965765507679230583 83562281948648261518845875)
              ·
                refine ⟨125343422922972392278268813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83562281948648261518845875 125343422922972392278268813)
                ·
                  refine ⟨47003783596114647104350805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125343422922972392278268813 47003783596114647104350805)
                  ·
                    refine ⟨550825589016968520754111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47003783596114647104350805 550825589016968520754111)
                    ·
                      rfl

theorem cell23_3218187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_3218187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218187 prefixEnd_3218187 := by exact prefixLift 3218187
  have htrace : WordTrace (prefixWord ++ tailWord_3218187) baseStart_3218187 baseEnd_3218187 := by
    simpa [prefixWord, tailWord_3218187, baseEnd_3218187] using wordTrace_append hprefix tailTrace_3218187
  have hstable : (prefixWord ++ tailWord_3218187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218187).length < 2 ^ (prefixWord ++ tailWord_3218187).sum := by decide
  have hdescent : baseEnd_3218187 < baseStart_3218187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218204 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3218204 : Nat := 118140960795 + 3218204 * 2 ^ 59
def prefixEnd_3218204 : Nat := 4983230072969 + 3 ^ 40 * 3218204 * 2
def baseEnd_3218204 : Nat := 550828498740677331916585

theorem tailTrace_3218204 : CollatzResearch.WordTrace tailWord_3218204 prefixEnd_3218204 550828498740677331916585 := by
  unfold tailWord_3218204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58688771416502004165194833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78251695222002672220259777 58688771416502004165194833)
  ·
    refine ⟨44016578562376503123896125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58688771416502004165194833 44016578562376503123896125)
    ·
      refine ⟨16506216960891188671461047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44016578562376503123896125 16506216960891188671461047)
      ·
        refine ⟨24759325441336783007191571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16506216960891188671461047 24759325441336783007191571)
        ·
          refine ⟨37138988162005174510787357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24759325441336783007191571 37138988162005174510787357)
          ·
            refine ⟨13927120560751940441545259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37138988162005174510787357 13927120560751940441545259)
            ·
              refine ⟨20890680841127910662317889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13927120560751940441545259 20890680841127910662317889)
              ·
                refine ⟨15668010630845932996738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20890680841127910662317889 15668010630845932996738417)
                ·
                  refine ⟨11751007973134449747553813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15668010630845932996738417 11751007973134449747553813)
                  ·
                    refine ⟨550828498740677331916585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11751007973134449747553813 550828498740677331916585)
                    ·
                      rfl

theorem cell23_3218204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3218204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218204 prefixEnd_3218204 := by exact prefixLift 3218204
  have htrace : WordTrace (prefixWord ++ tailWord_3218204) baseStart_3218204 baseEnd_3218204 := by
    simpa [prefixWord, tailWord_3218204, baseEnd_3218204] using wordTrace_append hprefix tailTrace_3218204
  have hstable : (prefixWord ++ tailWord_3218204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218204).length < 2 ^ (prefixWord ++ tailWord_3218204).sum := by decide
  have hdescent : baseEnd_3218204 < baseStart_3218204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218205 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3218205 : Nat := 118140960795 + 3218205 * 2 ^ 59
def prefixEnd_3218205 : Nat := 4983230072969 + 3 ^ 40 * 3218205 * 2
def baseEnd_3218205 : Nat := 1652486009702686491837251

theorem tailTrace_3218205 : CollatzResearch.WordTrace tailWord_3218205 prefixEnd_3218205 1652486009702686491837251 := by
  unfold tailWord_3218205
  simp only [CollatzResearch.WordTrace]
  refine ⟨117377579306000385501176069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78251719537333590334117379 117377579306000385501176069)
  ·
    refine ⟨22008296119875072281470513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117377579306000385501176069 22008296119875072281470513)
    ·
      refine ⟨16506222089906304211102885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22008296119875072281470513 16506222089906304211102885)
      ·
        refine ⟨3094916641857432039581791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16506222089906304211102885 3094916641857432039581791)
        ·
          refine ⟨4642374962786148059372687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094916641857432039581791 4642374962786148059372687)
          ·
            refine ⟨6963562444179222089059031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642374962786148059372687 6963562444179222089059031)
            ·
              refine ⟨10445343666268833133588547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963562444179222089059031 10445343666268833133588547)
              ·
                refine ⟨15668015499403249700382821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10445343666268833133588547 15668015499403249700382821)
                ·
                  refine ⟨2937752906138109318821779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15668015499403249700382821 2937752906138109318821779)
                  ·
                    refine ⟨4406629359207163978232669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937752906138109318821779 4406629359207163978232669)
                    ·
                      refine ⟨1652486009702686491837251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406629359207163978232669 1652486009702686491837251)
                      ·
                        rfl

theorem cell23_3218205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3218205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218205 prefixEnd_3218205 := by exact prefixLift 3218205
  have htrace : WordTrace (prefixWord ++ tailWord_3218205) baseStart_3218205 baseEnd_3218205 := by
    simpa [prefixWord, tailWord_3218205, baseEnd_3218205] using wordTrace_append hprefix tailTrace_3218205
  have hstable : (prefixWord ++ tailWord_3218205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218205).length < 2 ^ (prefixWord ++ tailWord_3218205).sum := by decide
  have hdescent : baseEnd_3218205 < baseStart_3218205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218217 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 11]
def baseStart_3218217 : Nat := 118140960795 + 3218217 * 2 ^ 59
def prefixEnd_3218217 : Nat := 4983230072969 + 3 ^ 40 * 3218217 * 2
def baseEnd_3218217 : Nat := 183610241274504493876355

theorem tailTrace_3218217 : CollatzResearch.WordTrace tailWord_3218217 prefixEnd_3218217 183610241274504493876355 := by
  unfold tailWord_3218217
  simp only [CollatzResearch.WordTrace]
  refine ⟨117378016981956911550612905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78252011321304607700408603 117378016981956911550612905)
  ·
    refine ⟨88033512736467683662959679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117378016981956911550612905 88033512736467683662959679)
    ·
      refine ⟨132050269104701525494439519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88033512736467683662959679 132050269104701525494439519)
      ·
        refine ⟨198075403657052288241659279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132050269104701525494439519 198075403657052288241659279)
        ·
          refine ⟨297113105485578432362488919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198075403657052288241659279 297113105485578432362488919)
          ·
            refine ⟨445669658228367648543733379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297113105485578432362488919 445669658228367648543733379)
            ·
              refine ⟨668504487342551472815600069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445669658228367648543733379 668504487342551472815600069)
              ·
                refine ⟨125344591376728401152925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668504487342551472815600069 125344591376728401152925013)
                ·
                  refine ⟨183610241274504493876355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 125344591376728401152925013 183610241274504493876355)
                  ·
                    rfl

theorem cell23_3218217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_3218217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218217 prefixEnd_3218217 := by exact prefixLift 3218217
  have htrace : WordTrace (prefixWord ++ tailWord_3218217) baseStart_3218217 baseEnd_3218217 := by
    simpa [prefixWord, tailWord_3218217, baseEnd_3218217] using wordTrace_append hprefix tailTrace_3218217
  have hstable : (prefixWord ++ tailWord_3218217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218217).length < 2 ^ (prefixWord ++ tailWord_3218217).sum := by decide
  have hdescent : baseEnd_3218217 < baseStart_3218217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218222 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3218222 : Nat := 118140960795 + 3218222 * 2 ^ 59
def prefixEnd_3218222 : Nat := 4983230072969 + 3 ^ 40 * 3218222 * 2
def baseEnd_3218222 : Nat := 1652494738873812925324673

theorem tailTrace_3218222 : CollatzResearch.WordTrace tailWord_3218222 prefixEnd_3218222 1652494738873812925324673 := by
  unfold tailWord_3218222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672274918367349675568115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78252132897959198269696613 14672274918367349675568115)
  ·
    refine ⟨22008412377551024513352173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14672274918367349675568115 22008412377551024513352173)
    ·
      refine ⟨8253154641581634192507065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22008412377551024513352173 8253154641581634192507065)
      ·
        refine ⟨6189865981186225644380299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253154641581634192507065 6189865981186225644380299)
        ·
          refine ⟨9284798971779338466570449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189865981186225644380299 9284798971779338466570449)
          ·
            refine ⟨6963599228834503849927837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9284798971779338466570449 6963599228834503849927837)
            ·
              refine ⟨2611349710812938943722939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6963599228834503849927837 2611349710812938943722939)
              ·
                refine ⟨3917024566219408415584409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611349710812938943722939 3917024566219408415584409)
                ·
                  refine ⟨2937768424664556311688307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917024566219408415584409 2937768424664556311688307)
                  ·
                    refine ⟨4406652636996834467532461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937768424664556311688307 4406652636996834467532461)
                    ·
                      refine ⟨1652494738873812925324673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406652636996834467532461 1652494738873812925324673)
                      ·
                        rfl

theorem cell23_3218222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3218222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218222 prefixEnd_3218222 := by exact prefixLift 3218222
  have htrace : WordTrace (prefixWord ++ tailWord_3218222) baseStart_3218222 baseEnd_3218222 := by
    simpa [prefixWord, tailWord_3218222, baseEnd_3218222] using wordTrace_append hprefix tailTrace_3218222
  have hstable : (prefixWord ++ tailWord_3218222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218222).length < 2 ^ (prefixWord ++ tailWord_3218222).sum := by decide
  have hdescent : baseEnd_3218222 < baseStart_3218222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218268 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 7]
def baseStart_3218268 : Nat := 118140960795 + 3218268 * 2 ^ 59
def prefixEnd_3218268 : Nat := 4983230072969 + 3 ^ 40 * 3218268 * 2
def baseEnd_3218268 : Nat := 183613150998213305038829

theorem tailTrace_3218268 : CollatzResearch.WordTrace tailWord_3218268 prefixEnd_3218268 183613150998213305038829 := by
  unfold tailWord_3218268
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689938552386073630359729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78253251403181431507146305 58689938552386073630359729)
  ·
    refine ⟨44017453914289555222769797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58689938552386073630359729 44017453914289555222769797)
    ·
      refine ⟨8253272608929291604269337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44017453914289555222769797 8253272608929291604269337)
      ·
        refine ⟨6189954456696968703202003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253272608929291604269337 6189954456696968703202003)
        ·
          refine ⟨9284931685045453054803005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189954456696968703202003 9284931685045453054803005)
          ·
            refine ⟨3481849381892044895551127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9284931685045453054803005 3481849381892044895551127)
            ·
              refine ⟨5222774072838067343326691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481849381892044895551127 5222774072838067343326691)
              ·
                refine ⟨7834161109257101014990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222774072838067343326691 7834161109257101014990037)
                ·
                  refine ⟨183613150998213305038829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7834161109257101014990037 183613150998213305038829)
                  ·
                    rfl

theorem cell23_3218268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_3218268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218268 prefixEnd_3218268 := by exact prefixLift 3218268
  have htrace : WordTrace (prefixWord ++ tailWord_3218268) baseStart_3218268 baseEnd_3218268 := by
    simpa [prefixWord, tailWord_3218268, baseEnd_3218268] using wordTrace_append hprefix tailTrace_3218268
  have hstable : (prefixWord ++ tailWord_3218268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218268).length < 2 ^ (prefixWord ++ tailWord_3218268).sum := by decide
  have hdescent : baseEnd_3218268 < baseStart_3218268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218271 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 5, 2]
def baseStart_3218271 : Nat := 118140960795 + 3218271 * 2 ^ 59
def prefixEnd_3218271 : Nat := 4983230072969 + 3 ^ 40 * 3218271 * 2
def baseEnd_3218271 : Nat := 1652519899425883233611947

theorem tailTrace_3218271 : CollatzResearch.WordTrace tailWord_3218271 prefixEnd_3218271 1652519899425883233611947 := by
  unfold tailWord_3218271
  simp only [CollatzResearch.WordTrace]
  refine ⟨117379986523761278773078667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78253324349174185848719111 117379986523761278773078667)
  ·
    refine ⟨176069979785641918159618001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117379986523761278773078667 176069979785641918159618001)
    ·
      refine ⟨132052484839231438619713501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176069979785641918159618001 132052484839231438619713501)
      ·
        refine ⟨49519681814711789482392563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132052484839231438619713501 49519681814711789482392563)
        ·
          refine ⟨74279522722067684223588845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49519681814711789482392563 74279522722067684223588845)
          ·
            refine ⟨27854821020775381583845817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74279522722067684223588845 27854821020775381583845817)
            ·
              refine ⟨20891115765581536187884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27854821020775381583845817 20891115765581536187884363)
              ·
                refine ⟨31336673648372304281826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20891115765581536187884363 31336673648372304281826545)
                ·
                  refine ⟨23502505236279228211369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31336673648372304281826545 23502505236279228211369909)
                  ·
                    refine ⟨2203359865901177644815929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23502505236279228211369909 2203359865901177644815929)
                    ·
                      refine ⟨1652519899425883233611947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203359865901177644815929 1652519899425883233611947)
                      ·
                        rfl

theorem cell23_3218271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_3218271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218271 prefixEnd_3218271 := by exact prefixLift 3218271
  have htrace : WordTrace (prefixWord ++ tailWord_3218271) baseStart_3218271 baseEnd_3218271 := by
    simpa [prefixWord, tailWord_3218271, baseEnd_3218271] using wordTrace_append hprefix tailTrace_3218271
  have hstable : (prefixWord ++ tailWord_3218271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218271).length < 2 ^ (prefixWord ++ tailWord_3218271).sum := by decide
  have hdescent : baseEnd_3218271 < baseStart_3218271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218301 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_3218301 : Nat := 118140960795 + 3218301 * 2 ^ 59
def prefixEnd_3218301 : Nat := 4983230072969 + 3 ^ 40 * 3218301 * 2
def baseEnd_3218301 : Nat := 1652535303845518116236809

theorem tailTrace_3218301 : CollatzResearch.WordTrace tailWord_3218301 prefixEnd_3218301 1652535303845518116236809 := by
  unfold tailWord_3218301
  simp only [CollatzResearch.WordTrace]
  refine ⟨117381080713652593896670757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78254053809101729264447171 117381080713652593896670757)
  ·
    refine ⟨22008952633809861355625767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117381080713652593896670757 22008952633809861355625767)
    ·
      refine ⟨33013428950714792033438651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22008952633809861355625767 33013428950714792033438651)
      ·
        refine ⟨49520143426072188050157977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33013428950714792033438651 49520143426072188050157977)
        ·
          refine ⟨37140107569554141037618483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49520143426072188050157977 37140107569554141037618483)
          ·
            refine ⟨55710161354331211556427725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37140107569554141037618483 55710161354331211556427725)
            ·
              refine ⟨20891310507874204333660397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55710161354331211556427725 20891310507874204333660397)
              ·
                refine ⟨7834241440452826625122649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20891310507874204333660397 7834241440452826625122649)
                ·
                  refine ⟨5875681080339619968841987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7834241440452826625122649 5875681080339619968841987)
                  ·
                    refine ⟨8813521620509429953262981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875681080339619968841987 8813521620509429953262981)
                    ·
                      refine ⟨1652535303845518116236809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8813521620509429953262981 1652535303845518116236809)
                      ·
                        rfl

theorem cell23_3218301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_3218301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218301 prefixEnd_3218301 := by exact prefixLift 3218301
  have htrace : WordTrace (prefixWord ++ tailWord_3218301) baseStart_3218301 baseEnd_3218301 := by
    simpa [prefixWord, tailWord_3218301, baseEnd_3218301] using wordTrace_append hprefix tailTrace_3218301
  have hstable : (prefixWord ++ tailWord_3218301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218301).length < 2 ^ (prefixWord ++ tailWord_3218301).sum := by decide
  have hdescent : baseEnd_3218301 < baseStart_3218301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218371 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 1, 5]
def baseStart_3218371 : Nat := 118140960795 + 3218371 * 2 ^ 59
def prefixEnd_3218371 : Nat := 4983230072969 + 3 ^ 40 * 3218371 * 2
def baseEnd_3218371 : Nat := 550857082497110947453829

theorem tailTrace_3218371 : CollatzResearch.WordTrace tailWord_3218371 prefixEnd_3218371 550857082497110947453829 := by
  unfold tailWord_3218371
  simp only [CollatzResearch.WordTrace]
  refine ⟨117383633823398995851718967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78255755882265997234479311 117383633823398995851718967)
  ·
    refine ⟨176075450735098493777578451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117383633823398995851718967 176075450735098493777578451)
    ·
      refine ⟨264113176102647740666367677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176075450735098493777578451 264113176102647740666367677)
      ·
        refine ⟨99042441038492902749887879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264113176102647740666367677 99042441038492902749887879)
        ·
          refine ⟨148563661557739354124831819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99042441038492902749887879 148563661557739354124831819)
          ·
            refine ⟨222845492336609031187247729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148563661557739354124831819 222845492336609031187247729)
            ·
              refine ⟨167134119252456773390435797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222845492336609031187247729 167134119252456773390435797)
              ·
                refine ⟨3917205919979455626338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167134119252456773390435797 3917205919979455626338339)
                ·
                  refine ⟨5875808879969183439507509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917205919979455626338339 5875808879969183439507509)
                  ·
                    refine ⟨550857082497110947453829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5875808879969183439507509 550857082497110947453829)
                    ·
                      rfl

theorem cell23_3218371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 5].length) (baseStart_3218371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218371 prefixEnd_3218371 := by exact prefixLift 3218371
  have htrace : WordTrace (prefixWord ++ tailWord_3218371) baseStart_3218371 baseEnd_3218371 := by
    simpa [prefixWord, tailWord_3218371, baseEnd_3218371] using wordTrace_append hprefix tailTrace_3218371
  have hstable : (prefixWord ++ tailWord_3218371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218371).length < 2 ^ (prefixWord ++ tailWord_3218371).sum := by decide
  have hdescent : baseEnd_3218371 < baseStart_3218371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218378 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_3218378 : Nat := 118140960795 + 3218378 * 2 ^ 59
def prefixEnd_3218378 : Nat := 4983230072969 + 3 ^ 40 * 3218378 * 2
def baseEnd_3218378 : Nat := 1652574841855914314973955

theorem tailTrace_3218378 : CollatzResearch.WordTrace tailWord_3218378 prefixEnd_3218378 1652574841855914314973955 := by
  unfold tailWord_3218378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345972283593409011805947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78255926089582424031482525 29345972283593409011805947)
  ·
    refine ⟨44018958425390113517708921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29345972283593409011805947 44018958425390113517708921)
    ·
      refine ⟨33014218819042585138281691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44018958425390113517708921 33014218819042585138281691)
      ·
        refine ⟨49521328228563877707422537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33014218819042585138281691 49521328228563877707422537)
        ·
          refine ⟨37140996171422908280566903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49521328228563877707422537 37140996171422908280566903)
          ·
            refine ⟨55711494257134362420850355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37140996171422908280566903 55711494257134362420850355)
            ·
              refine ⟨83567241385701543631275533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55711494257134362420850355 83567241385701543631275533)
              ·
                refine ⟨31337715519638078861728325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83567241385701543631275533 31337715519638078861728325)
                ·
                  refine ⟨5875821659932139786574061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31337715519638078861728325 5875821659932139786574061)
                  ·
                    refine ⟨2203433122474552419965273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5875821659932139786574061 2203433122474552419965273)
                    ·
                      refine ⟨1652574841855914314973955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203433122474552419965273 1652574841855914314973955)
                      ·
                        rfl

theorem cell23_3218378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_3218378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218378 prefixEnd_3218378 := by exact prefixLift 3218378
  have htrace : WordTrace (prefixWord ++ tailWord_3218378) baseStart_3218378 baseEnd_3218378 := by
    simpa [prefixWord, tailWord_3218378, baseEnd_3218378] using wordTrace_append hprefix tailTrace_3218378
  have hstable : (prefixWord ++ tailWord_3218378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218378).length < 2 ^ (prefixWord ++ tailWord_3218378).sum := by decide
  have hdescent : baseEnd_3218378 < baseStart_3218378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218385 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_3218385 : Nat := 118140960795 + 3218385 * 2 ^ 59
def prefixEnd_3218385 : Nat := 4983230072969 + 3 ^ 40 * 3218385 * 2
def baseEnd_3218385 : Nat := 1652578436220495787586423

theorem tailTrace_3218385 : CollatzResearch.WordTrace tailWord_3218385 prefixEnd_3218385 1652578436220495787586423 := by
  unfold tailWord_3218385
  simp only [CollatzResearch.WordTrace]
  refine ⟨117384144445348276242728609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78256096296898850828485739 117384144445348276242728609)
  ·
    refine ⟨88038108334011207182046457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117384144445348276242728609 88038108334011207182046457)
    ·
      refine ⟨66028581250508405386534843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88038108334011207182046457 66028581250508405386534843)
      ·
        refine ⟨99042871875762608079802265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66028581250508405386534843 99042871875762608079802265)
        ·
          refine ⟨74282153906821956059851699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99042871875762608079802265 74282153906821956059851699)
          ·
            refine ⟨111423230860232934089777549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74282153906821956059851699 111423230860232934089777549)
            ·
              refine ⟨41783711572587350283666581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111423230860232934089777549 41783711572587350283666581)
              ·
                refine ⟨1958611479965032044546871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41783711572587350283666581 1958611479965032044546871)
                ·
                  refine ⟨2937917219947548066820307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958611479965032044546871 2937917219947548066820307)
                  ·
                    refine ⟨4406875829921322100230461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937917219947548066820307 4406875829921322100230461)
                    ·
                      refine ⟨1652578436220495787586423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406875829921322100230461 1652578436220495787586423)
                      ·
                        rfl

theorem cell23_3218385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_3218385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218385 prefixEnd_3218385 := by exact prefixLift 3218385
  have htrace : WordTrace (prefixWord ++ tailWord_3218385) baseStart_3218385 baseEnd_3218385 := by
    simpa [prefixWord, tailWord_3218385, baseEnd_3218385] using wordTrace_append hprefix tailTrace_3218385
  have hstable : (prefixWord ++ tailWord_3218385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218385).length < 2 ^ (prefixWord ++ tailWord_3218385).sum := by decide
  have hdescent : baseEnd_3218385 < baseStart_3218385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218391 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3218391 : Nat := 118140960795 + 3218391 * 2 ^ 59
def prefixEnd_3218391 : Nat := 4983230072969 + 3 ^ 40 * 3218391 * 2
def baseEnd_3218391 : Nat := 1652581517104422764111395

theorem tailTrace_3218391 : CollatzResearch.WordTrace tailWord_3218391 prefixEnd_3218391 1652581517104422764111395 := by
  unfold tailWord_3218391
  simp only [CollatzResearch.WordTrace]
  refine ⟨117384363283326539267447027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78256242188884359511631351 117384363283326539267447027)
  ·
    refine ⟨176076544924989808901170541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117384363283326539267447027 176076544924989808901170541)
    ·
      refine ⟨66028704346871178337938953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176076544924989808901170541 66028704346871178337938953)
      ·
        refine ⟨49521528260153383753454215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66028704346871178337938953 49521528260153383753454215)
        ·
          refine ⟨74282292390230075630181323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49521528260153383753454215 74282292390230075630181323)
          ·
            refine ⟨111423438585345113445271985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74282292390230075630181323 111423438585345113445271985)
            ·
              refine ⟨83567578939008835083953989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111423438585345113445271985 83567578939008835083953989)
              ·
                refine ⟨15668921051064156578241373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83567578939008835083953989 15668921051064156578241373)
                ·
                  refine ⟨5875845394149058716840515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15668921051064156578241373 5875845394149058716840515)
                  ·
                    refine ⟨8813768091223588075260773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875845394149058716840515 8813768091223588075260773)
                    ·
                      refine ⟨1652581517104422764111395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8813768091223588075260773 1652581517104422764111395)
                      ·
                        rfl

theorem cell23_3218391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3218391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218391 prefixEnd_3218391 := by exact prefixLift 3218391
  have htrace : WordTrace (prefixWord ++ tailWord_3218391) baseStart_3218391 baseEnd_3218391 := by
    simpa [prefixWord, tailWord_3218391, baseEnd_3218391] using wordTrace_append hprefix tailTrace_3218391
  have hstable : (prefixWord ++ tailWord_3218391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218391).length < 2 ^ (prefixWord ++ tailWord_3218391).sum := by decide
  have hdescent : baseEnd_3218391 < baseStart_3218391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218402 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3218402 : Nat := 118140960795 + 3218402 * 2 ^ 59
def prefixEnd_3218402 : Nat := 4983230072969 + 3 ^ 40 * 3218402 * 2
def baseEnd_3218402 : Nat := 1652587165391622221073845

theorem tailTrace_3218402 : CollatzResearch.WordTrace tailWord_3218402 prefixEnd_3218402 1652587165391622221073845 := by
  unfold tailWord_3218402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346191121571672036524365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78256509657524458764064973 29346191121571672036524365)
  ·
    refine ⟨11004821670589377013696637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29346191121571672036524365 11004821670589377013696637)
    ·
      refine ⟨4126808126471016380136239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11004821670589377013696637 4126808126471016380136239)
      ·
        refine ⟨6190212189706524570204359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126808126471016380136239 6190212189706524570204359)
        ·
          refine ⟨9285318284559786855306539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190212189706524570204359 9285318284559786855306539)
          ·
            refine ⟨13927977426839680282959809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285318284559786855306539 13927977426839680282959809)
            ·
              refine ⟨10445983070129760212219857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13927977426839680282959809 10445983070129760212219857)
              ·
                refine ⟨7834487302597320159164893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445983070129760212219857 7834487302597320159164893)
                ·
                  refine ⟨2937932738473995059686835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7834487302597320159164893 2937932738473995059686835)
                  ·
                    refine ⟨4406899107710992589530253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937932738473995059686835 4406899107710992589530253)
                    ·
                      refine ⟨1652587165391622221073845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406899107710992589530253 1652587165391622221073845)
                      ·
                        rfl

theorem cell23_3218402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3218402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218402 prefixEnd_3218402 := by exact prefixLift 3218402
  have htrace : WordTrace (prefixWord ++ tailWord_3218402) baseStart_3218402 baseEnd_3218402 := by
    simpa [prefixWord, tailWord_3218402, baseEnd_3218402] using wordTrace_append hprefix tailTrace_3218402
  have hstable : (prefixWord ++ tailWord_3218402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218402).length < 2 ^ (prefixWord ++ tailWord_3218402).sum := by decide
  have hdescent : baseEnd_3218402 < baseStart_3218402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218408 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3218408 : Nat := 118140960795 + 3218408 * 2 ^ 59
def prefixEnd_3218408 : Nat := 4983230072969 + 3 ^ 40 * 3218408 * 2
def baseEnd_3218408 : Nat := 1652590246275549197598817

theorem tailTrace_3218408 : CollatzResearch.WordTrace tailWord_3218408 prefixEnd_3218408 1652590246275549197598817 := by
  unfold tailWord_3218408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58692491662132475585407939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78256655549509967447210585 58692491662132475585407939)
  ·
    refine ⟨88038737493198713378111909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58692491662132475585407939 88038737493198713378111909)
    ·
      refine ⟨16507263279974758758395983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88038737493198713378111909 16507263279974758758395983)
      ·
        refine ⟨24760894919962138137593975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16507263279974758758395983 24760894919962138137593975)
        ·
          refine ⟨37141342379943207206390963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24760894919962138137593975 37141342379943207206390963)
          ·
            refine ⟨55712013569914810809586445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37141342379943207206390963 55712013569914810809586445)
            ·
              refine ⟨20892005088718054053594917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55712013569914810809586445 20892005088718054053594917)
              ·
                refine ⟨3917250954134635135049047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20892005088718054053594917 3917250954134635135049047)
                ·
                  refine ⟨5875876431201952702573571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917250954134635135049047 5875876431201952702573571)
                  ·
                    refine ⟨8813814646802929053860357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875876431201952702573571 8813814646802929053860357)
                    ·
                      refine ⟨1652590246275549197598817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8813814646802929053860357 1652590246275549197598817)
                      ·
                        rfl

theorem cell23_3218408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3218408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218408 prefixEnd_3218408 := by exact prefixLift 3218408
  have htrace : WordTrace (prefixWord ++ tailWord_3218408) baseStart_3218408 baseEnd_3218408 := by
    simpa [prefixWord, tailWord_3218408, baseEnd_3218408] using wordTrace_append hprefix tailTrace_3218408
  have hstable : (prefixWord ++ tailWord_3218408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218408).length < 2 ^ (prefixWord ++ tailWord_3218408).sum := by decide
  have hdescent : baseEnd_3218408 < baseStart_3218408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218428 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3218428 : Nat := 118140960795 + 3218428 * 2 ^ 59
def prefixEnd_3218428 : Nat := 4983230072969 + 3 ^ 40 * 3218428 * 2
def baseEnd_3218428 : Nat := 1652600515888639119348725

theorem tailTrace_3218428 : CollatzResearch.WordTrace tailWord_3218428 prefixEnd_3218428 1652600515888639119348725 := by
  unfold tailWord_3218428
  simp only [CollatzResearch.WordTrace]
  refine ⟨58692856392096247293271969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78257141856128329724362625 58692856392096247293271969)
  ·
    refine ⟨44019642294072185469953977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58692856392096247293271969 44019642294072185469953977)
    ·
      refine ⟨33014731720554139102465483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44019642294072185469953977 33014731720554139102465483)
      ·
        refine ⟨49522097580831208653698225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33014731720554139102465483 49522097580831208653698225)
        ·
          refine ⟨37141573185623406490273669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49522097580831208653698225 37141573185623406490273669)
          ·
            refine ⟨6964044972304388716926313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37141573185623406490273669 6964044972304388716926313)
            ·
              refine ⟨5223033729228291537694735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964044972304388716926313 5223033729228291537694735)
              ·
                refine ⟨7834550593842437306542103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223033729228291537694735 7834550593842437306542103)
                ·
                  refine ⟨11751825890763655959813155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834550593842437306542103 11751825890763655959813155)
                  ·
                    refine ⟨17627738836145483939719733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11751825890763655959813155 17627738836145483939719733)
                    ·
                      refine ⟨1652600515888639119348725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17627738836145483939719733 1652600515888639119348725)
                      ·
                        rfl

theorem cell23_3218428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3218428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218428 prefixEnd_3218428 := by exact prefixLift 3218428
  have htrace : WordTrace (prefixWord ++ tailWord_3218428) baseStart_3218428 baseEnd_3218428 := by
    simpa [prefixWord, tailWord_3218428, baseEnd_3218428] using wordTrace_append hprefix tailTrace_3218428
  have hstable : (prefixWord ++ tailWord_3218428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218428).length < 2 ^ (prefixWord ++ tailWord_3218428).sum := by decide
  have hdescent : baseEnd_3218428 < baseStart_3218428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218442 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_3218442 : Nat := 118140960795 + 3218442 * 2 ^ 59
def prefixEnd_3218442 : Nat := 4983230072969 + 3 ^ 40 * 3218442 * 2
def baseEnd_3218442 : Nat := 1652607704617802064573661

theorem tailTrace_3218442 : CollatzResearch.WordTrace tailWord_3218442 prefixEnd_3218442 1652607704617802064573661 := by
  unfold tailWord_3218442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346555851535443744388395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78257482270761183318369053 29346555851535443744388395)
  ·
    refine ⟨44019833777303165616582593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29346555851535443744388395 44019833777303165616582593)
    ·
      refine ⟨33014875332977374212436945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44019833777303165616582593 33014875332977374212436945)
      ·
        refine ⟨24761156499733030659327709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33014875332977374212436945 24761156499733030659327709)
        ·
          refine ⟨9285433687399886497247891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24761156499733030659327709 9285433687399886497247891)
          ·
            refine ⟨13928150531099829745871837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285433687399886497247891 13928150531099829745871837)
            ·
              refine ⟨5223056449162436154701939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13928150531099829745871837 5223056449162436154701939)
              ·
                refine ⟨7834584673743654232052909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223056449162436154701939 7834584673743654232052909)
                ·
                  refine ⟨2937969252653870337019841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7834584673743654232052909 2937969252653870337019841)
                  ·
                    refine ⟨2203476939490402752764881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2937969252653870337019841 2203476939490402752764881)
                    ·
                      refine ⟨1652607704617802064573661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203476939490402752764881 1652607704617802064573661)
                      ·
                        rfl

theorem cell23_3218442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_3218442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218442 prefixEnd_3218442 := by exact prefixLift 3218442
  have htrace : WordTrace (prefixWord ++ tailWord_3218442) baseStart_3218442 baseEnd_3218442 := by
    simpa [prefixWord, tailWord_3218442, baseEnd_3218442] using wordTrace_append hprefix tailTrace_3218442
  have hstable : (prefixWord ++ tailWord_3218442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218442).length < 2 ^ (prefixWord ++ tailWord_3218442).sum := by decide
  have hdescent : baseEnd_3218442 < baseStart_3218442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218458 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3218458 : Nat := 118140960795 + 3218458 * 2 ^ 59
def prefixEnd_3218458 : Nat := 4983230072969 + 3 ^ 40 * 3218458 * 2
def baseEnd_3218458 : Nat := 1652615920308274001973587

theorem tailTrace_3218458 : CollatzResearch.WordTrace tailWord_3218458 prefixEnd_3218458 1652615920308274001973587 := by
  unfold tailWord_3218458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346701743520952427534007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78257871316055873140090685 29346701743520952427534007)
  ·
    refine ⟨44020052615281428641301011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29346701743520952427534007 44020052615281428641301011)
    ·
      refine ⟨66030078922922142961951517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44020052615281428641301011 66030078922922142961951517)
      ·
        refine ⟨24761279596095803610731819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66030078922922142961951517 24761279596095803610731819)
        ·
          refine ⟨37141919394143705416097729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24761279596095803610731819 37141919394143705416097729)
          ·
            refine ⟨27856439545607779062073297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37141919394143705416097729 27856439545607779062073297)
            ·
              refine ⟨20892329659205834296554973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27856439545607779062073297 20892329659205834296554973)
              ·
                refine ⟨7834623622202187861208115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20892329659205834296554973 7834623622202187861208115)
                ·
                  refine ⟨11751935433303281791812173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834623622202187861208115 11751935433303281791812173)
                  ·
                    refine ⟨4406975787488730671929565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11751935433303281791812173 4406975787488730671929565)
                    ·
                      refine ⟨1652615920308274001973587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4406975787488730671929565 1652615920308274001973587)
                      ·
                        rfl

theorem cell23_3218458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3218458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218458 prefixEnd_3218458 := by exact prefixLift 3218458
  have htrace : WordTrace (prefixWord ++ tailWord_3218458) baseStart_3218458 baseEnd_3218458 := by
    simpa [prefixWord, tailWord_3218458, baseEnd_3218458] using wordTrace_append hprefix tailTrace_3218458
  have hstable : (prefixWord ++ tailWord_3218458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218458).length < 2 ^ (prefixWord ++ tailWord_3218458).sum := by decide
  have hdescent : baseEnd_3218458 < baseStart_3218458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218492 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3218492 : Nat := 118140960795 + 3218492 * 2 ^ 59
def prefixEnd_3218492 : Nat := 4983230072969 + 3 ^ 40 * 3218492 * 2
def baseEnd_3218492 : Nat := 1652633378650526868948431

theorem tailTrace_3218492 : CollatzResearch.WordTrace tailWord_3218492 prefixEnd_3218492 1652633378650526868948431 := by
  unfold tailWord_3218492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58694023527980316758436865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78258698037307089011249153 58694023527980316758436865)
  ·
    refine ⟨44020517645985237568827649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58694023527980316758436865 44020517645985237568827649)
    ·
      refine ⟨33015388234488928176620737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44020517645985237568827649 33015388234488928176620737)
      ·
        refine ⟨24761541175866696132465553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33015388234488928176620737 24761541175866696132465553)
        ·
          refine ⟨18571155881900022099349165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24761541175866696132465553 18571155881900022099349165)
          ·
            refine ⟨6964183455712508287255937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18571155881900022099349165 6964183455712508287255937)
            ·
              refine ⟨5223137591784381215441953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964183455712508287255937 5223137591784381215441953)
              ·
                refine ⟨3917353193838285911581465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5223137591784381215441953 3917353193838285911581465)
                ·
                  refine ⟨2938014895378714433686099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917353193838285911581465 2938014895378714433686099)
                  ·
                    refine ⟨4407022343068071650529149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938014895378714433686099 4407022343068071650529149)
                    ·
                      refine ⟨1652633378650526868948431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407022343068071650529149 1652633378650526868948431)
                      ·
                        rfl

theorem cell23_3218492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3218492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218492 prefixEnd_3218492 := by exact prefixLift 3218492
  have htrace : WordTrace (prefixWord ++ tailWord_3218492) baseStart_3218492 baseEnd_3218492 := by
    simpa [prefixWord, tailWord_3218492, baseEnd_3218492] using wordTrace_append hprefix tailTrace_3218492
  have hstable : (prefixWord ++ tailWord_3218492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218492).length < 2 ^ (prefixWord ++ tailWord_3218492).sum := by decide
  have hdescent : baseEnd_3218492 < baseStart_3218492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218501 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_3218501 : Nat := 118140960795 + 3218501 * 2 ^ 59
def prefixEnd_3218501 : Nat := 4983230072969 + 3 ^ 40 * 3218501 * 2
def baseEnd_3218501 : Nat := 1652637999976417333735889

theorem tailTrace_3218501 : CollatzResearch.WordTrace tailWord_3218501 prefixEnd_3218501 1652637999976417333735889 := by
  unfold tailWord_3218501
  simp only [CollatzResearch.WordTrace]
  refine ⟨117388375312928028053951357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78258916875285352035967571 117388375312928028053951357)
  ·
    refine ⟨44020640742348010520231759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117388375312928028053951357 44020640742348010520231759)
    ·
      refine ⟨66030961113522015780347639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44020640742348010520231759 66030961113522015780347639)
      ·
        refine ⟨99046441670283023670521459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66030961113522015780347639 99046441670283023670521459)
        ·
          refine ⟨148569662505424535505782189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99046441670283023670521459 148569662505424535505782189)
          ·
            refine ⟨55713623439534200814668321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148569662505424535505782189 55713623439534200814668321)
            ·
              refine ⟨41785217579650650611001241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55713623439534200814668321 41785217579650650611001241)
              ·
                refine ⟨31338913184737987958250931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41785217579650650611001241 31338913184737987958250931)
                ·
                  refine ⟨47008369777106981937376397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31338913184737987958250931 47008369777106981937376397)
                  ·
                    refine ⟨17628138666415118226516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47008369777106981937376397 17628138666415118226516149)
                    ·
                      refine ⟨1652637999976417333735889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17628138666415118226516149 1652637999976417333735889)
                      ·
                        rfl

theorem cell23_3218501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_3218501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218501 prefixEnd_3218501 := by exact prefixLift 3218501
  have htrace : WordTrace (prefixWord ++ tailWord_3218501) baseStart_3218501 baseEnd_3218501 := by
    simpa [prefixWord, tailWord_3218501, baseEnd_3218501] using wordTrace_append hprefix tailTrace_3218501
  have hstable : (prefixWord ++ tailWord_3218501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218501).length < 2 ^ (prefixWord ++ tailWord_3218501).sum := by decide
  have hdescent : baseEnd_3218501 < baseStart_3218501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3218531 : Nat := 118140960795 + 3218531 * 2 ^ 59
def prefixEnd_3218531 : Nat := 4983230072969 + 3 ^ 40 * 3218531 * 2
def baseEnd_3218531 : Nat := 1652653404396052216360751

theorem tailTrace_3218531 : CollatzResearch.WordTrace tailWord_3218531 prefixEnd_3218531 1652653404396052216360751 := by
  unfold tailWord_3218531
  simp only [CollatzResearch.WordTrace]
  refine ⟨117389469502819343177543447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78259646335212895451695631 117389469502819343177543447)
  ·
    refine ⟨176084204254229014766315171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117389469502819343177543447 176084204254229014766315171)
    ·
      refine ⟨264126306381343522149472757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176084204254229014766315171 264126306381343522149472757)
      ·
        refine ⟨24761841223250955201513071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264126306381343522149472757 24761841223250955201513071)
        ·
          refine ⟨37142761834876432802269607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24761841223250955201513071 37142761834876432802269607)
          ·
            refine ⟨55714142752314649203404411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37142761834876432802269607 55714142752314649203404411)
            ·
              refine ⟨83571214128471973805106617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55714142752314649203404411 83571214128471973805106617)
              ·
                refine ⟨62678410596353980353829963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83571214128471973805106617 62678410596353980353829963)
                ·
                  refine ⟨94017615894530970530744945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62678410596353980353829963 94017615894530970530744945)
                  ·
                    refine ⟨70513211920898227898058709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94017615894530970530744945 70513211920898227898058709)
                    ·
                      refine ⟨1652653404396052216360751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70513211920898227898058709 1652653404396052216360751)
                      ·
                        rfl

theorem cell23_3218531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3218531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218531 prefixEnd_3218531 := by exact prefixLift 3218531
  have htrace : WordTrace (prefixWord ++ tailWord_3218531) baseStart_3218531 baseEnd_3218531 := by
    simpa [prefixWord, tailWord_3218531, baseEnd_3218531] using wordTrace_append hprefix tailTrace_3218531
  have hstable : (prefixWord ++ tailWord_3218531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218531).length < 2 ^ (prefixWord ++ tailWord_3218531).sum := by decide
  have hdescent : baseEnd_3218531 < baseStart_3218531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218602 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3218602 : Nat := 118140960795 + 3218602 * 2 ^ 59
def prefixEnd_3218602 : Nat := 4983230072969 + 3 ^ 40 * 3218602 * 2
def baseEnd_3218602 : Nat := 550896620507507146190975

theorem tailTrace_3218602 : CollatzResearch.WordTrace tailWord_3218602 prefixEnd_3218602 550896620507507146190975 := by
  unfold tailWord_3218602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348014771390530575844515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78261372723708081535585373 29348014771390530575844515)
  ·
    refine ⟨44022022157085795863766773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29348014771390530575844515 44022022157085795863766773)
    ·
      refine ⟨4127064577226793362228135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44022022157085795863766773 4127064577226793362228135)
      ·
        refine ⟨6190596865840190043342203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127064577226793362228135 6190596865840190043342203)
        ·
          refine ⟨9285895298760285065013305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190596865840190043342203 9285895298760285065013305)
          ·
            refine ⟨6964421474070213798759979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9285895298760285065013305 6964421474070213798759979)
            ·
              refine ⟨10446632211105320698139969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964421474070213798759979 10446632211105320698139969)
              ·
                refine ⟨7834974158328990523604977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446632211105320698139969 7834974158328990523604977)
                ·
                  refine ⟨5876230618746742892703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7834974158328990523604977 5876230618746742892703733)
                  ·
                    refine ⟨550896620507507146190975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5876230618746742892703733 550896620507507146190975)
                    ·
                      rfl

theorem cell23_3218602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3218602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218602 prefixEnd_3218602 := by exact prefixLift 3218602
  have htrace : WordTrace (prefixWord ++ tailWord_3218602) baseStart_3218602 baseEnd_3218602 := by
    simpa [prefixWord, tailWord_3218602, baseEnd_3218602] using wordTrace_append hprefix tailTrace_3218602
  have hstable : (prefixWord ++ tailWord_3218602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218602).length < 2 ^ (prefixWord ++ tailWord_3218602).sum := by decide
  have hdescent : baseEnd_3218602 < baseStart_3218602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218642 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3218642 : Nat := 118140960795 + 3218642 * 2 ^ 59
def prefixEnd_3218642 : Nat := 4983230072969 + 3 ^ 40 * 3218642 * 2
def baseEnd_3218642 : Nat := 1652710400748701282072741

theorem tailTrace_3218642 : CollatzResearch.WordTrace tailWord_3218642 prefixEnd_3218642 1652710400748701282072741 := by
  unfold tailWord_3218642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348379501354302283708545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78262345336944806089889453 29348379501354302283708545)
  ·
    refine ⟨22011284626015726712781409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29348379501354302283708545 22011284626015726712781409)
    ·
      refine ⟨16508463469511795034586057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22011284626015726712781409 16508463469511795034586057)
      ·
        refine ⟨12381347602133846275939543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16508463469511795034586057 12381347602133846275939543)
        ·
          refine ⟨18572021403200769413909315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381347602133846275939543 18572021403200769413909315)
          ·
            refine ⟨27858032104801154120863973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572021403200769413909315 27858032104801154120863973)
            ·
              refine ⟨5223381019650216397661995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27858032104801154120863973 5223381019650216397661995)
              ·
                refine ⟨7835071529475324596492993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223381019650216397661995 7835071529475324596492993)
                ·
                  refine ⟨5876303647106493447369745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7835071529475324596492993 5876303647106493447369745)
                  ·
                    refine ⟨4407227735329870085527309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5876303647106493447369745 4407227735329870085527309)
                    ·
                      refine ⟨1652710400748701282072741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407227735329870085527309 1652710400748701282072741)
                      ·
                        rfl

theorem cell23_3218642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3218642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218642 prefixEnd_3218642 := by exact prefixLift 3218642
  have htrace : WordTrace (prefixWord ++ tailWord_3218642) baseStart_3218642 baseEnd_3218642 := by
    simpa [prefixWord, tailWord_3218642, baseEnd_3218642] using wordTrace_append hprefix tailTrace_3218642
  have hstable : (prefixWord ++ tailWord_3218642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218642).length < 2 ^ (prefixWord ++ tailWord_3218642).sum := by decide
  have hdescent : baseEnd_3218642 < baseStart_3218642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218666 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3218666 : Nat := 118140960795 + 3218666 * 2 ^ 59
def prefixEnd_3218666 : Nat := 4983230072969 + 3 ^ 40 * 3218666 * 2
def baseEnd_3218666 : Nat := 550907574761469729390877

theorem tailTrace_3218666 : CollatzResearch.WordTrace tailWord_3218666 prefixEnd_3218666 550907574761469729390877 := by
  unfold tailWord_3218666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348598339332565308426963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78262928904886840822471901 29348598339332565308426963)
  ·
    refine ⟨44022897508998847962640445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29348598339332565308426963 44022897508998847962640445)
    ·
      refine ⟨16508586565874567985990167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44022897508998847962640445 16508586565874567985990167)
      ·
        refine ⟨24762879848811851978985251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508586565874567985990167 24762879848811851978985251)
        ·
          refine ⟨37144319773217777968477877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762879848811851978985251 37144319773217777968477877)
          ·
            refine ⟨3482279978739166684544801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37144319773217777968477877 3482279978739166684544801)
            ·
              refine ⟨2611709984054375013408601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482279978739166684544801 2611709984054375013408601)
              ·
                refine ⟨1958782488040781260056451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611709984054375013408601 1958782488040781260056451)
                ·
                  refine ⟨2938173732061171890084677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958782488040781260056451 2938173732061171890084677)
                  ·
                    refine ⟨550907574761469729390877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938173732061171890084677 550907574761469729390877)
                    ·
                      rfl

theorem cell23_3218666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3218666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218666 prefixEnd_3218666 := by exact prefixLift 3218666
  have htrace : WordTrace (prefixWord ++ tailWord_3218666) baseStart_3218666 baseEnd_3218666 := by
    simpa [prefixWord, tailWord_3218666, baseEnd_3218666] using wordTrace_append hprefix tailTrace_3218666
  have hstable : (prefixWord ++ tailWord_3218666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218666).length < 2 ^ (prefixWord ++ tailWord_3218666).sum := by decide
  have hdescent : baseEnd_3218666 < baseStart_3218666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218699 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 2, 3, 2]
def baseStart_3218699 : Nat := 118140960795 + 3218699 * 2 ^ 59
def prefixEnd_3218699 : Nat := 4983230072969 + 3 ^ 40 * 3218699 * 2
def baseEnd_3218699 : Nat := 1652739669146007559059979

theorem tailTrace_3218699 : CollatzResearch.WordTrace tailWord_3218699 prefixEnd_3218699 1652739669146007559059979 := by
  unfold tailWord_3218699
  simp only [CollatzResearch.WordTrace]
  refine ⟨117395596966210707869659151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78263731310807138579772767 117395596966210707869659151)
  ·
    refine ⟨176093395449316061804488727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117395596966210707869659151 176093395449316061804488727)
    ·
      refine ⟨264140093173974092706733091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176093395449316061804488727 264140093173974092706733091)
      ·
        refine ⟨396210139760961139060099637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264140093173974092706733091 396210139760961139060099637)
        ·
          refine ⟨37144700602590106786884341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 396210139760961139060099637 37144700602590106786884341)
          ·
            refine ⟨3482315681492822511270407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37144700602590106786884341 3482315681492822511270407)
            ·
              refine ⟨5223473522239233766905611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482315681492822511270407 5223473522239233766905611)
              ·
                refine ⟨7835210283358850650358417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223473522239233766905611 7835210283358850650358417)
                ·
                  refine ⟨5876407712519137987768813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7835210283358850650358417 5876407712519137987768813)
                  ·
                    refine ⟨2203652892194676745413305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5876407712519137987768813 2203652892194676745413305)
                    ·
                      refine ⟨1652739669146007559059979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203652892194676745413305 1652739669146007559059979)
                      ·
                        rfl

theorem cell23_3218699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3, 2].length) (baseStart_3218699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218699 prefixEnd_3218699 := by exact prefixLift 3218699
  have htrace : WordTrace (prefixWord ++ tailWord_3218699) baseStart_3218699 baseEnd_3218699 := by
    simpa [prefixWord, tailWord_3218699, baseEnd_3218699] using wordTrace_append hprefix tailTrace_3218699
  have hstable : (prefixWord ++ tailWord_3218699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218699).length < 2 ^ (prefixWord ++ tailWord_3218699).sum := by decide
  have hdescent : baseEnd_3218699 < baseStart_3218699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218705 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_3218705 : Nat := 118140960795 + 3218705 * 2 ^ 59
def prefixEnd_3218705 : Nat := 4983230072969 + 3 ^ 40 * 3218705 * 2
def baseEnd_3218705 : Nat := 550914250009978178528317

theorem tailTrace_3218705 : CollatzResearch.WordTrace tailWord_3218705 prefixEnd_3218705 550914250009978178528317 := by
  unfold tailWord_3218705
  simp only [CollatzResearch.WordTrace]
  refine ⟨117395815804188970894377569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78263877202792647262918379 117395815804188970894377569)
  ·
    refine ⟨88046861853141728170783177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117395815804188970894377569 88046861853141728170783177)
    ·
      refine ⟨66035146389856296128087383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88046861853141728170783177 66035146389856296128087383)
      ·
        refine ⟨99052719584784444192131075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66035146389856296128087383 99052719584784444192131075)
        ·
          refine ⟨148579079377176666288196613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99052719584784444192131075 148579079377176666288196613)
          ·
            refine ⟨27858577383220624929036865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148579079377176666288196613 27858577383220624929036865)
            ·
              refine ⟨20893933037415468696777649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27858577383220624929036865 20893933037415468696777649)
              ·
                refine ⟨15670449778061601522583237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20893933037415468696777649 15670449778061601522583237)
                ·
                  refine ⟨2938209333386550285484357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15670449778061601522583237 2938209333386550285484357)
                  ·
                    refine ⟨550914250009978178528317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938209333386550285484357 550914250009978178528317)
                    ·
                      rfl

theorem cell23_3218705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_3218705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218705 prefixEnd_3218705 := by exact prefixLift 3218705
  have htrace : WordTrace (prefixWord ++ tailWord_3218705) baseStart_3218705 baseEnd_3218705 := by
    simpa [prefixWord, tailWord_3218705, baseEnd_3218705] using wordTrace_append hprefix tailTrace_3218705
  have hstable : (prefixWord ++ tailWord_3218705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218705).length < 2 ^ (prefixWord ++ tailWord_3218705).sum := by decide
  have hdescent : baseEnd_3218705 < baseStart_3218705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218712 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3218712 : Nat := 118140960795 + 3218712 * 2 ^ 59
def prefixEnd_3218712 : Nat := 4983230072969 + 3 ^ 40 * 3218712 * 2
def baseEnd_3218712 : Nat := 1652746344394516008197419

theorem tailTrace_3218712 : CollatzResearch.WordTrace tailWord_3218712 prefixEnd_3218712 1652746344394516008197419 := by
  unfold tailWord_3218712
  simp only [CollatzResearch.WordTrace]
  refine ⟨58698035557581805544941195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78264047410109074059921593 58698035557581805544941195)
  ·
    refine ⟨88047053336372708317411793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58698035557581805544941195 88047053336372708317411793)
    ·
      refine ⟨66035290002279531238058845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88047053336372708317411793 66035290002279531238058845)
      ·
        refine ⟨24763233750854824214272067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66035290002279531238058845 24763233750854824214272067)
        ·
          refine ⟨37144850626282236321408101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24763233750854824214272067 37144850626282236321408101)
          ·
            refine ⟨6964659492427919310264019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37144850626282236321408101 6964659492427919310264019)
            ·
              refine ⟨10446989238641878965396029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964659492427919310264019 10446989238641878965396029)
              ·
                refine ⟨3917620964490704612023511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10446989238641878965396029 3917620964490704612023511)
                ·
                  refine ⟨5876431446736056918035267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917620964490704612023511 5876431446736056918035267)
                  ·
                    refine ⟨8814647170104085377052901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876431446736056918035267 8814647170104085377052901)
                    ·
                      refine ⟨1652746344394516008197419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8814647170104085377052901 1652746344394516008197419)
                      ·
                        rfl

theorem cell23_3218712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3218712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218712 prefixEnd_3218712 := by exact prefixLift 3218712
  have htrace : WordTrace (prefixWord ++ tailWord_3218712) baseStart_3218712 baseEnd_3218712 := by
    simpa [prefixWord, tailWord_3218712, baseEnd_3218712] using wordTrace_append hprefix tailTrace_3218712
  have hstable : (prefixWord ++ tailWord_3218712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218712).length < 2 ^ (prefixWord ++ tailWord_3218712).sum := by decide
  have hdescent : baseEnd_3218712 < baseStart_3218712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218739 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 2, 4]
def baseStart_3218739 : Nat := 118140960795 + 3218739 * 2 ^ 59
def prefixEnd_3218739 : Nat := 4983230072969 + 3 ^ 40 * 3218739 * 2
def baseEnd_3218739 : Nat := 550920069457395800853265

theorem tailTrace_3218739 : CollatzResearch.WordTrace tailWord_3218739 prefixEnd_3218739 550920069457395800853265 := by
  unfold tailWord_3218739
  simp only [CollatzResearch.WordTrace]
  refine ⟨117397055886065794701115271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78264703924043863134076847 117397055886065794701115271)
  ·
    refine ⟨176095583829098692051672907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117397055886065794701115271 176095583829098692051672907)
    ·
      refine ⟨264143375743648038077509361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176095583829098692051672907 264143375743648038077509361)
      ·
        refine ⟨198107531807736028558132021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264143375743648038077509361 198107531807736028558132021)
        ·
          refine ⟨18572581106975252677324877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198107531807736028558132021 18572581106975252677324877)
          ·
            refine ⟨6964717915115719753996829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18572581106975252677324877 6964717915115719753996829)
            ·
              refine ⟨2611769218168394907748811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6964717915115719753996829 2611769218168394907748811)
              ·
                refine ⟨3917653827252592361623217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611769218168394907748811 3917653827252592361623217)
                ·
                  refine ⟨2938240370439444271217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917653827252592361623217 2938240370439444271217413)
                  ·
                    refine ⟨550920069457395800853265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938240370439444271217413 550920069457395800853265)
                    ·
                      rfl

theorem cell23_3218739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 4].length) (baseStart_3218739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218739 prefixEnd_3218739 := by exact prefixLift 3218739
  have htrace : WordTrace (prefixWord ++ tailWord_3218739) baseStart_3218739 baseEnd_3218739 := by
    simpa [prefixWord, tailWord_3218739, baseEnd_3218739] using wordTrace_append hprefix tailTrace_3218739
  have hstable : (prefixWord ++ tailWord_3218739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218739).length < 2 ^ (prefixWord ++ tailWord_3218739).sum := by decide
  have hdescent : baseEnd_3218739 < baseStart_3218739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218774 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3218774 : Nat := 118140960795 + 3218774 * 2 ^ 59
def prefixEnd_3218774 : Nat := 4983230072969 + 3 ^ 40 * 3218774 * 2
def baseEnd_3218774 : Nat := 1652778180195094765622135

theorem tailTrace_3218774 : CollatzResearch.WordTrace tailWord_3218774 prefixEnd_3218774 1652778180195094765622135 := by
  unfold tailWord_3218774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337395777558687229914961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78265554960625997119092917 7337395777558687229914961)
  ·
    refine ⟨5503046833169015422436221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7337395777558687229914961 5503046833169015422436221)
    ·
      refine ⟨2063642562438380783413583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5503046833169015422436221 2063642562438380783413583)
      ·
        refine ⟨3095463843657571175120375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063642562438380783413583 3095463843657571175120375)
        ·
          refine ⟨4643195765486356762680563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095463843657571175120375 4643195765486356762680563)
          ·
            refine ⟨6964793648229535144020845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643195765486356762680563 6964793648229535144020845)
            ·
              refine ⟨2611797618086075679007817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6964793648229535144020845 2611797618086075679007817)
              ·
                refine ⟨1958848213564556759255863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611797618086075679007817 1958848213564556759255863)
                ·
                  refine ⟨2938272320346835138883795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958848213564556759255863 2938272320346835138883795)
                  ·
                    refine ⟨4407408480520252708325693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938272320346835138883795 4407408480520252708325693)
                    ·
                      refine ⟨1652778180195094765622135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407408480520252708325693 1652778180195094765622135)
                      ·
                        rfl

theorem cell23_3218774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3218774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218774 prefixEnd_3218774 := by exact prefixLift 3218774
  have htrace : WordTrace (prefixWord ++ tailWord_3218774) baseStart_3218774 baseEnd_3218774 := by
    simpa [prefixWord, tailWord_3218774, baseEnd_3218774] using wordTrace_append hprefix tailTrace_3218774
  have hstable : (prefixWord ++ tailWord_3218774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218774).length < 2 ^ (prefixWord ++ tailWord_3218774).sum := by decide
  have hdescent : baseEnd_3218774 < baseStart_3218774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218796 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_3218796 : Nat := 118140960795 + 3218796 * 2 ^ 59
def prefixEnd_3218796 : Nat := 4983230072969 + 3 ^ 40 * 3218796 * 2
def baseEnd_3218796 : Nat := 1652789476769493679547033

theorem tailTrace_3218796 : CollatzResearch.WordTrace tailWord_3218796 prefixEnd_3218796 1652789476769493679547033 := by
  unfold tailWord_3218796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58699567423429646717970121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78266089897906195623960161 58699567423429646717970121)
  ·
    refine ⟨44024675567572235038477591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58699567423429646717970121 44024675567572235038477591)
    ·
      refine ⟨66037013351358352557716387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44024675567572235038477591 66037013351358352557716387)
      ·
        refine ⟨99055520027037528836574581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66037013351358352557716387 99055520027037528836574581)
        ·
          refine ⟨9286455002534768328428867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99055520027037528836574581 9286455002534768328428867)
          ·
            refine ⟨13929682503802152492643301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286455002534768328428867 13929682503802152492643301)
            ·
              refine ⟨2611815469462903592370619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13929682503802152492643301 2611815469462903592370619)
              ·
                refine ⟨3917723204194355388555929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611815469462903592370619 3917723204194355388555929)
                ·
                  refine ⟨2938292403145766541416947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917723204194355388555929 2938292403145766541416947)
                  ·
                    refine ⟨4407438604718649812125421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938292403145766541416947 4407438604718649812125421)
                    ·
                      refine ⟨1652789476769493679547033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407438604718649812125421 1652789476769493679547033)
                      ·
                        rfl

theorem cell23_3218796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_3218796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218796 prefixEnd_3218796 := by exact prefixLift 3218796
  have htrace : WordTrace (prefixWord ++ tailWord_3218796) baseStart_3218796 baseEnd_3218796 := by
    simpa [prefixWord, tailWord_3218796, baseEnd_3218796] using wordTrace_append hprefix tailTrace_3218796
  have hstable : (prefixWord ++ tailWord_3218796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218796).length < 2 ^ (prefixWord ++ tailWord_3218796).sum := by decide
  have hdescent : baseEnd_3218796 < baseStart_3218796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218819 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 4, 2]
def baseStart_3218819 : Nat := 118140960795 + 3218819 * 2 ^ 59
def prefixEnd_3218819 : Nat := 4983230072969 + 3 ^ 40 * 3218819 * 2
def baseEnd_3218819 : Nat := 1652801286824547089559427

theorem tailTrace_3218819 : CollatzResearch.WordTrace tailWord_3218819 prefixEnd_3218819 1652801286824547089559427 := by
  unfold tailWord_3218819
  simp only [CollatzResearch.WordTrace]
  refine ⟨117399973725775968364027511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78266649150517312242685007 117399973725775968364027511)
  ·
    refine ⟨176099960588663952546041267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117399973725775968364027511 176099960588663952546041267)
    ·
      refine ⟨264149940882995928819061901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176099960588663952546041267 264149940882995928819061901)
      ·
        refine ⟨99056227831123473307148213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264149940882995928819061901 99056227831123473307148213)
        ·
          refine ⟨9286521359167825622545145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99056227831123473307148213 9286521359167825622545145)
          ·
            refine ⟨6964891019375869216908859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9286521359167825622545145 6964891019375869216908859)
            ·
              refine ⟨10447336529063803825363289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964891019375869216908859 10447336529063803825363289)
              ·
                refine ⟨7835502396797852869022467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10447336529063803825363289 7835502396797852869022467)
                ·
                  refine ⟨11753253595196779303533701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835502396797852869022467 11753253595196779303533701)
                  ·
                    refine ⟨2203735049099396119412569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11753253595196779303533701 2203735049099396119412569)
                    ·
                      refine ⟨1652801286824547089559427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203735049099396119412569 1652801286824547089559427)
                      ·
                        rfl

theorem cell23_3218819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_3218819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218819 prefixEnd_3218819 := by exact prefixLift 3218819
  have htrace : WordTrace (prefixWord ++ tailWord_3218819) baseStart_3218819 baseEnd_3218819 := by
    simpa [prefixWord, tailWord_3218819, baseEnd_3218819] using wordTrace_append hprefix tailTrace_3218819
  have hstable : (prefixWord ++ tailWord_3218819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218819).length < 2 ^ (prefixWord ++ tailWord_3218819).sum := by decide
  have hdescent : baseEnd_3218819 < baseStart_3218819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218835 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3]
def baseStart_3218835 : Nat := 118140960795 + 3218835 * 2 ^ 59
def prefixEnd_3218835 : Nat := 4983230072969 + 3 ^ 40 * 3218835 * 2
def baseEnd_3218835 : Nat := 1652809502515019026959353

theorem tailTrace_3218835 : CollatzResearch.WordTrace tailWord_3218835 prefixEnd_3218835 1652809502515019026959353 := by
  unfold tailWord_3218835
  simp only [CollatzResearch.WordTrace]
  refine ⟨117400557293718003096609959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78267038195812002064406639 117400557293718003096609959)
  ·
    refine ⟨176100835940577004644914939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117400557293718003096609959 176100835940577004644914939)
    ·
      refine ⟨264151253910865506967372409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176100835940577004644914939 264151253910865506967372409)
      ·
        refine ⟨198113440433149130225529307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264151253910865506967372409 198113440433149130225529307)
        ·
          refine ⟨297170160649723695338293961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198113440433149130225529307 297170160649723695338293961)
          ·
            refine ⟨222877620487292771503720471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297170160649723695338293961 222877620487292771503720471)
            ·
              refine ⟨334316430730939157255580707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222877620487292771503720471 334316430730939157255580707)
              ·
                refine ⟨501474646096408735883371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334316430730939157255580707 501474646096408735883371061)
                ·
                  refine ⟨47013248071538318989066037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501474646096408735883371061 47013248071538318989066037)
                  ·
                    refine ⟨4407492006706717405224941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47013248071538318989066037 4407492006706717405224941)
                    ·
                      refine ⟨1652809502515019026959353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407492006706717405224941 1652809502515019026959353)
                      ·
                        rfl

theorem cell23_3218835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_3218835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218835 prefixEnd_3218835 := by exact prefixLift 3218835
  have htrace : WordTrace (prefixWord ++ tailWord_3218835) baseStart_3218835 baseEnd_3218835 := by
    simpa [prefixWord, tailWord_3218835, baseEnd_3218835] using wordTrace_append hprefix tailTrace_3218835
  have hstable : (prefixWord ++ tailWord_3218835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218835).length < 2 ^ (prefixWord ++ tailWord_3218835).sum := by decide
  have hdescent : baseEnd_3218835 < baseStart_3218835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218872 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_3218872 : Nat := 118140960795 + 3218872 * 2 ^ 59
def prefixEnd_3218872 : Nat := 4983230072969 + 3 ^ 40 * 3218872 * 2
def baseEnd_3218872 : Nat := 550942833766411794065561

theorem tailTrace_3218872 : CollatzResearch.WordTrace tailWord_3218872 prefixEnd_3218872 550942833766411794065561 := by
  unfold tailWord_3218872
  simp only [CollatzResearch.WordTrace]
  refine ⟨58700953397291979207853435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78267937863055972277137913 58700953397291979207853435)
  ·
    refine ⟨88051430095937968811780153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58700953397291979207853435 88051430095937968811780153)
    ·
      refine ⟨66038572571953476608835115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88051430095937968811780153 66038572571953476608835115)
      ·
        refine ⟨99057858857930214913252673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66038572571953476608835115 99057858857930214913252673)
        ·
          refine ⟨74293394143447661184939505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99057858857930214913252673 74293394143447661184939505)
          ·
            refine ⟨55720045607585745888704629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74293394143447661184939505 55720045607585745888704629)
            ·
              refine ⟨5223754275711163677066059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55720045607585745888704629 5223754275711163677066059)
              ·
                refine ⟨7835631413566745515599089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223754275711163677066059 7835631413566745515599089)
                ·
                  refine ⟨5876723560175059136699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7835631413566745515599089 5876723560175059136699317)
                  ·
                    refine ⟨550942833766411794065561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5876723560175059136699317 550942833766411794065561)
                    ·
                      rfl

theorem cell23_3218872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_3218872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218872 prefixEnd_3218872 := by exact prefixLift 3218872
  have htrace : WordTrace (prefixWord ++ tailWord_3218872) baseStart_3218872 baseEnd_3218872 := by
    simpa [prefixWord, tailWord_3218872, baseEnd_3218872] using wordTrace_append hprefix tailTrace_3218872
  have hstable : (prefixWord ++ tailWord_3218872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218872).length < 2 ^ (prefixWord ++ tailWord_3218872).sum := by decide
  have hdescent : baseEnd_3218872 < baseStart_3218872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218876 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 5]
def baseStart_3218876 : Nat := 118140960795 + 3218876 * 2 ^ 59
def prefixEnd_3218876 : Nat := 4983230072969 + 3 ^ 40 * 3218876 * 2
def baseEnd_3218876 : Nat := 183647839469094818505185

theorem tailTrace_3218876 : CollatzResearch.WordTrace tailWord_3218876 prefixEnd_3218876 183647839469094818505185 := by
  unfold tailWord_3218876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58701026343284733549426241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78268035124379644732568321 58701026343284733549426241)
  ·
    refine ⟨44025769757463550162069681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58701026343284733549426241 44025769757463550162069681)
    ·
      refine ⟨33019327318097662621552261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44025769757463550162069681 33019327318097662621552261)
      ·
        refine ⟨6191123872143311741541049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33019327318097662621552261 6191123872143311741541049)
        ·
          refine ⟨4643342904107483806155787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6191123872143311741541049 4643342904107483806155787)
          ·
            refine ⟨6965014356161225709233681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643342904107483806155787 6965014356161225709233681)
            ·
              refine ⟨5223760767120919281925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6965014356161225709233681 5223760767120919281925261)
              ·
                refine ⟨1958910287670344730721973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5223760767120919281925261 1958910287670344730721973)
                ·
                  refine ⟨183647839469094818505185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958910287670344730721973 183647839469094818505185)
                  ·
                    rfl

theorem cell23_3218876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_3218876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218876 prefixEnd_3218876 := by exact prefixLift 3218876
  have htrace : WordTrace (prefixWord ++ tailWord_3218876) baseStart_3218876 baseEnd_3218876 := by
    simpa [prefixWord, tailWord_3218876, baseEnd_3218876] using wordTrace_append hprefix tailTrace_3218876
  have hstable : (prefixWord ++ tailWord_3218876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218876).length < 2 ^ (prefixWord ++ tailWord_3218876).sum := by decide
  have hdescent : baseEnd_3218876 < baseStart_3218876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218895 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_3218895 : Nat := 118140960795 + 3218895 * 2 ^ 59
def prefixEnd_3218895 : Nat := 4983230072969 + 3 ^ 40 * 3218895 * 2
def baseEnd_3218895 : Nat := 1652840311354288792209077

theorem tailTrace_3218895 : CollatzResearch.WordTrace tailWord_3218895 prefixEnd_3218895 1652840311354288792209077 := by
  unfold tailWord_3218895
  simp only [CollatzResearch.WordTrace]
  refine ⟨117402745673500633343794139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78268497115667088895862759 117402745673500633343794139)
  ·
    refine ⟨176104118510250950015691209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117402745673500633343794139 176104118510250950015691209)
    ·
      refine ⟨132078088882688212511768407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176104118510250950015691209 132078088882688212511768407)
      ·
        refine ⟨198117133324032318767652611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132078088882688212511768407 198117133324032318767652611)
        ·
          refine ⟨297175699986048478151478917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198117133324032318767652611 297175699986048478151478917)
          ·
            refine ⟨55720443747384089653402297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297175699986048478151478917 55720443747384089653402297)
            ·
              refine ⟨41790332810538067240051723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55720443747384089653402297 41790332810538067240051723)
              ·
                refine ⟨62685499215807100860077585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41790332810538067240051723 62685499215807100860077585)
                ·
                  refine ⟨47014124411855325645058189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62685499215807100860077585 47014124411855325645058189)
                  ·
                    refine ⟨17630296654445747116896821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47014124411855325645058189 17630296654445747116896821)
                    ·
                      refine ⟨1652840311354288792209077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17630296654445747116896821 1652840311354288792209077)
                      ·
                        rfl

theorem cell23_3218895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_3218895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218895 prefixEnd_3218895 := by exact prefixLift 3218895
  have htrace : WordTrace (prefixWord ++ tailWord_3218895) baseStart_3218895 baseEnd_3218895 := by
    simpa [prefixWord, tailWord_3218895, baseEnd_3218895] using wordTrace_append hprefix tailTrace_3218895
  have hstable : (prefixWord ++ tailWord_3218895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218895).length < 2 ^ (prefixWord ++ tailWord_3218895).sum := by decide
  have hdescent : baseEnd_3218895 < baseStart_3218895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218912 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3218912 : Nat := 118140960795 + 3218912 * 2 ^ 59
def prefixEnd_3218912 : Nat := 4983230072969 + 3 ^ 40 * 3218912 * 2
def baseEnd_3218912 : Nat := 1652849040525415225696499

theorem tailTrace_3218912 : CollatzResearch.WordTrace tailWord_3218912 prefixEnd_3218912 1652849040525415225696499 := by
  unfold tailWord_3218912
  simp only [CollatzResearch.WordTrace]
  refine ⟨58701682857219522623581495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78268910476292696831441993 58701682857219522623581495)
  ·
    refine ⟨88052524285829283935372243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58701682857219522623581495 88052524285829283935372243)
    ·
      refine ⟨132078786428743925903058365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88052524285829283935372243 132078786428743925903058365)
      ·
        refine ⟨49529544910778972213646887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132078786428743925903058365 49529544910778972213646887)
        ·
          refine ⟨74294317366168458320470331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49529544910778972213646887 74294317366168458320470331)
          ·
            refine ⟨111441476049252687480705497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74294317366168458320470331 111441476049252687480705497)
            ·
              refine ⟨83581107036939515610529123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111441476049252687480705497 83581107036939515610529123)
              ·
                refine ⟨125371660555409273415793685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83581107036939515610529123 125371660555409273415793685)
                ·
                  refine ⟨5876796588534809691365329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125371660555409273415793685 5876796588534809691365329)
                  ·
                    refine ⟨4407597441401107268523997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5876796588534809691365329 4407597441401107268523997)
                    ·
                      refine ⟨1652849040525415225696499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407597441401107268523997 1652849040525415225696499)
                      ·
                        rfl

theorem cell23_3218912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3218912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218912 prefixEnd_3218912 := by exact prefixLift 3218912
  have htrace : WordTrace (prefixWord ++ tailWord_3218912) baseStart_3218912 baseEnd_3218912 := by
    simpa [prefixWord, tailWord_3218912, baseEnd_3218912] using wordTrace_append hprefix tailTrace_3218912
  have hstable : (prefixWord ++ tailWord_3218912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218912).length < 2 ^ (prefixWord ++ tailWord_3218912).sum := by decide
  have hdescent : baseEnd_3218912 < baseStart_3218912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218919 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3218919 : Nat := 118140960795 + 3218919 * 2 ^ 59
def prefixEnd_3218919 : Nat := 4983230072969 + 3 ^ 40 * 3218919 * 2
def baseEnd_3218919 : Nat := 550950878296665566102989

theorem tailTrace_3218919 : CollatzResearch.WordTrace tailWord_3218919 prefixEnd_3218919 550950878296665566102989 := by
  unfold tailWord_3218919
  simp only [CollatzResearch.WordTrace]
  refine ⟨117403621025413685442667811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78269080683609123628445207 117403621025413685442667811)
  ·
    refine ⟨176105431538120528164001717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117403621025413685442667811 176105431538120528164001717)
    ·
      refine ⟨16509884206698799515375161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176105431538120528164001717 16509884206698799515375161)
      ·
        refine ⟨12382413155024099636531371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16509884206698799515375161 12382413155024099636531371)
        ·
          refine ⟨18573619732536149454797057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12382413155024099636531371 18573619732536149454797057)
          ·
            refine ⟨13930214799402112091097793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18573619732536149454797057 13930214799402112091097793)
            ·
              refine ⟨10447661099551584068323345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13930214799402112091097793 10447661099551584068323345)
              ·
                refine ⟨7835745824663688051242509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10447661099551584068323345 7835745824663688051242509)
                ·
                  refine ⟨2938404684248883019215941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7835745824663688051242509 2938404684248883019215941)
                  ·
                    refine ⟨550950878296665566102989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938404684248883019215941 550950878296665566102989)
                    ·
                      rfl

theorem cell23_3218919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3218919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218919 prefixEnd_3218919 := by exact prefixLift 3218919
  have htrace : WordTrace (prefixWord ++ tailWord_3218919) baseStart_3218919 baseEnd_3218919 := by
    simpa [prefixWord, tailWord_3218919, baseEnd_3218919] using wordTrace_append hprefix tailTrace_3218919
  have hstable : (prefixWord ++ tailWord_3218919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218919).length < 2 ^ (prefixWord ++ tailWord_3218919).sum := by decide
  have hdescent : baseEnd_3218919 < baseStart_3218919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3218935 : Nat := 118140960795 + 3218935 * 2 ^ 59
def prefixEnd_3218935 : Nat := 4983230072969 + 3 ^ 40 * 3218935 * 2
def baseEnd_3218935 : Nat := 1652860850580468635708893

theorem tailTrace_3218935 : CollatzResearch.WordTrace tailWord_3218935 prefixEnd_3218935 1652860850580468635708893 := by
  unfold tailWord_3218935
  simp only [CollatzResearch.WordTrace]
  refine ⟨117404204593355720175250259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78269469728903813450166839 117404204593355720175250259)
  ·
    refine ⟨176106306890033580262875389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117404204593355720175250259 176106306890033580262875389)
    ·
      refine ⟨66039865083762592598578271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176106306890033580262875389 66039865083762592598578271)
      ·
        refine ⟨99059797625643888897867407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66039865083762592598578271 99059797625643888897867407)
        ·
          refine ⟨148589696438465833346801111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99059797625643888897867407 148589696438465833346801111)
          ·
            refine ⟨222884544657698750020201667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148589696438465833346801111 222884544657698750020201667)
            ·
              refine ⟨334326816986548125030302501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222884544657698750020201667 334326816986548125030302501)
              ·
                refine ⟨62686278184977773443181719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334326816986548125030302501 62686278184977773443181719)
                ·
                  refine ⟨94029417277466660164772579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62686278184977773443181719 94029417277466660164772579)
                  ·
                    refine ⟨141044125916199990247158869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94029417277466660164772579 141044125916199990247158869)
                    ·
                      refine ⟨1652860850580468635708893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 141044125916199990247158869 1652860850580468635708893)
                      ·
                        rfl

theorem cell23_3218935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3218935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218935 prefixEnd_3218935 := by exact prefixLift 3218935
  have htrace : WordTrace (prefixWord ++ tailWord_3218935) baseStart_3218935 baseEnd_3218935 := by
    simpa [prefixWord, tailWord_3218935, baseEnd_3218935] using wordTrace_append hprefix tailTrace_3218935
  have hstable : (prefixWord ++ tailWord_3218935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218935).length < 2 ^ (prefixWord ++ tailWord_3218935).sum := by decide
  have hdescent : baseEnd_3218935 < baseStart_3218935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218936 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 1, 4]
def baseStart_3218936 : Nat := 118140960795 + 3218936 * 2 ^ 59
def prefixEnd_3218936 : Nat := 4983230072969 + 3 ^ 40 * 3218936 * 2
def baseEnd_3218936 : Nat := 550953788020374377265463

theorem tailTrace_3218936 : CollatzResearch.WordTrace tailWord_3218936 prefixEnd_3218936 550953788020374377265463 := by
  unfold tailWord_3218936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58702120533176048673018331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78269494044234731564024441 58702120533176048673018331)
  ·
    refine ⟨88053180799764073009527497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58702120533176048673018331 88053180799764073009527497)
    ·
      refine ⟨66039885599823054757145623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88053180799764073009527497 66039885599823054757145623)
      ·
        refine ⟨99059828399734582135718435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66039885599823054757145623 99059828399734582135718435)
        ·
          refine ⟨148589742599601873203577653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99059828399734582135718435 148589742599601873203577653)
          ·
            refine ⟨13930288368712675612835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148589742599601873203577653 13930288368712675612835405)
            ·
              refine ⟨5223858138267253354813277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13930288368712675612835405 5223858138267253354813277)
              ·
                refine ⟨1958946801850220008054979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5223858138267253354813277 1958946801850220008054979)
                ·
                  refine ⟨2938420202775330012082469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958946801850220008054979 2938420202775330012082469)
                  ·
                    refine ⟨550953788020374377265463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938420202775330012082469 550953788020374377265463)
                    ·
                      rfl

theorem cell23_3218936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_3218936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218936 prefixEnd_3218936 := by exact prefixLift 3218936
  have htrace : WordTrace (prefixWord ++ tailWord_3218936) baseStart_3218936 baseEnd_3218936 := by
    simpa [prefixWord, tailWord_3218936, baseEnd_3218936] using wordTrace_append hprefix tailTrace_3218936
  have hstable : (prefixWord ++ tailWord_3218936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218936).length < 2 ^ (prefixWord ++ tailWord_3218936).sum := by decide
  have hdescent : baseEnd_3218936 < baseStart_3218936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218946 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3218946 : Nat := 118140960795 + 3218946 * 2 ^ 59
def prefixEnd_3218946 : Nat := 4983230072969 + 3 ^ 40 * 3218946 * 2
def baseEnd_3218946 : Nat := 1652866498867668092671343

theorem tailTrace_3218946 : CollatzResearch.WordTrace tailWord_3218946 prefixEnd_3218946 1652866498867668092671343 := by
  unfold tailWord_3218946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29351151449078967263475173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78269737197543912702600461 29351151449078967263475173)
  ·
    refine ⟨5503340896702306361901595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29351151449078967263475173 5503340896702306361901595)
    ·
      refine ⟨8255011345053459542852393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503340896702306361901595 8255011345053459542852393)
      ·
        refine ⟨6191258508790094657139295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8255011345053459542852393 6191258508790094657139295)
        ·
          refine ⟨9286887763185141985708943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6191258508790094657139295 9286887763185141985708943)
          ·
            refine ⟨13930331644777712978563415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286887763185141985708943 13930331644777712978563415)
            ·
              refine ⟨20895497467166569467845123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13930331644777712978563415 20895497467166569467845123)
              ·
                refine ⟨31343246200749854201767685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20895497467166569467845123 31343246200749854201767685)
                ·
                  refine ⟨5876858662640597662831441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31343246200749854201767685 5876858662640597662831441)
                  ·
                    refine ⟨4407643996980448247123581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5876858662640597662831441 4407643996980448247123581)
                    ·
                      refine ⟨1652866498867668092671343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407643996980448247123581 1652866498867668092671343)
                      ·
                        rfl

theorem cell23_3218946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3218946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218946 prefixEnd_3218946 := by exact prefixLift 3218946
  have htrace : WordTrace (prefixWord ++ tailWord_3218946) baseStart_3218946 baseEnd_3218946 := by
    simpa [prefixWord, tailWord_3218946, baseEnd_3218946] using wordTrace_append hprefix tailTrace_3218946
  have hstable : (prefixWord ++ tailWord_3218946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218946).length < 2 ^ (prefixWord ++ tailWord_3218946).sum := by decide
  have hdescent : baseEnd_3218946 < baseStart_3218946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218979 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 3, 5]
def baseStart_3218979 : Nat := 118140960795 + 3218979 * 2 ^ 59
def prefixEnd_3218979 : Nat := 4983230072969 + 3 ^ 40 * 3218979 * 2
def baseEnd_3218979 : Nat := 550961147909755487852897

theorem tailTrace_3218979 : CollatzResearch.WordTrace tailWord_3218979 prefixEnd_3218979 550961147909755487852897 := by
  unfold tailWord_3218979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117405809405196315689851991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78270539603464210459901327 117405809405196315689851991)
  ·
    refine ⟨176108714107794473534777987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117405809405196315689851991 176108714107794473534777987)
    ·
      refine ⟨264163071161691710302166981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176108714107794473534777987 264163071161691710302166981)
      ·
        refine ⟨49530575842817195681656309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264163071161691710302166981 49530575842817195681656309)
        ·
          refine ⟨4643491485264112095155279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49530575842817195681656309 4643491485264112095155279)
          ·
            refine ⟨6965237227896168142732919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643491485264112095155279 6965237227896168142732919)
            ·
              refine ⟨10447855841844252214099379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965237227896168142732919 10447855841844252214099379)
              ·
                refine ⟨15671783762766378321149069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447855841844252214099379 15671783762766378321149069)
                ·
                  refine ⟨5876918911037391870430901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15671783762766378321149069 5876918911037391870430901)
                  ·
                    refine ⟨550961147909755487852897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5876918911037391870430901 550961147909755487852897)
                    ·
                      rfl

theorem cell23_3218979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].length) (baseStart_3218979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218979 prefixEnd_3218979 := by exact prefixLift 3218979
  have htrace : WordTrace (prefixWord ++ tailWord_3218979) baseStart_3218979 baseEnd_3218979 := by
    simpa [prefixWord, tailWord_3218979, baseEnd_3218979] using wordTrace_append hprefix tailTrace_3218979
  have hstable : (prefixWord ++ tailWord_3218979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218979).length < 2 ^ (prefixWord ++ tailWord_3218979).sum := by decide
  have hdescent : baseEnd_3218979 < baseStart_3218979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219026 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3219026 : Nat := 118140960795 + 3219026 * 2 ^ 59
def prefixEnd_3219026 : Nat := 4983230072969 + 3 ^ 40 * 3219026 * 2
def baseEnd_3219026 : Nat := 550969192440009259890325

theorem tailTrace_3219026 : CollatzResearch.WordTrace tailWord_3219026 prefixEnd_3219026 550969192440009259890325 := by
  unfold tailWord_3219026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29351880909006510679203233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78271682424017361811208621 29351880909006510679203233)
  ·
    refine ⟨22013910681754883009402425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29351880909006510679203233 22013910681754883009402425)
    ·
      refine ⟨16510433011316162257051819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22013910681754883009402425 16510433011316162257051819)
      ·
        refine ⟨24765649516974243385577729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510433011316162257051819 24765649516974243385577729)
        ·
          refine ⟨18574237137730682539183297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24765649516974243385577729 18574237137730682539183297)
          ·
            refine ⟨13930677853298011904387473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18574237137730682539183297 13930677853298011904387473)
            ·
              refine ⟨10448008389973508928290605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13930677853298011904387473 10448008389973508928290605)
              ·
                refine ⟨3918003146240065848108977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10448008389973508928290605 3918003146240065848108977)
                ·
                  refine ⟨2938502359680049386081733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918003146240065848108977 2938502359680049386081733)
                  ·
                    refine ⟨550969192440009259890325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938502359680049386081733 550969192440009259890325)
                    ·
                      rfl

theorem cell23_3219026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3219026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219026 prefixEnd_3219026 := by exact prefixLift 3219026
  have htrace : WordTrace (prefixWord ++ tailWord_3219026) baseStart_3219026 baseEnd_3219026 := by
    simpa [prefixWord, tailWord_3219026, baseEnd_3219026] using wordTrace_append hprefix tailTrace_3219026
  have hstable : (prefixWord ++ tailWord_3219026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219026).length < 2 ^ (prefixWord ++ tailWord_3219026).sum := by decide
  have hdescent : baseEnd_3219026 < baseStart_3219026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219036 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3219036 : Nat := 118140960795 + 3219036 * 2 ^ 59
def prefixEnd_3219036 : Nat := 4983230072969 + 3 ^ 40 * 3219036 * 2
def baseEnd_3219036 : Nat := 1652912712126572740545929

theorem tailTrace_3219036 : CollatzResearch.WordTrace tailWord_3219036 prefixEnd_3219036 1652912712126572740545929 := by
  unfold tailWord_3219036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58703944182994907212338481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78271925577326542949784641 58703944182994907212338481)
  ·
    refine ⟨44027958137246180409253861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58703944182994907212338481 44027958137246180409253861)
    ·
      refine ⟨8255242150733658826735099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44027958137246180409253861 8255242150733658826735099)
      ·
        refine ⟨12382863226100488240102649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255242150733658826735099 12382863226100488240102649)
        ·
          refine ⟨9287147419575366180076987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12382863226100488240102649 9287147419575366180076987)
          ·
            refine ⟨13930721129363049270115481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287147419575366180076987 13930721129363049270115481)
            ·
              refine ⟨10448040847022286952586611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13930721129363049270115481 10448040847022286952586611)
              ·
                refine ⟨15672061270533430428879917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448040847022286952586611 15672061270533430428879917)
                ·
                  refine ⟨5877022976450036410829969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15672061270533430428879917 5877022976450036410829969)
                  ·
                    refine ⟨4407767232337527308122477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877022976450036410829969 4407767232337527308122477)
                    ·
                      refine ⟨1652912712126572740545929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407767232337527308122477 1652912712126572740545929)
                      ·
                        rfl

theorem cell23_3219036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3219036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219036 prefixEnd_3219036 := by exact prefixLift 3219036
  have htrace : WordTrace (prefixWord ++ tailWord_3219036) baseStart_3219036 baseEnd_3219036 := by
    simpa [prefixWord, tailWord_3219036, baseEnd_3219036] using wordTrace_append hprefix tailTrace_3219036
  have hstable : (prefixWord ++ tailWord_3219036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219036).length < 2 ^ (prefixWord ++ tailWord_3219036).sum := by decide
  have hdescent : baseEnd_3219036 < baseStart_3219036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219037 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3219037 : Nat := 118140960795 + 3219037 * 2 ^ 59
def prefixEnd_3219037 : Nat := 4983230072969 + 3 ^ 40 * 3219037 * 2
def baseEnd_3219037 : Nat := 1652913225607227236633425

theorem tailTrace_3219037 : CollatzResearch.WordTrace tailWord_3219037 prefixEnd_3219037 1652913225607227236633425 := by
  unfold tailWord_3219037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117407924838986191595463365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78271949892657461063642243 117407924838986191595463365)
  ·
    refine ⟨22013985907309910924149381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117407924838986191595463365 22013985907309910924149381)
    ·
      refine ⟨4127622357620608298278009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22013985907309910924149381 4127622357620608298278009)
      ·
        refine ⟨3095716768215456223708507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4127622357620608298278009 3095716768215456223708507)
        ·
          refine ⟨4643575152323184335562761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095716768215456223708507 4643575152323184335562761)
          ·
            refine ⟨3482681364242388251672071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643575152323184335562761 3482681364242388251672071)
            ·
              refine ⟨5224022046363582377508107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482681364242388251672071 5224022046363582377508107)
              ·
                refine ⟨7836033069545373566262161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224022046363582377508107 7836033069545373566262161)
                ·
                  refine ⟨5877024802159030174696621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836033069545373566262161 5877024802159030174696621)
                  ·
                    refine ⟨2203884300809636315511233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5877024802159030174696621 2203884300809636315511233)
                    ·
                      refine ⟨1652913225607227236633425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203884300809636315511233 1652913225607227236633425)
                      ·
                        rfl

theorem cell23_3219037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3219037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219037 prefixEnd_3219037 := by exact prefixLift 3219037
  have htrace : WordTrace (prefixWord ++ tailWord_3219037) baseStart_3219037 baseEnd_3219037 := by
    simpa [prefixWord, tailWord_3219037, baseEnd_3219037] using wordTrace_append hprefix tailTrace_3219037
  have hstable : (prefixWord ++ tailWord_3219037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219037).length < 2 ^ (prefixWord ++ tailWord_3219037).sum := by decide
  have hdescent : baseEnd_3219037 < baseStart_3219037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219049 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_3219049 : Nat := 118140960795 + 3219049 * 2 ^ 59
def prefixEnd_3219049 : Nat := 4983230072969 + 3 ^ 40 * 3219049 * 2
def baseEnd_3219049 : Nat := 1652919387375081189683369

theorem tailTrace_3219049 : CollatzResearch.WordTrace tailWord_3219049 prefixEnd_3219049 1652919387375081189683369 := by
  unfold tailWord_3219049
  simp only [CollatzResearch.WordTrace]
  refine ⟨117408362514942717644900201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78272241676628478429933467 117408362514942717644900201)
  ·
    refine ⟨88056271886207038233675151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117408362514942717644900201 88056271886207038233675151)
    ·
      refine ⟨132084407829310557350512727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88056271886207038233675151 132084407829310557350512727)
      ·
        refine ⟨198126611743965836025769091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132084407829310557350512727 198126611743965836025769091)
        ·
          refine ⟨297189917615948754038653637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198126611743965836025769091 297189917615948754038653637)
          ·
            refine ⟨55723109552990391382247557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297189917615948754038653637 55723109552990391382247557)
            ·
              refine ⟨10448083041185698384171417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55723109552990391382247557 10448083041185698384171417)
              ·
                refine ⟨7836062280889273788128563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10448083041185698384171417 7836062280889273788128563)
                ·
                  refine ⟨11754093421333910682192845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836062280889273788128563 11754093421333910682192845)
                  ·
                    refine ⟨4407785033000216505822317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11754093421333910682192845 4407785033000216505822317)
                    ·
                      refine ⟨1652919387375081189683369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407785033000216505822317 1652919387375081189683369)
                      ·
                        rfl

theorem cell23_3219049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_3219049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219049 prefixEnd_3219049 := by exact prefixLift 3219049
  have htrace : WordTrace (prefixWord ++ tailWord_3219049) baseStart_3219049 baseEnd_3219049 := by
    simpa [prefixWord, tailWord_3219049, baseEnd_3219049] using wordTrace_append hprefix tailTrace_3219049
  have hstable : (prefixWord ++ tailWord_3219049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219049).length < 2 ^ (prefixWord ++ tailWord_3219049).sum := by decide
  have hdescent : baseEnd_3219049 < baseStart_3219049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219050 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3219050 : Nat := 118140960795 + 3219050 * 2 ^ 59
def prefixEnd_3219050 : Nat := 4983230072969 + 3 ^ 40 * 3219050 * 2
def baseEnd_3219050 : Nat := 1652919900855735685770865

theorem tailTrace_3219050 : CollatzResearch.WordTrace tailWord_3219050 prefixEnd_3219050 1652919900855735685770865 := by
  unfold tailWord_3219050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352099746984773703921651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78272265991959396543791069 29352099746984773703921651)
  ·
    refine ⟨44028149620477160555882477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29352099746984773703921651 44028149620477160555882477)
    ·
      refine ⟨16510556107678935208455929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44028149620477160555882477 16510556107678935208455929)
      ·
        refine ⟨12382917080759201406341947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16510556107678935208455929 12382917080759201406341947)
        ·
          refine ⟨18574375621138802109512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12382917080759201406341947 18574375621138802109512921)
          ·
            refine ⟨13930781715854101582134691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18574375621138802109512921 13930781715854101582134691)
            ·
              refine ⟨20896172573781152373202037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13930781715854101582134691 20896172573781152373202037)
              ·
                refine ⟨1959016178791983034987691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20896172573781152373202037 1959016178791983034987691)
                ·
                  refine ⟨2938524268187974552481537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959016178791983034987691 2938524268187974552481537)
                  ·
                    refine ⟨2203893201140980914361153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938524268187974552481537 2203893201140980914361153)
                    ·
                      refine ⟨1652919900855735685770865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203893201140980914361153 1652919900855735685770865)
                      ·
                        rfl

theorem cell23_3219050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3219050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219050 prefixEnd_3219050 := by exact prefixLift 3219050
  have htrace : WordTrace (prefixWord ++ tailWord_3219050) baseStart_3219050 baseEnd_3219050 := by
    simpa [prefixWord, tailWord_3219050, baseEnd_3219050] using wordTrace_append hprefix tailTrace_3219050
  have hstable : (prefixWord ++ tailWord_3219050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219050).length < 2 ^ (prefixWord ++ tailWord_3219050).sum := by decide
  have hdescent : baseEnd_3219050 < baseStart_3219050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219053 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3219053 : Nat := 118140960795 + 3219053 * 2 ^ 59
def prefixEnd_3219053 : Nat := 4983230072969 + 3 ^ 40 * 3219053 * 2
def baseEnd_3219053 : Nat := 1652921441297699174033351

theorem tailTrace_3219053 : CollatzResearch.WordTrace tailWord_3219053 prefixEnd_3219053 1652921441297699174033351 := by
  unfold tailWord_3219053
  simp only [CollatzResearch.WordTrace]
  refine ⟨117408508406928226328045813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78272338937952150885363875 117408508406928226328045813)
  ·
    refine ⟨11007047663149521218254295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117408508406928226328045813 11007047663149521218254295)
    ·
      refine ⟨16510571494724281827381443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007047663149521218254295 16510571494724281827381443)
      ·
        refine ⟨24765857242086422741072165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510571494724281827381443 24765857242086422741072165)
        ·
          refine ⟨4643598232891204263951031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24765857242086422741072165 4643598232891204263951031)
          ·
            refine ⟨6965397349336806395926547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643598232891204263951031 6965397349336806395926547)
            ·
              refine ⟨10448096024005209593889821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965397349336806395926547 10448096024005209593889821)
              ·
                refine ⟨3918036009001953597708683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10448096024005209593889821 3918036009001953597708683)
                ·
                  refine ⟨5877054013502930396563025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918036009001953597708683 5877054013502930396563025)
                  ·
                    refine ⟨4407790510127197797422269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877054013502930396563025 4407790510127197797422269)
                    ·
                      refine ⟨1652921441297699174033351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407790510127197797422269 1652921441297699174033351)
                      ·
                        rfl

theorem cell23_3219053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3219053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219053 prefixEnd_3219053 := by exact prefixLift 3219053
  have htrace : WordTrace (prefixWord ++ tailWord_3219053) baseStart_3219053 baseEnd_3219053 := by
    simpa [prefixWord, tailWord_3219053, baseEnd_3219053] using wordTrace_append hprefix tailTrace_3219053
  have hstable : (prefixWord ++ tailWord_3219053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219053).length < 2 ^ (prefixWord ++ tailWord_3219053).sum := by decide
  have hdescent : baseEnd_3219053 < baseStart_3219053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219066 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_3219066 : Nat := 118140960795 + 3219066 * 2 ^ 59
def prefixEnd_3219066 : Nat := 4983230072969 + 3 ^ 40 * 3219066 * 2
def baseEnd_3219066 : Nat := 1652928116546207623170791

theorem tailTrace_3219066 : CollatzResearch.WordTrace tailWord_3219066 prefixEnd_3219066 1652928116546207623170791 := by
  unfold tailWord_3219066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352245638970282387067263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78272655037254086365512701 29352245638970282387067263)
  ·
    refine ⟨44028368458455423580600895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29352245638970282387067263 44028368458455423580600895)
    ·
      refine ⟨66042552687683135370901343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44028368458455423580600895 66042552687683135370901343)
      ·
        refine ⟨99063829031524703056352015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66042552687683135370901343 99063829031524703056352015)
        ·
          refine ⟨148595743547287054584528023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99063829031524703056352015 148595743547287054584528023)
          ·
            refine ⟨222893615320930581876792035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148595743547287054584528023 222893615320930581876792035)
            ·
              refine ⟨334340422981395872815188053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222893615320930581876792035 334340422981395872815188053)
              ·
                refine ⟨3918051831813232884552985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 334340422981395872815188053 3918051831813232884552985)
                ·
                  refine ⟨2938538873859924663414739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918051831813232884552985 2938538873859924663414739)
                  ·
                    refine ⟨4407808310789886995122109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938538873859924663414739 4407808310789886995122109)
                    ·
                      refine ⟨1652928116546207623170791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407808310789886995122109 1652928116546207623170791)
                      ·
                        rfl

theorem cell23_3219066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_3219066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219066 prefixEnd_3219066 := by exact prefixLift 3219066
  have htrace : WordTrace (prefixWord ++ tailWord_3219066) baseStart_3219066 baseEnd_3219066 := by
    simpa [prefixWord, tailWord_3219066, baseEnd_3219066] using wordTrace_append hprefix tailTrace_3219066
  have hstable : (prefixWord ++ tailWord_3219066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219066).length < 2 ^ (prefixWord ++ tailWord_3219066).sum := by decide
  have hdescent : baseEnd_3219066 < baseStart_3219066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219080 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3219080 : Nat := 118140960795 + 3219080 * 2 ^ 59
def prefixEnd_3219080 : Nat := 4983230072969 + 3 ^ 40 * 3219080 * 2
def baseEnd_3219080 : Nat := 1652935305275370568395727

theorem tailTrace_3219080 : CollatzResearch.WordTrace tailWord_3219080 prefixEnd_3219080 1652935305275370568395727 := by
  unfold tailWord_3219080
  simp only [CollatzResearch.WordTrace]
  refine ⟨58704746588915204969639347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78272995451886939959519129 58704746588915204969639347)
  ·
    refine ⟨88057119883372807454459021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58704746588915204969639347 88057119883372807454459021)
    ·
      refine ⟨33021419956264802795422133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88057119883372807454459021 33021419956264802795422133)
      ·
        refine ⟨3095758120899825262070825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33021419956264802795422133 3095758120899825262070825)
        ·
          refine ⟨2321818590674868946553119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095758120899825262070825 2321818590674868946553119)
          ·
            refine ⟨3482727886012303419829679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321818590674868946553119 3482727886012303419829679)
            ·
              refine ⟨5224091829018455129744519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482727886012303419829679 5224091829018455129744519)
              ·
                refine ⟨7836137743527682694616779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224091829018455129744519 7836137743527682694616779)
                ·
                  refine ⟨11754206615291524041925169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836137743527682694616779 11754206615291524041925169)
                  ·
                    refine ⟨8815654961468643031443877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11754206615291524041925169 8815654961468643031443877)
                    ·
                      refine ⟨1652935305275370568395727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8815654961468643031443877 1652935305275370568395727)
                      ·
                        rfl

theorem cell23_3219080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3219080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219080 prefixEnd_3219080 := by exact prefixLift 3219080
  have htrace : WordTrace (prefixWord ++ tailWord_3219080) baseStart_3219080 baseEnd_3219080 := by
    simpa [prefixWord, tailWord_3219080, baseEnd_3219080] using wordTrace_append hprefix tailTrace_3219080
  have hstable : (prefixWord ++ tailWord_3219080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219080).length < 2 ^ (prefixWord ++ tailWord_3219080).sum := by decide
  have hdescent : baseEnd_3219080 < baseStart_3219080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219083 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 2, 1, 3]
def baseStart_3219083 : Nat := 118140960795 + 3219083 * 2 ^ 59
def prefixEnd_3219083 : Nat := 4983230072969 + 3 ^ 40 * 3219083 * 2
def baseEnd_3219083 : Nat := 1652936845717334056658213

theorem tailTrace_3219083 : CollatzResearch.WordTrace tailWord_3219083 prefixEnd_3219083 1652936845717334056658213 := by
  unfold tailWord_3219083
  simp only [CollatzResearch.WordTrace]
  refine ⟨117409602596819541451637903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78273068397879694301091935 117409602596819541451637903)
  ·
    refine ⟨176114403895229312177456855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117409602596819541451637903 176114403895229312177456855)
    ·
      refine ⟨264171605842843968266185283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176114403895229312177456855 264171605842843968266185283)
      ·
        refine ⟨396257408764265952399277925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264171605842843968266185283 396257408764265952399277925)
        ·
          refine ⟨74298264143299866074864611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 396257408764265952399277925 74298264143299866074864611)
          ·
            refine ⟨111447396214949799112296917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74298264143299866074864611 111447396214949799112296917)
            ·
              refine ⟨2612048348787885916694459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111447396214949799112296917 2612048348787885916694459)
              ·
                refine ⟨3918072523181828875041689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612048348787885916694459 3918072523181828875041689)
                ·
                  refine ⟨2938554392386371656281267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918072523181828875041689 2938554392386371656281267)
                  ·
                    refine ⟨4407831588579557484421901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938554392386371656281267 4407831588579557484421901)
                    ·
                      refine ⟨1652936845717334056658213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4407831588579557484421901 1652936845717334056658213)
                      ·
                        rfl

theorem cell23_3219083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 1, 3].length) (baseStart_3219083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219083 prefixEnd_3219083 := by exact prefixLift 3219083
  have htrace : WordTrace (prefixWord ++ tailWord_3219083) baseStart_3219083 baseEnd_3219083 := by
    simpa [prefixWord, tailWord_3219083, baseEnd_3219083] using wordTrace_append hprefix tailTrace_3219083
  have hstable : (prefixWord ++ tailWord_3219083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219083).length < 2 ^ (prefixWord ++ tailWord_3219083).sum := by decide
  have hdescent : baseEnd_3219083 < baseStart_3219083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219123 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 2, 2, 2]
def baseStart_3219123 : Nat := 118140960795 + 3219123 * 2 ^ 59
def prefixEnd_3219123 : Nat := 4983230072969 + 3 ^ 40 * 3219123 * 2
def baseEnd_3219123 : Nat := 1652957384943513900158029

theorem tailTrace_3219123 : CollatzResearch.WordTrace tailWord_3219123 prefixEnd_3219123 1652957384943513900158029 := by
  unfold tailWord_3219123
  simp only [CollatzResearch.WordTrace]
  refine ⟨117411061516674628283094023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78274041011116418855396015 117411061516674628283094023)
  ·
    refine ⟨176116592275011942424641035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117411061516674628283094023 176116592275011942424641035)
    ·
      refine ⟨264174888412517913636961553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176116592275011942424641035 264174888412517913636961553)
      ·
        refine ⟨198131166309388435227721165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264174888412517913636961553 198131166309388435227721165)
        ·
          refine ⟨74299187366020663210395437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198131166309388435227721165 74299187366020663210395437)
          ·
            refine ⟨27862195262257748703898289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74299187366020663210395437 27862195262257748703898289)
            ·
              refine ⟨20896646446693311527923717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27862195262257748703898289 20896646446693311527923717)
              ·
                refine ⟨3918121208754995911485697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20896646446693311527923717 3918121208754995911485697)
                ·
                  refine ⟨2938590906566246933614273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918121208754995911485697 2938590906566246933614273)
                  ·
                    refine ⟨2203943179924685200210705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938590906566246933614273 2203943179924685200210705)
                    ·
                      refine ⟨1652957384943513900158029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203943179924685200210705 1652957384943513900158029)
                      ·
                        rfl

theorem cell23_3219123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2, 2].length) (baseStart_3219123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219123 prefixEnd_3219123 := by exact prefixLift 3219123
  have htrace : WordTrace (prefixWord ++ tailWord_3219123) baseStart_3219123 baseEnd_3219123 := by
    simpa [prefixWord, tailWord_3219123, baseEnd_3219123] using wordTrace_append hprefix tailTrace_3219123
  have hstable : (prefixWord ++ tailWord_3219123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219123).length < 2 ^ (prefixWord ++ tailWord_3219123).sum := by decide
  have hdescent : baseEnd_3219123 < baseStart_3219123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219129 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 7]
def baseStart_3219129 : Nat := 118140960795 + 3219129 * 2 ^ 59
def prefixEnd_3219129 : Nat := 4983230072969 + 3 ^ 40 * 3219129 * 2
def baseEnd_3219129 : Nat := 183662273980826764075889

theorem tailTrace_3219129 : CollatzResearch.WordTrace tailWord_3219129 prefixEnd_3219129 183662273980826764075889 := by
  unfold tailWord_3219129
  simp only [CollatzResearch.WordTrace]
  refine ⟨117411280354652891307812441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78274186903101927538541627 117411280354652891307812441)
  ·
    refine ⟨88058460265989668480859331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117411280354652891307812441 88058460265989668480859331)
    ·
      refine ⟨132087690398984502721288997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88058460265989668480859331 132087690398984502721288997)
      ·
        refine ⟨24766441949809594260241687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132087690398984502721288997 24766441949809594260241687)
        ·
          refine ⟨37149662924714391390362531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24766441949809594260241687 37149662924714391390362531)
          ·
            refine ⟨55724494387071587085543797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37149662924714391390362531 55724494387071587085543797)
            ·
              refine ⟨5224171348787961289269731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55724494387071587085543797 5224171348787961289269731)
              ·
                refine ⟨7836257023181941933904597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224171348787961289269731 7836257023181941933904597)
                ·
                  refine ⟨183662273980826764075889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7836257023181941933904597 183662273980826764075889)
                  ·
                    rfl

theorem cell23_3219129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_3219129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219129 prefixEnd_3219129 := by exact prefixLift 3219129
  have htrace : WordTrace (prefixWord ++ tailWord_3219129) baseStart_3219129 baseEnd_3219129 := by
    simpa [prefixWord, tailWord_3219129, baseEnd_3219129] using wordTrace_append hprefix tailTrace_3219129
  have hstable : (prefixWord ++ tailWord_3219129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219129).length < 2 ^ (prefixWord ++ tailWord_3219129).sum := by decide
  have hdescent : baseEnd_3219129 < baseStart_3219129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219140 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3219140 : Nat := 118140960795 + 3219140 * 2 ^ 59
def prefixEnd_3219140 : Nat := 4983230072969 + 3 ^ 40 * 3219140 * 2
def baseEnd_3219140 : Nat := 1652966114114640333645451

theorem tailTrace_3219140 : CollatzResearch.WordTrace tailWord_3219140 prefixEnd_3219140 1652966114114640333645451 := by
  unfold tailWord_3219140
  simp only [CollatzResearch.WordTrace]
  refine ⟨58705840778806520093231437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78274454371742026790975249 58705840778806520093231437)
  ·
    refine ⟨22014690292052445034961789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58705840778806520093231437 22014690292052445034961789)
    ·
      refine ⟨8255508859519666888110671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22014690292052445034961789 8255508859519666888110671)
      ·
        refine ⟨12383263289279500332166007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255508859519666888110671 12383263289279500332166007)
        ·
          refine ⟨18574894933919250498249011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383263289279500332166007 18574894933919250498249011)
          ·
            refine ⟨27862342400878875747373517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18574894933919250498249011 27862342400878875747373517)
            ·
              refine ⟨10448378400329578405265069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27862342400878875747373517 10448378400329578405265069)
              ·
                refine ⟨3918141900123591901974401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10448378400329578405265069 3918141900123591901974401)
                ·
                  refine ⟨2938606425092693926480801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918141900123591901974401 2938606425092693926480801)
                  ·
                    refine ⟨2203954818819520444860601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938606425092693926480801 2203954818819520444860601)
                    ·
                      refine ⟨1652966114114640333645451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2203954818819520444860601 1652966114114640333645451)
                      ·
                        rfl

theorem cell23_3219140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3219140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219140 prefixEnd_3219140 := by exact prefixLift 3219140
  have htrace : WordTrace (prefixWord ++ tailWord_3219140) baseStart_3219140 baseEnd_3219140 := by
    simpa [prefixWord, tailWord_3219140, baseEnd_3219140] using wordTrace_append hprefix tailTrace_3219140
  have hstable : (prefixWord ++ tailWord_3219140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219140).length < 2 ^ (prefixWord ++ tailWord_3219140).sum := by decide
  have hdescent : baseEnd_3219140 < baseStart_3219140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219176 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3219176 : Nat := 118140960795 + 3219176 * 2 ^ 59
def prefixEnd_3219176 : Nat := 4983230072969 + 3 ^ 40 * 3219176 * 2
def baseEnd_3219176 : Nat := 550994866472734064265095

theorem tailTrace_3219176 : CollatzResearch.WordTrace tailWord_3219176 prefixEnd_3219176 550994866472734064265095 := by
  unfold tailWord_3219176
  simp only [CollatzResearch.WordTrace]
  refine ⟨58706497292741309167386691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78275329723655078889848921 58706497292741309167386691)
  ·
    refine ⟨88059745939111963751080037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58706497292741309167386691 88059745939111963751080037)
    ·
      refine ⟨16511202363583493203327507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88059745939111963751080037 16511202363583493203327507)
      ·
        refine ⟨24766803545375239804991261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16511202363583493203327507 24766803545375239804991261)
        ·
          refine ⟨9287551329515714926871723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24766803545375239804991261 9287551329515714926871723)
          ·
            refine ⟨13931326994273572390307585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287551329515714926871723 13931326994273572390307585)
            ·
              refine ⟨10448495245705179292730689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13931326994273572390307585 10448495245705179292730689)
              ·
                refine ⟨7836371434278884469548017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10448495245705179292730689 7836371434278884469548017)
                ·
                  refine ⟨5877278575709163352161013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836371434278884469548017 5877278575709163352161013)
                  ·
                    refine ⟨550994866472734064265095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5877278575709163352161013 550994866472734064265095)
                    ·
                      rfl

theorem cell23_3219176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3219176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219176 prefixEnd_3219176 := by exact prefixLift 3219176
  have htrace : WordTrace (prefixWord ++ tailWord_3219176) baseStart_3219176 baseEnd_3219176 := by
    simpa [prefixWord, tailWord_3219176, baseEnd_3219176] using wordTrace_append hprefix tailTrace_3219176
  have hstable : (prefixWord ++ tailWord_3219176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219176).length < 2 ^ (prefixWord ++ tailWord_3219176).sum := by decide
  have hdescent : baseEnd_3219176 < baseStart_3219176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219236 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 8]
def baseStart_3219236 : Nat := 118140960795 + 3219236 * 2 ^ 59
def prefixEnd_3219236 : Nat := 4983230072969 + 3 ^ 40 * 3219236 * 2
def baseEnd_3219236 : Nat := 183668378695274662005001

theorem tailTrace_3219236 : CollatzResearch.WordTrace tailWord_3219236 prefixEnd_3219236 183668378695274662005001 := by
  unfold tailWord_3219236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707591482632624290978781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78276788643510165721305041 58707591482632624290978781)
  ·
    refine ⟨22015346805987234109117043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58707591482632624290978781 22015346805987234109117043)
    ·
      refine ⟨33023020208980851163675565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22015346805987234109117043 33023020208980851163675565)
      ·
        refine ⟨12383632578367819186378337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33023020208980851163675565 12383632578367819186378337)
        ·
          refine ⟨9287724433775864389783753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12383632578367819186378337 9287724433775864389783753)
          ·
            refine ⟨6965793325331898292337815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9287724433775864389783753 6965793325331898292337815)
            ·
              refine ⟨10448689987997847438506723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965793325331898292337815 10448689987997847438506723)
              ·
                refine ⟨15673034981996771157760085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448689987997847438506723 15673034981996771157760085)
                ·
                  refine ⟨183668378695274662005001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15673034981996771157760085 183668378695274662005001)
                  ·
                    rfl

theorem cell23_3219236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_3219236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219236 prefixEnd_3219236 := by exact prefixLift 3219236
  have htrace : WordTrace (prefixWord ++ tailWord_3219236) baseStart_3219236 baseEnd_3219236 := by
    simpa [prefixWord, tailWord_3219236, baseEnd_3219236] using wordTrace_append hprefix tailTrace_3219236
  have hstable : (prefixWord ++ tailWord_3219236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219236).length < 2 ^ (prefixWord ++ tailWord_3219236).sum := by decide
  have hdescent : baseEnd_3219236 < baseStart_3219236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219240 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3219240 : Nat := 118140960795 + 3219240 * 2 ^ 59
def prefixEnd_3219240 : Nat := 4983230072969 + 3 ^ 40 * 3219240 * 2
def baseEnd_3219240 : Nat := 551005820726696647464997

theorem tailTrace_3219240 : CollatzResearch.WordTrace tailWord_3219240 prefixEnd_3219240 551005820726696647464997 := by
  unfold tailWord_3219240
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707664428625378632551587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78276885904833838176735449 58707664428625378632551587)
  ·
    refine ⟨88061496642938067948827381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58707664428625378632551587 88061496642938067948827381)
    ·
      refine ⟨8255765310275443870202567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88061496642938067948827381 8255765310275443870202567)
      ·
        refine ⟨12383647965413165805303851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255765310275443870202567 12383647965413165805303851)
        ·
          refine ⟨18575471948119748707955777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383647965413165805303851 18575471948119748707955777)
          ·
            refine ⟨13931603961089811530966833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18575471948119748707955777 13931603961089811530966833)
            ·
              refine ⟨10448702970817358648225125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13931603961089811530966833 10448702970817358648225125)
              ·
                refine ⟨1959131807028254746542211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10448702970817358648225125 1959131807028254746542211)
                ·
                  refine ⟨2938697710542382119813317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959131807028254746542211 2938697710542382119813317)
                  ·
                    refine ⟨551005820726696647464997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938697710542382119813317 551005820726696647464997)
                    ·
                      rfl

theorem cell23_3219240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3219240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219240 prefixEnd_3219240 := by exact prefixLift 3219240
  have htrace : WordTrace (prefixWord ++ tailWord_3219240) baseStart_3219240 baseEnd_3219240 := by
    simpa [prefixWord, tailWord_3219240, baseEnd_3219240] using wordTrace_append hprefix tailTrace_3219240
  have hstable : (prefixWord ++ tailWord_3219240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219240).length < 2 ^ (prefixWord ++ tailWord_3219240).sum := by decide
  have hdescent : baseEnd_3219240 < baseStart_3219240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219273 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 2, 3, 2]
def baseStart_3219273 : Nat := 118140960795 + 3219273 * 2 ^ 59
def prefixEnd_3219273 : Nat := 4983230072969 + 3 ^ 40 * 3219273 * 2
def baseEnd_3219273 : Nat := 1653034407041688313282339

theorem tailTrace_3219273 : CollatzResearch.WordTrace tailWord_3219273 prefixEnd_3219273 1653034407041688313282339 := by
  unfold tailWord_3219273
  simp only [CollatzResearch.WordTrace]
  refine ⟨117416532466131203901054473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78277688310754135934036315 117416532466131203901054473)
  ·
    refine ⟨88062399349598402925790855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117416532466131203901054473 88062399349598402925790855)
    ·
      refine ⟨132093599024397604388686283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88062399349598402925790855 132093599024397604388686283)
      ·
        refine ⟨198140398536596406583029425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132093599024397604388686283 198140398536596406583029425)
        ·
          refine ⟨148605298902447304937272069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198140398536596406583029425 148605298902447304937272069)
          ·
            refine ⟨27863493544208869675738513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148605298902447304937272069 27863493544208869675738513)
            ·
              refine ⟨20897620158156652256803885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27863493544208869675738513 20897620158156652256803885)
              ·
                refine ⟨7836607559308744596301457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20897620158156652256803885 7836607559308744596301457)
                ·
                  refine ⟨5877455669481558447226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836607559308744596301457 5877455669481558447226093)
                  ·
                    refine ⟨2204045876055584417709785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5877455669481558447226093 2204045876055584417709785)
                    ·
                      refine ⟨1653034407041688313282339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204045876055584417709785 1653034407041688313282339)
                      ·
                        rfl

theorem cell23_3219273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 3, 2].length) (baseStart_3219273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219273 prefixEnd_3219273 := by exact prefixLift 3219273
  have htrace : WordTrace (prefixWord ++ tailWord_3219273) baseStart_3219273 baseEnd_3219273 := by
    simpa [prefixWord, tailWord_3219273, baseEnd_3219273] using wordTrace_append hprefix tailTrace_3219273
  have hstable : (prefixWord ++ tailWord_3219273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219273).length < 2 ^ (prefixWord ++ tailWord_3219273).sum := by decide
  have hdescent : baseEnd_3219273 < baseStart_3219273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219297 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_3219297 : Nat := 118140960795 + 3219297 * 2 ^ 59
def prefixEnd_3219297 : Nat := 4983230072969 + 3 ^ 40 * 3219297 * 2
def baseEnd_3219297 : Nat := 1653046730577396219382229

theorem tailTrace_3219297 : CollatzResearch.WordTrace tailWord_3219297 prefixEnd_3219297 1653046730577396219382229 := by
  unfold tailWord_3219297
  simp only [CollatzResearch.WordTrace]
  refine ⟨117417407818044255999928145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78278271878696170666618763 117417407818044255999928145)
  ·
    refine ⟨88063055863533191999946109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117417407818044255999928145 88063055863533191999946109)
    ·
      refine ⟨33023645948824946999979791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88063055863533191999946109 33023645948824946999979791)
      ·
        refine ⟨49535468923237420499969687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33023645948824946999979791 49535468923237420499969687)
        ·
          refine ⟨74303203384856130749954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49535468923237420499969687 74303203384856130749954531)
          ·
            refine ⟨111454805077284196124931797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74303203384856130749954531 111454805077284196124931797)
            ·
              refine ⟨2612221993998848346678089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111454805077284196124931797 2612221993998848346678089)
              ·
                refine ⟨1959166495499136260008567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612221993998848346678089 1959166495499136260008567)
                ·
                  refine ⟨2938749743248704390012851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959166495499136260008567 2938749743248704390012851)
                  ·
                    refine ⟨4408124614873056585019277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938749743248704390012851 4408124614873056585019277)
                    ·
                      refine ⟨1653046730577396219382229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408124614873056585019277 1653046730577396219382229)
                      ·
                        rfl

theorem cell23_3219297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_3219297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219297 prefixEnd_3219297 := by exact prefixLift 3219297
  have htrace : WordTrace (prefixWord ++ tailWord_3219297) baseStart_3219297 baseEnd_3219297 := by
    simpa [prefixWord, tailWord_3219297, baseEnd_3219297] using wordTrace_append hprefix tailTrace_3219297
  have hstable : (prefixWord ++ tailWord_3219297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219297).length < 2 ^ (prefixWord ++ tailWord_3219297).sum := by decide
  have hdescent : baseEnd_3219297 < baseStart_3219297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219313 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_3219313 : Nat := 118140960795 + 3219313 * 2 ^ 59
def prefixEnd_3219313 : Nat := 4983230072969 + 3 ^ 40 * 3219313 * 2
def baseEnd_3219313 : Nat := 551018315422622718927385

theorem tailTrace_3219313 : CollatzResearch.WordTrace tailWord_3219313 prefixEnd_3219313 551018315422622718927385 := by
  unfold tailWord_3219313
  simp only [CollatzResearch.WordTrace]
  refine ⟨117417991385986290732510593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78278660923990860488340395 117417991385986290732510593)
  ·
    refine ⟨88063493539489718049382945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117417991385986290732510593 88063493539489718049382945)
    ·
      refine ⟨66047620154617288537037209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88063493539489718049382945 66047620154617288537037209)
      ·
        refine ⟨49535715115962966402777907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66047620154617288537037209 49535715115962966402777907)
        ·
          refine ⟨74303572673944449604166861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49535715115962966402777907 74303572673944449604166861)
          ·
            refine ⟨27863839752729168601562573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74303572673944449604166861 27863839752729168601562573)
            ·
              refine ⟨10448939907273438225585965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27863839752729168601562573 10448939907273438225585965)
              ·
                refine ⟨3918352465227539334594737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10448939907273438225585965 3918352465227539334594737)
                ·
                  refine ⟨2938764348920654500946053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918352465227539334594737 2938764348920654500946053)
                  ·
                    refine ⟨551018315422622718927385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938764348920654500946053 551018315422622718927385)
                    ·
                      rfl

theorem cell23_3219313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_3219313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219313 prefixEnd_3219313 := by exact prefixLift 3219313
  have htrace : WordTrace (prefixWord ++ tailWord_3219313) baseStart_3219313 baseEnd_3219313 := by
    simpa [prefixWord, tailWord_3219313, baseEnd_3219313] using wordTrace_append hprefix tailTrace_3219313
  have hstable : (prefixWord ++ tailWord_3219313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219313).length < 2 ^ (prefixWord ++ tailWord_3219313).sum := by decide
  have hdescent : baseEnd_3219313 < baseStart_3219313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219337 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 1, 2, 2]
def baseStart_3219337 : Nat := 118140960795 + 3219337 * 2 ^ 59
def prefixEnd_3219337 : Nat := 4983230072969 + 3 ^ 40 * 3219337 * 2
def baseEnd_3219337 : Nat := 1653067269803576062882045

theorem tailTrace_3219337 : CollatzResearch.WordTrace tailWord_3219337 prefixEnd_3219337 1653067269803576062882045 := by
  unfold tailWord_3219337
  simp only [CollatzResearch.WordTrace]
  refine ⟨117418866737899342831384265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78279244491932895220922843 117418866737899342831384265)
  ·
    refine ⟨88064150053424507123538199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117418866737899342831384265 88064150053424507123538199)
    ·
      refine ⟨132096225080136760685307299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88064150053424507123538199 132096225080136760685307299)
      ·
        refine ⟨198144337620205141027960949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132096225080136760685307299 198144337620205141027960949)
        ·
          refine ⟨18576031651894231971371339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198144337620205141027960949 18576031651894231971371339)
          ·
            refine ⟨27864047477841347957057009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18576031651894231971371339 27864047477841347957057009)
            ·
              refine ⟨20898035608381010967792757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27864047477841347957057009 20898035608381010967792757)
              ·
                refine ⟨1959190838285719778230571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20898035608381010967792757 1959190838285719778230571)
                ·
                  refine ⟨2938786257428579667345857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959190838285719778230571 2938786257428579667345857)
                  ·
                    refine ⟨2204089693071434750509393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938786257428579667345857 2204089693071434750509393)
                    ·
                      refine ⟨1653067269803576062882045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204089693071434750509393 1653067269803576062882045)
                      ·
                        rfl

theorem cell23_3219337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 2, 2].length) (baseStart_3219337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219337 prefixEnd_3219337 := by exact prefixLift 3219337
  have htrace : WordTrace (prefixWord ++ tailWord_3219337) baseStart_3219337 baseEnd_3219337 := by
    simpa [prefixWord, tailWord_3219337, baseEnd_3219337] using wordTrace_append hprefix tailTrace_3219337
  have hstable : (prefixWord ++ tailWord_3219337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219337).length < 2 ^ (prefixWord ++ tailWord_3219337).sum := by decide
  have hdescent : baseEnd_3219337 < baseStart_3219337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219353 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_3219353 : Nat := 118140960795 + 3219353 * 2 ^ 59
def prefixEnd_3219353 : Nat := 4983230072969 + 3 ^ 40 * 3219353 * 2
def baseEnd_3219353 : Nat := 1653075485494048000281971

theorem tailTrace_3219353 : CollatzResearch.WordTrace tailWord_3219353 prefixEnd_3219353 1653075485494048000281971 := by
  unfold tailWord_3219353
  simp only [CollatzResearch.WordTrace]
  refine ⟨117419450305841377563966713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78279633537227585042644475 117419450305841377563966713)
  ·
    refine ⟨88064587729381033172975035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117419450305841377563966713 88064587729381033172975035)
    ·
      refine ⟨132096881594071549759462553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88064587729381033172975035 132096881594071549759462553)
      ·
        refine ⟨99072661195553662319596915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132096881594071549759462553 99072661195553662319596915)
        ·
          refine ⟨148608991793330493479395373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99072661195553662319596915 148608991793330493479395373)
          ·
            refine ⟨55728371922498935054773265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148608991793330493479395373 55728371922498935054773265)
            ·
              refine ⟨41796278941874201291079949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55728371922498935054773265 41796278941874201291079949)
              ·
                refine ⟨15673604603202825484154981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41796278941874201291079949 15673604603202825484154981)
                ·
                  refine ⟨2938800863100529778279059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15673604603202825484154981 2938800863100529778279059)
                  ·
                    refine ⟨4408201294650794667418589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938800863100529778279059 4408201294650794667418589)
                    ·
                      refine ⟨1653075485494048000281971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408201294650794667418589 1653075485494048000281971)
                      ·
                        rfl

theorem cell23_3219353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_3219353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219353 prefixEnd_3219353 := by exact prefixLift 3219353
  have htrace : WordTrace (prefixWord ++ tailWord_3219353) baseStart_3219353 baseEnd_3219353 := by
    simpa [prefixWord, tailWord_3219353, baseEnd_3219353] using wordTrace_append hprefix tailTrace_3219353
  have hstable : (prefixWord ++ tailWord_3219353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219353).length < 2 ^ (prefixWord ++ tailWord_3219353).sum := by decide
  have hdescent : baseEnd_3219353 < baseStart_3219353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219354 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3219354 : Nat := 118140960795 + 3219354 * 2 ^ 59
def prefixEnd_3219354 : Nat := 4983230072969 + 3 ^ 40 * 3219354 * 2
def baseEnd_3219354 : Nat := 1653075998974702496369467

theorem tailTrace_3219354 : CollatzResearch.WordTrace tailWord_3219354 prefixEnd_3219354 1653075998974702496369467 := by
  unfold tailWord_3219354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354871694709438683688279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78279657852558503156502077 29354871694709438683688279)
  ·
    refine ⟨44032307542064158025532419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29354871694709438683688279 44032307542064158025532419)
    ·
      refine ⟨66048461313096237038298629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44032307542064158025532419 66048461313096237038298629)
      ·
        refine ⟨12384086496205544444680993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66048461313096237038298629 12384086496205544444680993)
        ·
          refine ⟨9288064872154158333510745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12384086496205544444680993 9288064872154158333510745)
          ·
            refine ⟨6966048654115618750133059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9288064872154158333510745 6966048654115618750133059)
            ·
              refine ⟨10449072981173428125199589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966048654115618750133059 10449072981173428125199589)
              ·
                refine ⟨1959201183970017773474923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10449072981173428125199589 1959201183970017773474923)
                ·
                  refine ⟨2938801775955026660212385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959201183970017773474923 2938801775955026660212385)
                  ·
                    refine ⟨2204101331966269995159289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938801775955026660212385 2204101331966269995159289)
                    ·
                      refine ⟨1653075998974702496369467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204101331966269995159289 1653075998974702496369467)
                      ·
                        rfl

theorem cell23_3219354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3219354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219354 prefixEnd_3219354 := by exact prefixLift 3219354
  have htrace : WordTrace (prefixWord ++ tailWord_3219354) baseStart_3219354 baseEnd_3219354 := by
    simpa [prefixWord, tailWord_3219354, baseEnd_3219354] using wordTrace_append hprefix tailTrace_3219354
  have hstable : (prefixWord ++ tailWord_3219354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219354).length < 2 ^ (prefixWord ++ tailWord_3219354).sum := by decide
  have hdescent : baseEnd_3219354 < baseStart_3219354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219423 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3219423 : Nat := 118140960795 + 3219423 * 2 ^ 59
def prefixEnd_3219423 : Nat := 4983230072969 + 3 ^ 40 * 3219423 * 2
def baseEnd_3219423 : Nat := 1653111429139862726406649

theorem tailTrace_3219423 : CollatzResearch.WordTrace tailWord_3219423 prefixEnd_3219423 1653111429139862726406649 := by
  unfold tailWord_3219423
  simp only [CollatzResearch.WordTrace]
  refine ⟨117422003415587779519014923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78281335610391853012676615 117422003415587779519014923)
  ·
    refine ⟨176133005123381669278522385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117422003415587779519014923 176133005123381669278522385)
    ·
      refine ⟨132099753842536251958891789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176133005123381669278522385 132099753842536251958891789)
      ·
        refine ⟨49537407690951094484584421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132099753842536251958891789 49537407690951094484584421)
        ·
          refine ⟨9288263942053330215859579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49537407690951094484584421 9288263942053330215859579)
          ·
            refine ⟨13932395913079995323789369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288263942053330215859579 13932395913079995323789369)
            ·
              refine ⟨10449296934809996492842027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13932395913079995323789369 10449296934809996492842027)
              ·
                refine ⟨15673945402214994739263041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449296934809996492842027 15673945402214994739263041)
                ·
                  refine ⟨11755459051661246054447281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15673945402214994739263041 11755459051661246054447281)
                  ·
                    refine ⟨8816594288745934540835461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11755459051661246054447281 8816594288745934540835461)
                    ·
                      refine ⟨1653111429139862726406649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8816594288745934540835461 1653111429139862726406649)
                      ·
                        rfl

theorem cell23_3219423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3219423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219423 prefixEnd_3219423 := by exact prefixLift 3219423
  have htrace : WordTrace (prefixWord ++ tailWord_3219423) baseStart_3219423 baseEnd_3219423 := by
    simpa [prefixWord, tailWord_3219423, baseEnd_3219423] using wordTrace_append hprefix tailTrace_3219423
  have hstable : (prefixWord ++ tailWord_3219423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219423).length < 2 ^ (prefixWord ++ tailWord_3219423).sum := by decide
  have hdescent : baseEnd_3219423 < baseStart_3219423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219427 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3219427 : Nat := 118140960795 + 3219427 * 2 ^ 59
def prefixEnd_3219427 : Nat := 4983230072969 + 3 ^ 40 * 3219427 * 2
def baseEnd_3219427 : Nat := 1653113483062480710756631

theorem tailTrace_3219427 : CollatzResearch.WordTrace tailWord_3219427 prefixEnd_3219427 1653113483062480710756631 := by
  unfold tailWord_3219427
  simp only [CollatzResearch.WordTrace]
  refine ⟨117422149307573288202160535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78281432871715525468107023 117422149307573288202160535)
  ·
    refine ⟨176133223961359932303240803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117422149307573288202160535 176133223961359932303240803)
    ·
      refine ⟨264199835942039898454861205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176133223961359932303240803 264199835942039898454861205)
      ·
        refine ⟨12384367309783120240071619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 264199835942039898454861205 12384367309783120240071619)
        ·
          refine ⟨18576550964674680360107429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12384367309783120240071619 18576550964674680360107429)
          ·
            refine ⟨3483103305876502567520143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18576550964674680360107429 3483103305876502567520143)
            ·
              refine ⟨5224654958814753851280215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483103305876502567520143 5224654958814753851280215)
              ·
                refine ⟨7836982438222130776920323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224654958814753851280215 7836982438222130776920323)
                ·
                  refine ⟨11755473657333196165380485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836982438222130776920323 11755473657333196165380485)
                  ·
                    refine ⟨2204151310749974281008841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11755473657333196165380485 2204151310749974281008841)
                    ·
                      refine ⟨1653113483062480710756631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204151310749974281008841 1653113483062480710756631)
                      ·
                        rfl

theorem cell23_3219427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3219427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219427 prefixEnd_3219427 := by exact prefixLift 3219427
  have htrace : WordTrace (prefixWord ++ tailWord_3219427) baseStart_3219427 baseEnd_3219427 := by
    simpa [prefixWord, tailWord_3219427, baseEnd_3219427] using wordTrace_append hprefix tailTrace_3219427
  have hstable : (prefixWord ++ tailWord_3219427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219427).length < 2 ^ (prefixWord ++ tailWord_3219427).sum := by decide
  have hdescent : baseEnd_3219427 < baseStart_3219427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219463 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3219463 : Nat := 118140960795 + 3219463 * 2 ^ 59
def prefixEnd_3219463 : Nat := 4983230072969 + 3 ^ 40 * 3219463 * 2
def baseEnd_3219463 : Nat := 551043989455347523302155

theorem tailTrace_3219463 : CollatzResearch.WordTrace tailWord_3219463 prefixEnd_3219463 551043989455347523302155 := by
  unfold tailWord_3219463
  simp only [CollatzResearch.WordTrace]
  refine ⟨117423462335442866350471043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78282308223628577566980695 117423462335442866350471043)
  ·
    refine ⟨176135193503164299525706565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117423462335442866350471043 176135193503164299525706565)
    ·
      refine ⟨33025348781843306161069981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176135193503164299525706565 33025348781843306161069981)
      ·
        refine ⟨12384505793191239810401243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33025348781843306161069981 12384505793191239810401243)
        ·
          refine ⟨18576758689786859715601865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12384505793191239810401243 18576758689786859715601865)
          ·
            refine ⟨13932569017340144786701399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18576758689786859715601865 13932569017340144786701399)
            ·
              refine ⟨20898853526010217180052099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13932569017340144786701399 20898853526010217180052099)
              ·
                refine ⟨31348280289015325770078149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20898853526010217180052099 31348280289015325770078149)
                ·
                  refine ⟨5877802554190373581889653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31348280289015325770078149 5877802554190373581889653)
                  ·
                    refine ⟨551043989455347523302155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5877802554190373581889653 551043989455347523302155)
                    ·
                      rfl

theorem cell23_3219463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3219463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219463 prefixEnd_3219463 := by exact prefixLift 3219463
  have htrace : WordTrace (prefixWord ++ tailWord_3219463) baseStart_3219463 baseEnd_3219463 := by
    simpa [prefixWord, tailWord_3219463, baseEnd_3219463] using wordTrace_append hprefix tailTrace_3219463
  have hstable : (prefixWord ++ tailWord_3219463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219463).length < 2 ^ (prefixWord ++ tailWord_3219463).sum := by decide
  have hdescent : baseEnd_3219463 < baseStart_3219463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219470 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3219470 : Nat := 118140960795 + 3219470 * 2 ^ 59
def prefixEnd_3219470 : Nat := 4983230072969 + 3 ^ 40 * 3219470 * 2
def baseEnd_3219470 : Nat := 1653135562730624042518933

theorem tailTrace_3219470 : CollatzResearch.WordTrace tailWord_3219470 prefixEnd_3219470 1653135562730624042518933 := by
  unfold tailWord_3219470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14677964705802188318246983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78282478430945004363983909 14677964705802188318246983)
  ·
    refine ⟨22016947058703282477370475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14677964705802188318246983 22016947058703282477370475)
    ·
      refine ⟨33025420588054923716055713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22016947058703282477370475 33025420588054923716055713)
      ·
        refine ⟨24769065441041192787041785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33025420588054923716055713 24769065441041192787041785)
        ·
          refine ⟨18576799080780894590281339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24769065441041192787041785 18576799080780894590281339)
          ·
            refine ⟨27865198621171341885422009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18576799080780894590281339 27865198621171341885422009)
            ·
              refine ⟨20898898965878506414066507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27865198621171341885422009 20898898965878506414066507)
              ·
                refine ⟨31348348448817759621099761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20898898965878506414066507 31348348448817759621099761)
                ·
                  refine ⟨23511261336613319715824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31348348448817759621099761 23511261336613319715824821)
                  ·
                    refine ⟨2204180750307498723358577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23511261336613319715824821 2204180750307498723358577)
                    ·
                      refine ⟨1653135562730624042518933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204180750307498723358577 1653135562730624042518933)
                      ·
                        rfl

theorem cell23_3219470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3219470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219470 prefixEnd_3219470 := by exact prefixLift 3219470
  have htrace : WordTrace (prefixWord ++ tailWord_3219470) baseStart_3219470 baseEnd_3219470 := by
    simpa [prefixWord, tailWord_3219470, baseEnd_3219470] using wordTrace_append hprefix tailTrace_3219470
  have hstable : (prefixWord ++ tailWord_3219470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219470).length < 2 ^ (prefixWord ++ tailWord_3219470).sum := by decide
  have hdescent : baseEnd_3219470 < baseStart_3219470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219520 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_3219520 : Nat := 118140960795 + 3219520 * 2 ^ 59
def prefixEnd_3219520 : Nat := 4983230072969 + 3 ^ 40 * 3219520 * 2
def baseEnd_3219520 : Nat := 1653161236763348846893703

theorem tailTrace_3219520 : CollatzResearch.WordTrace tailWord_3219520 prefixEnd_3219520 1653161236763348846893703 := by
  unfold tailWord_3219520
  simp only [CollatzResearch.WordTrace]
  refine ⟨58712770648118182542648007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78283694197490910056864009 58712770648118182542648007)
  ·
    refine ⟨88069155972177273813972011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58712770648118182542648007 88069155972177273813972011)
    ·
      refine ⟨132103733958265910720958017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88069155972177273813972011 132103733958265910720958017)
      ·
        refine ⟨99077800468699433040718513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132103733958265910720958017 99077800468699433040718513)
        ·
          refine ⟨74308350351524574780538885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99077800468699433040718513 74308350351524574780538885)
          ·
            refine ⟨13932815690910857771351041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74308350351524574780538885 13932815690910857771351041)
            ·
              refine ⟨10449611768183143328513281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13932815690910857771351041 10449611768183143328513281)
              ·
                refine ⟨7837208826137357496384961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10449611768183143328513281 7837208826137357496384961)
                ·
                  refine ⟨5877906619603018122288721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837208826137357496384961 5877906619603018122288721)
                  ·
                    refine ⟨4408429964702263591716541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877906619603018122288721 4408429964702263591716541)
                    ·
                      refine ⟨1653161236763348846893703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408429964702263591716541 1653161236763348846893703)
                      ·
                        rfl

theorem cell23_3219520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_3219520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219520 prefixEnd_3219520 := by exact prefixLift 3219520
  have htrace : WordTrace (prefixWord ++ tailWord_3219520) baseStart_3219520 baseEnd_3219520 := by
    simpa [prefixWord, tailWord_3219520, baseEnd_3219520] using wordTrace_append hprefix tailTrace_3219520
  have hstable : (prefixWord ++ tailWord_3219520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219520).length < 2 ^ (prefixWord ++ tailWord_3219520).sum := by decide
  have hdescent : baseEnd_3219520 < baseStart_3219520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219527 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 1, 4]
def baseStart_3219527 : Nat := 118140960795 + 3219527 * 2 ^ 59
def prefixEnd_3219527 : Nat := 4983230072969 + 3 ^ 40 * 3219527 * 2
def baseEnd_3219527 : Nat := 551054943709310106502057

theorem tailTrace_3219527 : CollatzResearch.WordTrace tailWord_3219527 prefixEnd_3219527 551054943709310106502057 := by
  unfold tailWord_3219527
  simp only [CollatzResearch.WordTrace]
  refine ⟨117425796607211005280800835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78283864404807336853867223 117425796607211005280800835)
  ·
    refine ⟨176138694910816507921201253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117425796607211005280800835 176138694910816507921201253)
    ·
      refine ⟨33026005295778095235225235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176138694910816507921201253 33026005295778095235225235)
      ·
        refine ⟨49539007943667142852837853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33026005295778095235225235 49539007943667142852837853)
        ·
          refine ⟨18577127978875178569814195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49539007943667142852837853 18577127978875178569814195)
          ·
            refine ⟨27865691968312767854721293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18577127978875178569814195 27865691968312767854721293)
            ·
              refine ⟨10449634488117287945520485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27865691968312767854721293 10449634488117287945520485)
              ·
                refine ⟨1959306466521991489785091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10449634488117287945520485 1959306466521991489785091)
                ·
                  refine ⟨2938959699782987234677637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959306466521991489785091 2938959699782987234677637)
                  ·
                    refine ⟨551054943709310106502057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938959699782987234677637 551054943709310106502057)
                    ·
                      rfl

theorem cell23_3219527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_3219527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219527 prefixEnd_3219527 := by exact prefixLift 3219527
  have htrace : WordTrace (prefixWord ++ tailWord_3219527) baseStart_3219527 baseEnd_3219527 := by
    simpa [prefixWord, tailWord_3219527, baseEnd_3219527] using wordTrace_append hprefix tailTrace_3219527
  have hstable : (prefixWord ++ tailWord_3219527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219527).length < 2 ^ (prefixWord ++ tailWord_3219527).sum := by decide
  have hdescent : baseEnd_3219527 < baseStart_3219527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219618 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3219618 : Nat := 118140960795 + 3219618 * 2 ^ 59
def prefixEnd_3219618 : Nat := 4983230072969 + 3 ^ 40 * 3219618 * 2
def baseEnd_3219618 : Nat := 1653211557867489463468253

theorem tailTrace_3219618 : CollatzResearch.WordTrace tailWord_3219618 prefixEnd_3219618 1653211557867489463468253 := by
  unfold tailWord_3219618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357278912470331955590877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78286077099920885214909005 29357278912470331955590877)
  ·
    refine ⟨11008979592176374483346579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29357278912470331955590877 11008979592176374483346579)
    ·
      refine ⟨16513469388264561725019869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008979592176374483346579 16513469388264561725019869)
      ·
        refine ⟨6192551020599210646882451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16513469388264561725019869 6192551020599210646882451)
        ·
          refine ⟨9288826530898815970323677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192551020599210646882451 9288826530898815970323677)
          ·
            refine ⟨3483309949087055988871379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9288826530898815970323677 3483309949087055988871379)
            ·
              refine ⟨5224964923630583983307069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483309949087055988871379 5224964923630583983307069)
              ·
                refine ⟨1959361846361468993740151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5224964923630583983307069 1959361846361468993740151)
                ·
                  refine ⟨2939042769542203490610227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959361846361468993740151 2939042769542203490610227)
                  ·
                    refine ⟨4408564154313305235915341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2939042769542203490610227 4408564154313305235915341)
                    ·
                      refine ⟨1653211557867489463468253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408564154313305235915341 1653211557867489463468253)
                      ·
                        rfl

theorem cell23_3219618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3219618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219618 prefixEnd_3219618 := by exact prefixLift 3219618
  have htrace : WordTrace (prefixWord ++ tailWord_3219618) baseStart_3219618 baseEnd_3219618 := by
    simpa [prefixWord, tailWord_3219618, baseEnd_3219618] using wordTrace_append hprefix tailTrace_3219618
  have hstable : (prefixWord ++ tailWord_3219618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219618).length < 2 ^ (prefixWord ++ tailWord_3219618).sum := by decide
  have hdescent : baseEnd_3219618 < baseStart_3219618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219643 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 7]
def baseStart_3219643 : Nat := 118140960795 + 3219643 * 2 ^ 59
def prefixEnd_3219643 : Nat := 4983230072969 + 3 ^ 40 * 3219643 * 2
def baseEnd_3219643 : Nat := 551074798294617288551879

theorem tailTrace_3219643 : CollatzResearch.WordTrace tailWord_3219643 prefixEnd_3219643 551074798294617288551879 := by
  unfold tailWord_3219643
  simp only [CollatzResearch.WordTrace]
  refine ⟨117430027474790757092023583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78286684983193838061349055 117430027474790757092023583)
  ·
    refine ⟨176145041212186135638035375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117430027474790757092023583 176145041212186135638035375)
    ·
      refine ⟨264217561818279203457053063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176145041212186135638035375 264217561818279203457053063)
      ·
        refine ⟨396326342727418805185579595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264217561818279203457053063 396326342727418805185579595)
        ·
          refine ⟨594489514091128207778369393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396326342727418805185579595 594489514091128207778369393)
          ·
            refine ⟨445867135568346155833777045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594489514091128207778369393 445867135568346155833777045)
            ·
              refine ⟨20900021979766226054708299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 445867135568346155833777045 20900021979766226054708299)
              ·
                refine ⟨31350032969649339082062449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20900021979766226054708299 31350032969649339082062449)
                ·
                  refine ⟨23512524727237004311546837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31350032969649339082062449 23512524727237004311546837)
                  ·
                    refine ⟨551074798294617288551879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23512524727237004311546837 551074798294617288551879)
                    ·
                      rfl

theorem cell23_3219643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_3219643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219643 prefixEnd_3219643 := by exact prefixLift 3219643
  have htrace : WordTrace (prefixWord ++ tailWord_3219643) baseStart_3219643 baseEnd_3219643 := by
    simpa [prefixWord, tailWord_3219643, baseEnd_3219643] using wordTrace_append hprefix tailTrace_3219643
  have hstable : (prefixWord ++ tailWord_3219643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219643).length < 2 ^ (prefixWord ++ tailWord_3219643).sum := by decide
  have hdescent : baseEnd_3219643 < baseStart_3219643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219690 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3219690 : Nat := 118140960795 + 3219690 * 2 ^ 59
def prefixEnd_3219690 : Nat := 4983230072969 + 3 ^ 40 * 3219690 * 2
def baseEnd_3219690 : Nat := 551082842824871060589307

theorem tailTrace_3219690 : CollatzResearch.WordTrace tailWord_3219690 prefixEnd_3219690 551082842824871060589307 := by
  unfold tailWord_3219690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357935426405121029746131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78287827803746989412656349 29357935426405121029746131)
  ·
    refine ⟨44036903139607681544619197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357935426405121029746131 44036903139607681544619197)
    ·
      refine ⟨16513838677352880579232199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44036903139607681544619197 16513838677352880579232199)
      ·
        refine ⟨24770758016029320868848299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16513838677352880579232199 24770758016029320868848299)
        ·
          refine ⟨37156137024043981303272449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24770758016029320868848299 37156137024043981303272449)
          ·
            refine ⟨27867102768032985977454337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37156137024043981303272449 27867102768032985977454337)
            ·
              refine ⟨20900327076024739483090753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27867102768032985977454337 20900327076024739483090753)
              ·
                refine ⟨15675245307018554612318065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20900327076024739483090753 15675245307018554612318065)
                ·
                  refine ⟨11756433980263915959238549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15675245307018554612318065 11756433980263915959238549)
                  ·
                    refine ⟨551082842824871060589307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11756433980263915959238549 551082842824871060589307)
                    ·
                      rfl

theorem cell23_3219690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3219690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219690 prefixEnd_3219690 := by exact prefixLift 3219690
  have htrace : WordTrace (prefixWord ++ tailWord_3219690) baseStart_3219690 baseEnd_3219690 := by
    simpa [prefixWord, tailWord_3219690, baseEnd_3219690] using wordTrace_append hprefix tailTrace_3219690
  have hstable : (prefixWord ++ tailWord_3219690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219690).length < 2 ^ (prefixWord ++ tailWord_3219690).sum := by decide
  have hdescent : baseEnd_3219690 < baseStart_3219690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219720 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 9]
def baseStart_3219720 : Nat := 118140960795 + 3219720 * 2 ^ 59
def prefixEnd_3219720 : Nat := 4983230072969 + 3 ^ 40 * 3219720 * 2
def baseEnd_3219720 : Nat := 183695992543805340488087

theorem tailTrace_3219720 : CollatzResearch.WordTrace tailWord_3219720 prefixEnd_3219720 183695992543805340488087 := by
  unfold tailWord_3219720
  simp only [CollatzResearch.WordTrace]
  refine ⟨58716417947755899621288307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78288557263674532828384409 58716417947755899621288307)
  ·
    refine ⟨88074626921633849431932461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58716417947755899621288307 88074626921633849431932461)
    ·
      refine ⟨33027985095612693536974673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88074626921633849431932461 33027985095612693536974673)
      ·
        refine ⟨24770988821709520152731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33027985095612693536974673 24770988821709520152731005)
        ·
          refine ⟨9289120808141070057274127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24770988821709520152731005 9289120808141070057274127)
          ·
            refine ⟨13933681212211605085911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289120808141070057274127 13933681212211605085911191)
            ·
              refine ⟨20900521818317407628866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933681212211605085911191 20900521818317407628866787)
              ·
                refine ⟨31350782727476111443300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20900521818317407628866787 31350782727476111443300181)
                ·
                  refine ⟨183695992543805340488087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31350782727476111443300181 183695992543805340488087)
                  ·
                    rfl

theorem cell23_3219720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_3219720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219720 prefixEnd_3219720 := by exact prefixLift 3219720
  have htrace : WordTrace (prefixWord ++ tailWord_3219720) baseStart_3219720 baseEnd_3219720 := by
    simpa [prefixWord, tailWord_3219720, baseEnd_3219720] using wordTrace_append hprefix tailTrace_3219720
  have hstable : (prefixWord ++ tailWord_3219720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219720).length < 2 ^ (prefixWord ++ tailWord_3219720).sum := by decide
  have hdescent : baseEnd_3219720 < baseStart_3219720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219748 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3219748 : Nat := 118140960795 + 3219748 * 2 ^ 59
def prefixEnd_3219748 : Nat := 4983230072969 + 3 ^ 40 * 3219748 * 2
def baseEnd_3219748 : Nat := 1653278310352573954842655

theorem tailTrace_3219748 : CollatzResearch.WordTrace tailWord_3219748 prefixEnd_3219748 1653278310352573954842655 := by
  unfold tailWord_3219748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58716928569705180012297949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78289238092940240016397265 58716928569705180012297949)
  ·
    refine ⟨22018848213639442504611731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58716928569705180012297949 22018848213639442504611731)
    ·
      refine ⟨33028272320459163756917597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22018848213639442504611731 33028272320459163756917597)
      ·
        refine ⟨12385602120172186408844099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33028272320459163756917597 12385602120172186408844099)
        ·
          refine ⟨18578403180258279613266149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385602120172186408844099 18578403180258279613266149)
          ·
            refine ⟨3483450596298427427487403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18578403180258279613266149 3483450596298427427487403)
            ·
              refine ⟨5225175894447641141231105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483450596298427427487403 5225175894447641141231105)
              ·
                refine ⟨3918881920835730855923329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225175894447641141231105 3918881920835730855923329)
                ·
                  refine ⟨2939161440626798141942497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918881920835730855923329 2939161440626798141942497)
                  ·
                    refine ⟨2204371080470098606456873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2939161440626798141942497 2204371080470098606456873)
                    ·
                      refine ⟨1653278310352573954842655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204371080470098606456873 1653278310352573954842655)
                      ·
                        rfl

theorem cell23_3219748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3219748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219748 prefixEnd_3219748 := by exact prefixLift 3219748
  have htrace : WordTrace (prefixWord ++ tailWord_3219748) baseStart_3219748 baseEnd_3219748 := by
    simpa [prefixWord, tailWord_3219748, baseEnd_3219748] using wordTrace_append hprefix tailTrace_3219748
  have hstable : (prefixWord ++ tailWord_3219748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219748).length < 2 ^ (prefixWord ++ tailWord_3219748).sum := by decide
  have hdescent : baseEnd_3219748 < baseStart_3219748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219754 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_3219754 : Nat := 118140960795 + 3219754 * 2 ^ 59
def prefixEnd_3219754 : Nat := 4983230072969 + 3 ^ 40 * 3219754 * 2
def baseEnd_3219754 : Nat := 183697932359611214596403

theorem tailTrace_3219754 : CollatzResearch.WordTrace tailWord_3219754 prefixEnd_3219754 183697932359611214596403 := by
  unfold tailWord_3219754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29358518994347155762328579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78289383984925748699542877 29358518994347155762328579)
  ·
    refine ⟨44037778491520733643492869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29358518994347155762328579 44037778491520733643492869)
    ·
      refine ⟨8257083467160137558154913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44037778491520733643492869 8257083467160137558154913)
      ·
        refine ⟨6192812600370103168616185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8257083467160137558154913 6192812600370103168616185)
        ·
          refine ⟨4644609450277577376462139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6192812600370103168616185 4644609450277577376462139)
          ·
            refine ⟨6966914175416366064693209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644609450277577376462139 6966914175416366064693209)
            ·
              refine ⟨5225185631562274548519907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6966914175416366064693209 5225185631562274548519907)
              ·
                refine ⟨7837778447343411822779861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225185631562274548519907 7837778447343411822779861)
                ·
                  refine ⟨183697932359611214596403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7837778447343411822779861 183697932359611214596403)
                  ·
                    rfl

theorem cell23_3219754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_3219754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219754 prefixEnd_3219754 := by exact prefixLift 3219754
  have htrace : WordTrace (prefixWord ++ tailWord_3219754) baseStart_3219754 baseEnd_3219754 := by
    simpa [prefixWord, tailWord_3219754, baseEnd_3219754] using wordTrace_append hprefix tailTrace_3219754
  have hstable : (prefixWord ++ tailWord_3219754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219754).length < 2 ^ (prefixWord ++ tailWord_3219754).sum := by decide
  have hdescent : baseEnd_3219754 < baseStart_3219754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219764 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3219764 : Nat := 118140960795 + 3219764 * 2 ^ 59
def prefixEnd_3219764 : Nat := 4983230072969 + 3 ^ 40 * 3219764 * 2
def baseEnd_3219764 : Nat := 1653286526043045892242581

theorem tailTrace_3219764 : CollatzResearch.WordTrace tailWord_3219764 prefixEnd_3219764 1653286526043045892242581 := by
  unfold tailWord_3219764
  simp only [CollatzResearch.WordTrace]
  refine ⟨58717220353676197378589173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78289627138234929838118897 58717220353676197378589173)
  ·
    refine ⟨5504739408157143504242735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58717220353676197378589173 5504739408157143504242735)
    ·
      refine ⟨8257109112235715256364103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504739408157143504242735 8257109112235715256364103)
      ·
        refine ⟨12385663668353572884546155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257109112235715256364103 12385663668353572884546155)
        ·
          refine ⟨18578495502530359326819233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385663668353572884546155 18578495502530359326819233)
          ·
            refine ⟨13933871626897769495114425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18578495502530359326819233 13933871626897769495114425)
            ·
              refine ⟨10450403720173327121335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13933871626897769495114425 10450403720173327121335819)
              ·
                refine ⟨15675605580259990682003729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10450403720173327121335819 15675605580259990682003729)
                ·
                  refine ⟨11756704185194993011502797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15675605580259990682003729 11756704185194993011502797)
                  ·
                    refine ⟨4408764069448122379313549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11756704185194993011502797 4408764069448122379313549)
                    ·
                      refine ⟨1653286526043045892242581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408764069448122379313549 1653286526043045892242581)
                      ·
                        rfl

theorem cell23_3219764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3219764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219764 prefixEnd_3219764 := by exact prefixLift 3219764
  have htrace : WordTrace (prefixWord ++ tailWord_3219764) baseStart_3219764 baseEnd_3219764 := by
    simpa [prefixWord, tailWord_3219764, baseEnd_3219764] using wordTrace_append hprefix tailTrace_3219764
  have hstable : (prefixWord ++ tailWord_3219764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219764).length < 2 ^ (prefixWord ++ tailWord_3219764).sum := by decide
  have hdescent : baseEnd_3219764 < baseStart_3219764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 4, 2]
def baseStart_3219787 : Nat := 118140960795 + 3219787 * 2 ^ 59
def prefixEnd_3219787 : Nat := 4983230072969 + 3 ^ 40 * 3219787 * 2
def baseEnd_3219787 : Nat := 1653298336098099302254975

theorem tailTrace_3219787 : CollatzResearch.WordTrace tailWord_3219787 prefixEnd_3219787 1653298336098099302254975 := by
  unfold tailWord_3219787
  simp only [CollatzResearch.WordTrace]
  refine ⟨117435279586269069685265615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78290186390846046456843743 117435279586269069685265615)
  ·
    refine ⟨176152919379403604527898423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117435279586269069685265615 176152919379403604527898423)
    ·
      refine ⟨264229379069105406791847635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176152919379403604527898423 264229379069105406791847635)
      ·
        refine ⟨396344068603658110187771453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264229379069105406791847635 396344068603658110187771453)
        ·
          refine ⟨148629025726371791320414295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396344068603658110187771453 148629025726371791320414295)
          ·
            refine ⟨222943538589557686980621443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148629025726371791320414295 222943538589557686980621443)
            ·
              refine ⟨334415307884336530470932165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222943538589557686980621443 334415307884336530470932165)
              ·
                refine ⟨62702870228313099463299781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334415307884336530470932165 62702870228313099463299781)
                ·
                  refine ⟨11756788167808706149368709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62702870228313099463299781 11756788167808706149368709)
                  ·
                    refine ⟨2204397781464132403006633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11756788167808706149368709 2204397781464132403006633)
                    ·
                      refine ⟨1653298336098099302254975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204397781464132403006633 1653298336098099302254975)
                      ·
                        rfl

theorem cell23_3219787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4, 2].length) (baseStart_3219787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219787 prefixEnd_3219787 := by exact prefixLift 3219787
  have htrace : WordTrace (prefixWord ++ tailWord_3219787) baseStart_3219787 baseEnd_3219787 := by
    simpa [prefixWord, tailWord_3219787, baseEnd_3219787] using wordTrace_append hprefix tailTrace_3219787
  have hstable : (prefixWord ++ tailWord_3219787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219787).length < 2 ^ (prefixWord ++ tailWord_3219787).sum := by decide
  have hdescent : baseEnd_3219787 < baseStart_3219787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219800 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3219800 : Nat := 118140960795 + 3219800 * 2 ^ 59
def prefixEnd_3219800 : Nat := 4983230072969 + 3 ^ 40 * 3219800 * 2
def baseEnd_3219800 : Nat := 1653305011346607751392415

theorem tailTrace_3219800 : CollatzResearch.WordTrace tailWord_3219800 prefixEnd_3219800 1653305011346607751392415 := by
  unfold tailWord_3219800
  simp only [CollatzResearch.WordTrace]
  refine ⟨58717876867610986452744427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78290502490147981936992569 58717876867610986452744427)
  ·
    refine ⟨88076815301416479679116641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58717876867610986452744427 88076815301416479679116641)
    ·
      refine ⟨66057611476062359759337481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88076815301416479679116641 66057611476062359759337481)
      ·
        refine ⟨49543208607046769819503111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66057611476062359759337481 49543208607046769819503111)
        ·
          refine ⟨74314812910570154729254667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49543208607046769819503111 74314812910570154729254667)
          ·
            refine ⟨111472219365855232093882001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74314812910570154729254667 111472219365855232093882001)
            ·
              refine ⟨83604164524391424070411501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111472219365855232093882001 83604164524391424070411501)
              ·
                refine ⟨31351561696646784026404313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83604164524391424070411501 31351561696646784026404313)
                ·
                  refine ⟨23513671272485088019803235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31351561696646784026404313 23513671272485088019803235)
                  ·
                    refine ⟨35270506908727632029704853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23513671272485088019803235 35270506908727632029704853)
                    ·
                      refine ⟨1653305011346607751392415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35270506908727632029704853 1653305011346607751392415)
                      ·
                        rfl

theorem cell23_3219800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3219800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219800 prefixEnd_3219800 := by exact prefixLift 3219800
  have htrace : WordTrace (prefixWord ++ tailWord_3219800) baseStart_3219800 baseEnd_3219800 := by
    simpa [prefixWord, tailWord_3219800, baseEnd_3219800] using wordTrace_append hprefix tailTrace_3219800
  have hstable : (prefixWord ++ tailWord_3219800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219800).length < 2 ^ (prefixWord ++ tailWord_3219800).sum := by decide
  have hdescent : baseEnd_3219800 < baseStart_3219800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219807 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_3219807 : Nat := 118140960795 + 3219807 * 2 ^ 59
def prefixEnd_3219807 : Nat := 4983230072969 + 3 ^ 40 * 3219807 * 2
def baseEnd_3219807 : Nat := 1653308605711189224004883

theorem tailTrace_3219807 : CollatzResearch.WordTrace tailWord_3219807 prefixEnd_3219807 1653308605711189224004883 := by
  unfold tailWord_3219807
  simp only [CollatzResearch.WordTrace]
  refine ⟨117436009046196613100993675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78290672697464408733995783 117436009046196613100993675)
  ·
    refine ⟨176154013569294919651490513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117436009046196613100993675 176154013569294919651490513)
    ·
      refine ⟨132115510176971189738617885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176154013569294919651490513 132115510176971189738617885)
      ·
        refine ⟨49543316316364196151981707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132115510176971189738617885 49543316316364196151981707)
        ·
          refine ⟨74314974474546294227972561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49543316316364196151981707 74314974474546294227972561)
          ·
            refine ⟨55736230855909720670979421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74314974474546294227972561 55736230855909720670979421)
            ·
              refine ⟨20901086570966145251617283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55736230855909720670979421 20901086570966145251617283)
              ·
                refine ⟨31351629856449217877425925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20901086570966145251617283 31351629856449217877425925)
                ·
                  refine ⟨5878430598084228352017361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31351629856449217877425925 5878430598084228352017361)
                  ·
                    refine ⟨4408822948563171264013021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878430598084228352017361 4408822948563171264013021)
                    ·
                      refine ⟨1653308605711189224004883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408822948563171264013021 1653308605711189224004883)
                      ·
                        rfl

theorem cell23_3219807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_3219807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219807 prefixEnd_3219807 := by exact prefixLift 3219807
  have htrace : WordTrace (prefixWord ++ tailWord_3219807) baseStart_3219807 baseEnd_3219807 := by
    simpa [prefixWord, tailWord_3219807, baseEnd_3219807] using wordTrace_append hprefix tailTrace_3219807
  have hstable : (prefixWord ++ tailWord_3219807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219807).length < 2 ^ (prefixWord ++ tailWord_3219807).sum := by decide
  have hdescent : baseEnd_3219807 < baseStart_3219807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219841 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3219841 : Nat := 118140960795 + 3219841 * 2 ^ 59
def prefixEnd_3219841 : Nat := 4983230072969 + 3 ^ 40 * 3219841 * 2
def baseEnd_3219841 : Nat := 1653326064053442090979727

theorem tailTrace_3219841 : CollatzResearch.WordTrace tailWord_3219841 prefixEnd_3219841 1653326064053442090979727 := by
  unfold tailWord_3219841
  simp only [CollatzResearch.WordTrace]
  refine ⟨117437249128073436907731377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78291499418715624605154251 117437249128073436907731377)
  ·
    refine ⟨88077936846055077680798533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117437249128073436907731377 88077936846055077680798533)
    ·
      refine ⟨16514613158635327065149725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88077936846055077680798533 16514613158635327065149725)
      ·
        refine ⟨6192979934488247649431147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16514613158635327065149725 6192979934488247649431147)
        ·
          refine ⟨9289469901732371474146721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192979934488247649431147 9289469901732371474146721)
          ·
            refine ⟨6967102426299278605610041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9289469901732371474146721 6967102426299278605610041)
            ·
              refine ⟨5225326819724458954207531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6967102426299278605610041 5225326819724458954207531)
              ·
                refine ⟨7837990229586688431311297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225326819724458954207531 7837990229586688431311297)
                ·
                  refine ⟨5878492672190016323483473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837990229586688431311297 5878492672190016323483473)
                  ·
                    refine ⟨4408869504142512242612605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878492672190016323483473 4408869504142512242612605)
                    ·
                      refine ⟨1653326064053442090979727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408869504142512242612605 1653326064053442090979727)
                      ·
                        rfl

theorem cell23_3219841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3219841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219841 prefixEnd_3219841 := by exact prefixLift 3219841
  have htrace : WordTrace (prefixWord ++ tailWord_3219841) baseStart_3219841 baseEnd_3219841 := by
    simpa [prefixWord, tailWord_3219841, baseEnd_3219841] using wordTrace_append hprefix tailTrace_3219841
  have hstable : (prefixWord ++ tailWord_3219841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219841).length < 2 ^ (prefixWord ++ tailWord_3219841).sum := by decide
  have hdescent : baseEnd_3219841 < baseStart_3219841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219877 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_3219877 : Nat := 118140960795 + 3219877 * 2 ^ 59
def prefixEnd_3219877 : Nat := 4983230072969 + 3 ^ 40 * 3219877 * 2
def baseEnd_3219877 : Nat := 1653344549357003950129561

theorem tailTrace_3219877 : CollatzResearch.WordTrace tailWord_3219877 prefixEnd_3219877 1653344549357003950129561 := by
  unfold tailWord_3219877
  simp only [CollatzResearch.WordTrace]
  refine ⟨117438562155943015056041885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78292374770628676704027923 117438562155943015056041885)
  ·
    refine ⟨44039460808478630646015707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117438562155943015056041885 44039460808478630646015707)
    ·
      refine ⟨66059191212717945969023561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44039460808478630646015707 66059191212717945969023561)
      ·
        refine ⟨49544393409538459476767671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66059191212717945969023561 49544393409538459476767671)
        ·
          refine ⟨74316590114307689215151507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49544393409538459476767671 74316590114307689215151507)
          ·
            refine ⟨111474885171461533822727261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74316590114307689215151507 111474885171461533822727261)
            ·
              refine ⟨41803081939298075183522723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111474885171461533822727261 41803081939298075183522723)
              ·
                refine ⟨62704622908947112775284085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41803081939298075183522723 62704622908947112775284085)
                ·
                  refine ⟨5878558397713791822682883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62704622908947112775284085 5878558397713791822682883)
                  ·
                    refine ⟨8817837596570687734024325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5878558397713791822682883 8817837596570687734024325)
                    ·
                      refine ⟨1653344549357003950129561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8817837596570687734024325 1653344549357003950129561)
                      ·
                        rfl

theorem cell23_3219877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_3219877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219877 prefixEnd_3219877 := by exact prefixLift 3219877
  have htrace : WordTrace (prefixWord ++ tailWord_3219877) baseStart_3219877 baseEnd_3219877 := by
    simpa [prefixWord, tailWord_3219877, baseEnd_3219877] using wordTrace_append hprefix tailTrace_3219877
  have hstable : (prefixWord ++ tailWord_3219877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219877).length < 2 ^ (prefixWord ++ tailWord_3219877).sum := by decide
  have hdescent : baseEnd_3219877 < baseStart_3219877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219887 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 8, 4]
def baseStart_3219887 : Nat := 118140960795 + 3219887 * 2 ^ 59
def prefixEnd_3219887 : Nat := 4983230072969 + 3 ^ 40 * 3219887 * 2
def baseEnd_3219887 : Nat := 551116561387849637001505

theorem tailTrace_3219887 : CollatzResearch.WordTrace tailWord_3219887 prefixEnd_3219887 551116561387849637001505 := by
  unfold tailWord_3219887
  simp only [CollatzResearch.WordTrace]
  refine ⟨117438926885906786763905915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78292617923937857842603943 117438926885906786763905915)
  ·
    refine ⟨176158390328860180145858873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117438926885906786763905915 176158390328860180145858873)
    ·
      refine ⟨132118792746645135109394155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176158390328860180145858873 132118792746645135109394155)
      ·
        refine ⟨198178189119967702664091233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132118792746645135109394155 198178189119967702664091233)
        ·
          refine ⟨148633641839975776998068425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198178189119967702664091233 148633641839975776998068425)
          ·
            refine ⟨111475231379981832748551319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148633641839975776998068425 111475231379981832748551319)
            ·
              refine ⟨167212847069972749122826979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111475231379981832748551319 167212847069972749122826979)
              ·
                refine ⟨250819270604959123684240469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167212847069972749122826979 250819270604959123684240469)
                ·
                  refine ⟨2939288327401864730674693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 250819270604959123684240469 2939288327401864730674693)
                  ·
                    refine ⟨551116561387849637001505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939288327401864730674693 551116561387849637001505)
                    ·
                      rfl

theorem cell23_3219887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_3219887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219887 prefixEnd_3219887 := by exact prefixLift 3219887
  have htrace : WordTrace (prefixWord ++ tailWord_3219887) baseStart_3219887 baseEnd_3219887 := by
    simpa [prefixWord, tailWord_3219887, baseEnd_3219887] using wordTrace_append hprefix tailTrace_3219887
  have hstable : (prefixWord ++ tailWord_3219887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219887).length < 2 ^ (prefixWord ++ tailWord_3219887).sum := by decide
  have hdescent : baseEnd_3219887 < baseStart_3219887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219892 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3219892 : Nat := 118140960795 + 3219892 * 2 ^ 59
def prefixEnd_3219892 : Nat := 4983230072969 + 3 ^ 40 * 3219892 * 2
def baseEnd_3219892 : Nat := 1653352251566821391441993

theorem tailTrace_3219892 : CollatzResearch.WordTrace tailWord_3219892 prefixEnd_3219892 1653352251566821391441993 := by
  unfold tailWord_3219892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58719554625444336308918965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78292739500592448411891953 58719554625444336308918965)
  ·
    refine ⟨5504958246135406528961153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58719554625444336308918965 5504958246135406528961153)
    ·
      refine ⟨4128718684601554896720865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5504958246135406528961153 4128718684601554896720865)
      ·
        refine ⟨3096539013451166172540649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4128718684601554896720865 3096539013451166172540649)
        ·
          refine ⟨2322404260088374629405487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096539013451166172540649 2322404260088374629405487)
          ·
            refine ⟨3483606390132561944108231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322404260088374629405487 3483606390132561944108231)
            ·
              refine ⟨5225409585198842916162347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483606390132561944108231 5225409585198842916162347)
              ·
                refine ⟨7838114377798264374243521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225409585198842916162347 7838114377798264374243521)
                ·
                  refine ⟨5878585783348698280682641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7838114377798264374243521 5878585783348698280682641)
                  ·
                    refine ⟨4408939337511523710511981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878585783348698280682641 4408939337511523710511981)
                    ·
                      refine ⟨1653352251566821391441993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408939337511523710511981 1653352251566821391441993)
                      ·
                        rfl

theorem cell23_3219892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3219892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219892 prefixEnd_3219892 := by exact prefixLift 3219892
  have htrace : WordTrace (prefixWord ++ tailWord_3219892) baseStart_3219892 baseEnd_3219892 := by
    simpa [prefixWord, tailWord_3219892, baseEnd_3219892] using wordTrace_append hprefix tailTrace_3219892
  have hstable : (prefixWord ++ tailWord_3219892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219892).length < 2 ^ (prefixWord ++ tailWord_3219892).sum := by decide
  have hdescent : baseEnd_3219892 < baseStart_3219892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219911 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_3219911 : Nat := 118140960795 + 3219911 * 2 ^ 59
def prefixEnd_3219911 : Nat := 4983230072969 + 3 ^ 40 * 3219911 * 2
def baseEnd_3219911 : Nat := 1653362007699256817104405

theorem tailTrace_3219911 : CollatzResearch.WordTrace tailWord_3219911 prefixEnd_3219911 1653362007699256817104405 := by
  unfold tailWord_3219911
  simp only [CollatzResearch.WordTrace]
  refine ⟨117439802237819838862779587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78293201491879892575186391 117439802237819838862779587)
  ·
    refine ⟨176159703356729758294169381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117439802237819838862779587 176159703356729758294169381)
    ·
      refine ⟨33029944379386829680156759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176159703356729758294169381 33029944379386829680156759)
      ·
        refine ⟨49544916569080244520235139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33029944379386829680156759 49544916569080244520235139)
        ·
          refine ⟨74317374853620366780352709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49544916569080244520235139 74317374853620366780352709)
          ·
            refine ⟨13934507785053818771316133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74317374853620366780352709 13934507785053818771316133)
            ·
              refine ⟨2612720209697591019621775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13934507785053818771316133 2612720209697591019621775)
              ·
                refine ⟨3919080314546386529432663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612720209697591019621775 3919080314546386529432663)
                ·
                  refine ⟨5878620471819579794148995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919080314546386529432663 5878620471819579794148995)
                  ·
                    refine ⟨8817930707729369691223493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5878620471819579794148995 8817930707729369691223493)
                    ·
                      refine ⟨1653362007699256817104405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8817930707729369691223493 1653362007699256817104405)
                      ·
                        rfl

theorem cell23_3219911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_3219911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219911 prefixEnd_3219911 := by exact prefixLift 3219911
  have htrace : WordTrace (prefixWord ++ tailWord_3219911) baseStart_3219911 baseEnd_3219911 := by
    simpa [prefixWord, tailWord_3219911, baseEnd_3219911] using wordTrace_append hprefix tailTrace_3219911
  have hstable : (prefixWord ++ tailWord_3219911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219911).length < 2 ^ (prefixWord ++ tailWord_3219911).sum := by decide
  have hdescent : baseEnd_3219911 < baseStart_3219911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219927 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3219927 : Nat := 118140960795 + 3219927 * 2 ^ 59
def prefixEnd_3219927 : Nat := 4983230072969 + 3 ^ 40 * 3219927 * 2
def baseEnd_3219927 : Nat := 1653370223389728754504331

theorem tailTrace_3219927 : CollatzResearch.WordTrace tailWord_3219927 prefixEnd_3219927 1653370223389728754504331 := by
  unfold tailWord_3219927
  simp only [CollatzResearch.WordTrace]
  refine ⟨117440385805761873595362035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78293590537174582396908023 117440385805761873595362035)
  ·
    refine ⟨176160578708642810393043053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117440385805761873595362035 176160578708642810393043053)
    ·
      refine ⟨66060217015741053897391145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176160578708642810393043053 66060217015741053897391145)
      ·
        refine ⟨49545162761805790423043359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66060217015741053897391145 49545162761805790423043359)
        ·
          refine ⟨74317744142708685634565039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49545162761805790423043359 74317744142708685634565039)
          ·
            refine ⟨111476616214063028451847559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74317744142708685634565039 111476616214063028451847559)
            ·
              refine ⟨167214924321094542677771339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111476616214063028451847559 167214924321094542677771339)
              ·
                refine ⟨250822386481641814016657009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167214924321094542677771339 250822386481641814016657009)
                ·
                  refine ⟨188116789861231360512492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250822386481641814016657009 188116789861231360512492757)
                  ·
                    refine ⟨4408987262372610012011549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188116789861231360512492757 4408987262372610012011549)
                    ·
                      refine ⟨1653370223389728754504331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4408987262372610012011549 1653370223389728754504331)
                      ·
                        rfl

theorem cell23_3219927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3219927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219927 prefixEnd_3219927 := by exact prefixLift 3219927
  have htrace : WordTrace (prefixWord ++ tailWord_3219927) baseStart_3219927 baseEnd_3219927 := by
    simpa [prefixWord, tailWord_3219927, baseEnd_3219927] using wordTrace_append hprefix tailTrace_3219927
  have hstable : (prefixWord ++ tailWord_3219927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219927).length < 2 ^ (prefixWord ++ tailWord_3219927).sum := by decide
  have hdescent : baseEnd_3219927 < baseStart_3219927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219971 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 1, 3, 2]
def baseStart_3219971 : Nat := 118140960795 + 3219971 * 2 ^ 59
def prefixEnd_3219971 : Nat := 4983230072969 + 3 ^ 40 * 3219971 * 2
def baseEnd_3219971 : Nat := 1653392816538526582354129

theorem tailTrace_3219971 : CollatzResearch.WordTrace tailWord_3219971 prefixEnd_3219971 1653392816538526582354129 := by
  unfold tailWord_3219971
  simp only [CollatzResearch.WordTrace]
  refine ⟨117441990617602469109963767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78294660411734979406642511 117441990617602469109963767)
  ·
    refine ⟨176162985926403703664945651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117441990617602469109963767 176162985926403703664945651)
    ·
      refine ⟨264244478889605555497418477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176162985926403703664945651 264244478889605555497418477)
      ·
        refine ⟨99091679583602083311531929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264244478889605555497418477 99091679583602083311531929)
        ·
          refine ⟨74318759687701562483648947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99091679583602083311531929 74318759687701562483648947)
          ·
            refine ⟨111478139531552343725473421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74318759687701562483648947 111478139531552343725473421)
            ·
              refine ⟨41804302324332128897052533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111478139531552343725473421 41804302324332128897052533)
              ·
                refine ⟨3919153342906137084098675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41804302324332128897052533 3919153342906137084098675)
                ·
                  refine ⟨5878730014359205626148013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919153342906137084098675 5878730014359205626148013)
                  ·
                    refine ⟨2204523755384702109805505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5878730014359205626148013 2204523755384702109805505)
                    ·
                      refine ⟨1653392816538526582354129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204523755384702109805505 1653392816538526582354129)
                      ·
                        rfl

theorem cell23_3219971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_3219971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219971 prefixEnd_3219971 := by exact prefixLift 3219971
  have htrace : WordTrace (prefixWord ++ tailWord_3219971) baseStart_3219971 baseEnd_3219971 := by
    simpa [prefixWord, tailWord_3219971, baseEnd_3219971] using wordTrace_append hprefix tailTrace_3219971
  have hstable : (prefixWord ++ tailWord_3219971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219971).length < 2 ^ (prefixWord ++ tailWord_3219971).sum := by decide
  have hdescent : baseEnd_3219971 < baseStart_3219971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219977 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_3219977 : Nat := 118140960795 + 3219977 * 2 ^ 59
def prefixEnd_3219977 : Nat := 4983230072969 + 3 ^ 40 * 3219977 * 2
def baseEnd_3219977 : Nat := 551131965807484519626367

theorem tailTrace_3219977 : CollatzResearch.WordTrace tailWord_3219977 prefixEnd_3219977 551131965807484519626367 := by
  unfold tailWord_3219977
  simp only [CollatzResearch.WordTrace]
  refine ⟨117442209455580732134682185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78294806303720488089788123 117442209455580732134682185)
  ·
    refine ⟨88081657091685549101011639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117442209455580732134682185 88081657091685549101011639)
    ·
      refine ⟨132122485637528323651517459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88081657091685549101011639 132122485637528323651517459)
      ·
        refine ⟨198183728456292485477276189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132122485637528323651517459 198183728456292485477276189)
        ·
          refine ⟨74318898171109682053978571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198183728456292485477276189 74318898171109682053978571)
          ·
            refine ⟨111478347256664523080967857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74318898171109682053978571 111478347256664523080967857)
            ·
              refine ⟨83608760442498392310725893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111478347256664523080967857 83608760442498392310725893)
              ·
                refine ⟨15676642582968448558261105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83608760442498392310725893 15676642582968448558261105)
                ·
                  refine ⟨11757481937226336418695829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676642582968448558261105 11757481937226336418695829)
                  ·
                    refine ⟨551131965807484519626367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11757481937226336418695829 551131965807484519626367)
                    ·
                      rfl

theorem cell23_3219977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_3219977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219977 prefixEnd_3219977 := by exact prefixLift 3219977
  have htrace : WordTrace (prefixWord ++ tailWord_3219977) baseStart_3219977 baseEnd_3219977 := by
    simpa [prefixWord, tailWord_3219977, baseEnd_3219977] using wordTrace_append hprefix tailTrace_3219977
  have hstable : (prefixWord ++ tailWord_3219977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219977).length < 2 ^ (prefixWord ++ tailWord_3219977).sum := by decide
  have hdescent : baseEnd_3219977 < baseStart_3219977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219987 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_3219987 : Nat := 118140960795 + 3219987 * 2 ^ 59
def prefixEnd_3219987 : Nat := 4983230072969 + 3 ^ 40 * 3219987 * 2
def baseEnd_3219987 : Nat := 1653401032228998519754055

theorem tailTrace_3219987 : CollatzResearch.WordTrace tailWord_3219987 prefixEnd_3219987 1653401032228998519754055 := by
  unfold tailWord_3219987
  simp only [CollatzResearch.WordTrace]
  refine ⟨117442574185544503842546215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78295049457029669228364143 117442574185544503842546215)
  ·
    refine ⟨176163861278316755763819323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117442574185544503842546215 176163861278316755763819323)
    ·
      refine ⟨264245791917475133645728985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176163861278316755763819323 264245791917475133645728985)
      ·
        refine ⟨198184343938106350234296739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264245791917475133645728985 198184343938106350234296739)
        ·
          refine ⟨297276515907159525351445109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198184343938106350234296739 297276515907159525351445109)
          ·
            refine ⟨27869673366296205501697979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297276515907159525351445109 27869673366296205501697979)
            ·
              refine ⟨41804510049444308252546969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27869673366296205501697979 41804510049444308252546969)
              ·
                refine ⟨31353382537083231189410227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41804510049444308252546969 31353382537083231189410227)
                ·
                  refine ⟨47030073805624846784115341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31353382537083231189410227 47030073805624846784115341)
                  ·
                    refine ⟨17636277677109317544043253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47030073805624846784115341 17636277677109317544043253)
                    ·
                      refine ⟨1653401032228998519754055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17636277677109317544043253 1653401032228998519754055)
                      ·
                        rfl

theorem cell23_3219987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_3219987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3219987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3219987 prefixEnd_3219987 := by exact prefixLift 3219987
  have htrace : WordTrace (prefixWord ++ tailWord_3219987) baseStart_3219987 baseEnd_3219987 := by
    simpa [prefixWord, tailWord_3219987, baseEnd_3219987] using wordTrace_append hprefix tailTrace_3219987
  have hstable : (prefixWord ++ tailWord_3219987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219987).length < 2 ^ (prefixWord ++ tailWord_3219987).sum := by decide
  have hdescent : baseEnd_3219987 < baseStart_3219987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220001 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3220001 : Nat := 118140960795 + 3220001 * 2 ^ 59
def prefixEnd_3220001 : Nat := 4983230072969 + 3 ^ 40 * 3220001 * 2
def baseEnd_3220001 : Nat := 1653408220958161464978991

theorem tailTrace_3220001 : CollatzResearch.WordTrace tailWord_3220001 prefixEnd_3220001 1653408220958161464978991 := by
  unfold tailWord_3220001
  simp only [CollatzResearch.WordTrace]
  refine ⟨117443084807493784233555857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78295389871662522822370571 117443084807493784233555857)
  ·
    refine ⟨88082313605620338175166893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117443084807493784233555857 88082313605620338175166893)
    ·
      refine ⟨33030867602107626815687585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88082313605620338175166893 33030867602107626815687585)
      ·
        refine ⟨24773150701580720111765689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33030867602107626815687585 24773150701580720111765689)
        ·
          refine ⟨18579863026185540083824267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24773150701580720111765689 18579863026185540083824267)
          ·
            refine ⟨27869794539278310125736401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18579863026185540083824267 27869794539278310125736401)
            ·
              refine ⟨20902345904458732594302301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27869794539278310125736401 20902345904458732594302301)
              ·
                refine ⟨7838379714172024722863363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20902345904458732594302301 7838379714172024722863363)
                ·
                  refine ⟨11757569571258037084295045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838379714172024722863363 11757569571258037084295045)
                  ·
                    refine ⟨2204544294610881953305321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11757569571258037084295045 2204544294610881953305321)
                    ·
                      refine ⟨1653408220958161464978991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204544294610881953305321 1653408220958161464978991)
                      ·
                        rfl

theorem cell23_3220001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3220001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220001 prefixEnd_3220001 := by exact prefixLift 3220001
  have htrace : WordTrace (prefixWord ++ tailWord_3220001) baseStart_3220001 baseEnd_3220001 := by
    simpa [prefixWord, tailWord_3220001, baseEnd_3220001] using wordTrace_append hprefix tailTrace_3220001
  have hstable : (prefixWord ++ tailWord_3220001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220001).length < 2 ^ (prefixWord ++ tailWord_3220001).sum := by decide
  have hdescent : baseEnd_3220001 < baseStart_3220001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220022 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3220022 : Nat := 118140960795 + 3220022 * 2 ^ 59
def prefixEnd_3220022 : Nat := 4983230072969 + 3 ^ 40 * 3220022 * 2
def baseEnd_3220022 : Nat := 1653419004051905882816395

theorem tailTrace_3220022 : CollatzResearch.WordTrace tailWord_3220022 prefixEnd_3220022 1653419004051905882816395 := by
  unfold tailWord_3220022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340240671276106551254395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78295900493611803213380213 7340240671276106551254395)
  ·
    refine ⟨11010361006914159826881593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7340240671276106551254395 11010361006914159826881593)
    ·
      refine ⟨8257770755185619870161195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11010361006914159826881593 8257770755185619870161195)
      ·
        refine ⟨12386656132778429805241793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257770755185619870161195 12386656132778429805241793)
        ·
          refine ⟨9289992099583822353931345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12386656132778429805241793 9289992099583822353931345)
          ·
            refine ⟨6967494074687866765448509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9289992099583822353931345 6967494074687866765448509)
            ·
              refine ⟨2612810278007950037043191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6967494074687866765448509 2612810278007950037043191)
              ·
                refine ⟨3919215417011925055564787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612810278007950037043191 3919215417011925055564787)
                ·
                  refine ⟨5878823125517887583347181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919215417011925055564787 5878823125517887583347181)
                  ·
                    refine ⟨2204558672069207843755193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5878823125517887583347181 2204558672069207843755193)
                    ·
                      refine ⟨1653419004051905882816395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204558672069207843755193 1653419004051905882816395)
                      ·
                        rfl

theorem cell23_3220022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3220022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220022 prefixEnd_3220022 := by exact prefixLift 3220022
  have htrace : WordTrace (prefixWord ++ tailWord_3220022) baseStart_3220022 baseEnd_3220022 := by
    simpa [prefixWord, tailWord_3220022, baseEnd_3220022] using wordTrace_append hprefix tailTrace_3220022
  have hstable : (prefixWord ++ tailWord_3220022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220022).length < 2 ^ (prefixWord ++ tailWord_3220022).sum := by decide
  have hdescent : baseEnd_3220022 < baseStart_3220022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220038 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3220038 : Nat := 118140960795 + 3220038 * 2 ^ 59
def prefixEnd_3220038 : Nat := 4983230072969 + 3 ^ 40 * 3220038 * 2
def baseEnd_3220038 : Nat := 1653427219742377820216321

theorem tailTrace_3220038 : CollatzResearch.WordTrace tailWord_3220038 prefixEnd_3220038 1653427219742377820216321 := by
  unfold tailWord_3220038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670138572136241861020399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78296289538906493035101845 3670138572136241861020399)
  ·
    refine ⟨5505207858204362791530599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3670138572136241861020399 5505207858204362791530599)
    ·
      refine ⟨8257811787306544187295899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505207858204362791530599 8257811787306544187295899)
      ·
        refine ⟨12386717680959816280943849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257811787306544187295899 12386717680959816280943849)
        ·
          refine ⟨9290038260719862210707887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12386717680959816280943849 9290038260719862210707887)
          ·
            refine ⟨13935057391079793316061831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290038260719862210707887 13935057391079793316061831)
            ·
              refine ⟨20902586086619689974092747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935057391079793316061831 20902586086619689974092747)
              ·
                refine ⟨31353879129929534961139121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20902586086619689974092747 31353879129929534961139121)
                ·
                  refine ⟨23515409347447151220854341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31353879129929534961139121 23515409347447151220854341)
                  ·
                    refine ⟨4409139252646340853910189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23515409347447151220854341 4409139252646340853910189)
                    ·
                      refine ⟨1653427219742377820216321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409139252646340853910189 1653427219742377820216321)
                      ·
                        rfl

theorem cell23_3220038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3220038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220038 prefixEnd_3220038 := by exact prefixLift 3220038
  have htrace : WordTrace (prefixWord ++ tailWord_3220038) baseStart_3220038 baseEnd_3220038 := by
    simpa [prefixWord, tailWord_3220038, baseEnd_3220038] using wordTrace_append hprefix tailTrace_3220038
  have hstable : (prefixWord ++ tailWord_3220038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220038).length < 2 ^ (prefixWord ++ tailWord_3220038).sum := by decide
  have hdescent : baseEnd_3220038 < baseStart_3220038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220101 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_3220101 : Nat := 118140960795 + 3220101 * 2 ^ 59
def prefixEnd_3220101 : Nat := 4983230072969 + 3 ^ 40 * 3220101 * 2
def baseEnd_3220101 : Nat := 551153189674537024576177

theorem tailTrace_3220101 : CollatzResearch.WordTrace tailWord_3220101 prefixEnd_3220101 551153189674537024576177 := by
  unfold tailWord_3220101
  simp only [CollatzResearch.WordTrace]
  refine ⟨117446732107131501312196157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78297821404754334208130771 117446732107131501312196157)
  ·
    refine ⟨44042524540174312992073559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117446732107131501312196157 44042524540174312992073559)
    ·
      refine ⟨66063786810261469488110339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44042524540174312992073559 66063786810261469488110339)
      ·
        refine ⟨99095680215392204232165509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66063786810261469488110339 99095680215392204232165509)
        ·
          refine ⟨18580440040386038293531033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99095680215392204232165509 18580440040386038293531033)
          ·
            refine ⟨13935330030289528720148275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18580440040386038293531033 13935330030289528720148275)
            ·
              refine ⟨20902995045434293080222413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935330030289528720148275 20902995045434293080222413)
              ·
                refine ⟨7838623142037859905083405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20902995045434293080222413 7838623142037859905083405)
                ·
                  refine ⟨2939483678264197464406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7838623142037859905083405 2939483678264197464406277)
                  ·
                    refine ⟨551153189674537024576177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939483678264197464406277 551153189674537024576177)
                    ·
                      rfl

theorem cell23_3220101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_3220101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220101 prefixEnd_3220101 := by exact prefixLift 3220101
  have htrace : WordTrace (prefixWord ++ tailWord_3220101) baseStart_3220101 baseEnd_3220101 := by
    simpa [prefixWord, tailWord_3220101, baseEnd_3220101] using wordTrace_append hprefix tailTrace_3220101
  have hstable : (prefixWord ++ tailWord_3220101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220101).length < 2 ^ (prefixWord ++ tailWord_3220101).sum := by decide
  have hdescent : baseEnd_3220101 < baseStart_3220101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220144 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_3220144 : Nat := 118140960795 + 3220144 * 2 ^ 59
def prefixEnd_3220144 : Nat := 4983230072969 + 3 ^ 40 * 3220144 * 2
def baseEnd_3220144 : Nat := 551160549563918135163611

theorem tailTrace_3220144 : CollatzResearch.WordTrace tailWord_3220144 prefixEnd_3220144 551160549563918135163611 := by
  unfold tailWord_3220144
  simp only [CollatzResearch.WordTrace]
  refine ⟨58724150222987859828005743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78298866963983813104007657 58724150222987859828005743)
  ·
    refine ⟨88086225334481789742008615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58724150222987859828005743 88086225334481789742008615)
    ·
      refine ⟨132129338001722684613012923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88086225334481789742008615 132129338001722684613012923)
      ·
        refine ⟨198194007002584026919519385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132129338001722684613012923 198194007002584026919519385)
        ·
          refine ⟨148645505251938020189639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198194007002584026919519385 148645505251938020189639539)
          ·
            refine ⟨222968257877907030284459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148645505251938020189639539 222968257877907030284459309)
            ·
              refine ⟨83613096704215136356672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222968257877907030284459309 83613096704215136356672241)
              ·
                refine ⟨62709822528161352267504181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83613096704215136356672241 62709822528161352267504181)
                ·
                  refine ⟨5879045862015126775078517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62709822528161352267504181 5879045862015126775078517)
                  ·
                    refine ⟨551160549563918135163611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5879045862015126775078517 551160549563918135163611)
                    ·
                      rfl

theorem cell23_3220144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_3220144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220144 prefixEnd_3220144 := by exact prefixLift 3220144
  have htrace : WordTrace (prefixWord ++ tailWord_3220144) baseStart_3220144 baseEnd_3220144 := by
    simpa [prefixWord, tailWord_3220144, baseEnd_3220144] using wordTrace_append hprefix tailTrace_3220144
  have hstable : (prefixWord ++ tailWord_3220144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220144).length < 2 ^ (prefixWord ++ tailWord_3220144).sum := by decide
  have hdescent : baseEnd_3220144 < baseStart_3220144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220145 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3220145 : Nat := 118140960795 + 3220145 * 2 ^ 59
def prefixEnd_3220145 : Nat := 4983230072969 + 3 ^ 40 * 3220145 * 2
def baseEnd_3220145 : Nat := 1653482162172408901578329

theorem tailTrace_3220145 : CollatzResearch.WordTrace tailWord_3220145 prefixEnd_3220145 1653482162172408901578329 := by
  unfold tailWord_3220145
  simp only [CollatzResearch.WordTrace]
  refine ⟨117448336918972096826797889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78298891279314731217865259 117448336918972096826797889)
  ·
    refine ⟨88086252689229072620098417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117448336918972096826797889 88086252689229072620098417)
    ·
      refine ⟨66064689516921804465073813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88086252689229072620098417 66064689516921804465073813)
      ·
        refine ⟨3096782321105709584300335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66064689516921804465073813 3096782321105709584300335)
        ·
          refine ⟨4645173481658564376450503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096782321105709584300335 4645173481658564376450503)
          ·
            refine ⟨6967760222487846564675755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645173481658564376450503 6967760222487846564675755)
            ·
              refine ⟨10451640333731769847013633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967760222487846564675755 10451640333731769847013633)
              ·
                refine ⟨7838730250298827385260225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10451640333731769847013633 7838730250298827385260225)
                ·
                  refine ⟨5879047687724120538945169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7838730250298827385260225 5879047687724120538945169)
                  ·
                    refine ⟨4409285765793090404208877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879047687724120538945169 4409285765793090404208877)
                    ·
                      refine ⟨1653482162172408901578329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409285765793090404208877 1653482162172408901578329)
                      ·
                        rfl

theorem cell23_3220145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3220145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220145 prefixEnd_3220145 := by exact prefixLift 3220145
  have htrace : WordTrace (prefixWord ++ tailWord_3220145) baseStart_3220145 baseEnd_3220145 := by
    simpa [prefixWord, tailWord_3220145, baseEnd_3220145] using wordTrace_append hprefix tailTrace_3220145
  have hstable : (prefixWord ++ tailWord_3220145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220145).length < 2 ^ (prefixWord ++ tailWord_3220145).sum := by decide
  have hdescent : baseEnd_3220145 < baseStart_3220145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220178 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3220178 : Nat := 118140960795 + 3220178 * 2 ^ 59
def prefixEnd_3220178 : Nat := 4983230072969 + 3 ^ 40 * 3220178 * 2
def baseEnd_3220178 : Nat := 551166369011335757488559

theorem tailTrace_3220178 : CollatzResearch.WordTrace tailWord_3220178 prefixEnd_3220178 551166369011335757488559 := by
  unfold tailWord_3220178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29362385131963135865687297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78299693685235028975166125 29362385131963135865687297)
  ·
    refine ⟨22021788848972351899265473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29362385131963135865687297 22021788848972351899265473)
    ·
      refine ⟨16516341636729263924449105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22021788848972351899265473 16516341636729263924449105)
      ·
        refine ⟨12387256227546947943336829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16516341636729263924449105 12387256227546947943336829)
        ·
          refine ⟨4645221085330105478751311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12387256227546947943336829 4645221085330105478751311)
          ·
            refine ⟨6967831627995158218126967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645221085330105478751311 6967831627995158218126967)
            ·
              refine ⟨10451747441992737327190451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967831627995158218126967 10451747441992737327190451)
              ·
                refine ⟨15677621162989105990785677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451747441992737327190451 15677621162989105990785677)
                ·
                  refine ⟨5879107936120914746544629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15677621162989105990785677 5879107936120914746544629)
                  ·
                    refine ⟨551166369011335757488559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5879107936120914746544629 551166369011335757488559)
                    ·
                      rfl

theorem cell23_3220178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3220178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220178 prefixEnd_3220178 := by exact prefixLift 3220178
  have htrace : WordTrace (prefixWord ++ tailWord_3220178) baseStart_3220178 baseEnd_3220178 := by
    simpa [prefixWord, tailWord_3220178, baseEnd_3220178] using wordTrace_append hprefix tailTrace_3220178
  have hstable : (prefixWord ++ tailWord_3220178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220178).length < 2 ^ (prefixWord ++ tailWord_3220178).sum := by decide
  have hdescent : baseEnd_3220178 < baseStart_3220178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220191 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 6]
def baseStart_3220191 : Nat := 118140960795 + 3220191 * 2 ^ 59
def prefixEnd_3220191 : Nat := 4983230072969 + 3 ^ 40 * 3220191 * 2
def baseEnd_3220191 : Nat := 551168594094171907201039

theorem tailTrace_3220191 : CollatzResearch.WordTrace tailWord_3220191 prefixEnd_3220191 551168594094171907201039 := by
  unfold tailWord_3220191
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450014676805446682972427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78300009784536964455314951 117450014676805446682972427)
  ·
    refine ⟨176175022015208170024458641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117450014676805446682972427 176175022015208170024458641)
    ·
      refine ⟨132131266511406127518343981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176175022015208170024458641 132131266511406127518343981)
      ·
        refine ⟨49549224941777297819378993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132131266511406127518343981 49549224941777297819378993)
        ·
          refine ⟨37161918706332973364534245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49549224941777297819378993 37161918706332973364534245)
          ·
            refine ⟨6967859757437432505850171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37161918706332973364534245 6967859757437432505850171)
            ·
              refine ⟨10451789636156148758775257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967859757437432505850171 10451789636156148758775257)
              ·
                refine ⟨7838842227117111569081443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10451789636156148758775257 7838842227117111569081443)
                ·
                  refine ⟨11758263340675667353622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838842227117111569081443 11758263340675667353622165)
                  ·
                    refine ⟨551168594094171907201039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11758263340675667353622165 551168594094171907201039)
                    ·
                      rfl

theorem cell23_3220191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_3220191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220191 prefixEnd_3220191 := by exact prefixLift 3220191
  have htrace : WordTrace (prefixWord ++ tailWord_3220191) baseStart_3220191 baseEnd_3220191 := by
    simpa [prefixWord, tailWord_3220191, baseEnd_3220191] using wordTrace_append hprefix tailTrace_3220191
  have hstable : (prefixWord ++ tailWord_3220191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220191).length < 2 ^ (prefixWord ++ tailWord_3220191).sum := by decide
  have hdescent : baseEnd_3220191 < baseStart_3220191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220195 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 1, 5]
def baseStart_3220195 : Nat := 118140960795 + 3220195 * 2 ^ 59
def prefixEnd_3220195 : Nat := 4983230072969 + 3 ^ 40 * 3220195 * 2
def baseEnd_3220195 : Nat := 551169278735044568651033

theorem tailTrace_3220195 : CollatzResearch.WordTrace tailWord_3220195 prefixEnd_3220195 551169278735044568651033 := by
  unfold tailWord_3220195
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450160568790955366118039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78300107045860636910745359 117450160568790955366118039)
  ·
    refine ⟨176175240853186433049177059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117450160568790955366118039 176175240853186433049177059)
    ·
      refine ⟨264262861279779649573765589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176175240853186433049177059 264262861279779649573765589)
      ·
        refine ⟨6193660811244835536885131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 264262861279779649573765589 6193660811244835536885131)
        ·
          refine ⟨9290491216867253305327697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193660811244835536885131 9290491216867253305327697)
          ·
            refine ⟨6967868412650439978995773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9290491216867253305327697 6967868412650439978995773)
            ·
              refine ⟨2612950654743914992123415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6967868412650439978995773 2612950654743914992123415)
              ·
                refine ⟨3919425982115872488185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612950654743914992123415 3919425982115872488185123)
                ·
                  refine ⟨5879138973173808732277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919425982115872488185123 5879138973173808732277685)
                  ·
                    refine ⟨551169278735044568651033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5879138973173808732277685 551169278735044568651033)
                    ·
                      rfl

theorem cell23_3220195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 5].length) (baseStart_3220195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220195 prefixEnd_3220195 := by exact prefixLift 3220195
  have htrace : WordTrace (prefixWord ++ tailWord_3220195) baseStart_3220195 baseEnd_3220195 := by
    simpa [prefixWord, tailWord_3220195, baseEnd_3220195] using wordTrace_append hprefix tailTrace_3220195
  have hstable : (prefixWord ++ tailWord_3220195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220195).length < 2 ^ (prefixWord ++ tailWord_3220195).sum := by decide
  have hdescent : baseEnd_3220195 < baseStart_3220195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220201 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_3220201 : Nat := 118140960795 + 3220201 * 2 ^ 59
def prefixEnd_3220201 : Nat := 4983230072969 + 3 ^ 40 * 3220201 * 2
def baseEnd_3220201 : Nat := 1653510917089060682478071

theorem tailTrace_3220201 : CollatzResearch.WordTrace tailWord_3220201 prefixEnd_3220201 1653510917089060682478071 := by
  unfold tailWord_3220201
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450379406769218390836457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78300252937846145593890971 117450379406769218390836457)
  ·
    refine ⟨88087784555076913793127343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117450379406769218390836457 88087784555076913793127343)
    ·
      refine ⟨132131676832615370689691015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88087784555076913793127343 132131676832615370689691015)
      ·
        refine ⟨198197515248923056034536523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132131676832615370689691015 198197515248923056034536523)
        ·
          refine ⟨297296272873384584051804785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198197515248923056034536523 297296272873384584051804785)
          ·
            refine ⟨222972204655038438038853589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297296272873384584051804785 222972204655038438038853589)
            ·
              refine ⟨5225911046602463391535631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 222972204655038438038853589 5225911046602463391535631)
              ·
                refine ⟨7838866569903695087303447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225911046602463391535631 7838866569903695087303447)
                ·
                  refine ⟨11758299854855542630955171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838866569903695087303447 11758299854855542630955171)
                  ·
                    refine ⟨17637449782283313946432757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11758299854855542630955171 17637449782283313946432757)
                    ·
                      refine ⟨1653510917089060682478071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17637449782283313946432757 1653510917089060682478071)
                      ·
                        rfl

theorem cell23_3220201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_3220201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220201 prefixEnd_3220201 := by exact prefixLift 3220201
  have htrace : WordTrace (prefixWord ++ tailWord_3220201) baseStart_3220201 baseEnd_3220201 := by
    simpa [prefixWord, tailWord_3220201, baseEnd_3220201] using wordTrace_append hprefix tailTrace_3220201
  have hstable : (prefixWord ++ tailWord_3220201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220201).length < 2 ^ (prefixWord ++ tailWord_3220201).sum := by decide
  have hdescent : baseEnd_3220201 < baseStart_3220201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220208 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_3220208 : Nat := 118140960795 + 3220208 * 2 ^ 59
def prefixEnd_3220208 : Nat := 4983230072969 + 3 ^ 40 * 3220208 * 2
def baseEnd_3220208 : Nat := 551171503817880718363513

theorem tailTrace_3220208 : CollatzResearch.WordTrace tailWord_3220208 prefixEnd_3220208 551171503817880718363513 := by
  unfold tailWord_3220208
  simp only [CollatzResearch.WordTrace]
  refine ⟨58725317358871929293170639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78300423145162572390894185 58725317358871929293170639)
  ·
    refine ⟨88087976038307893939755959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58725317358871929293170639 88087976038307893939755959)
    ·
      refine ⟨132131964057461840909633939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88087976038307893939755959 132131964057461840909633939)
      ·
        refine ⟨198197946086192761364450909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132131964057461840909633939 198197946086192761364450909)
        ·
          refine ⟨74324229782322285511669091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198197946086192761364450909 74324229782322285511669091)
          ·
            refine ⟨111486344673483428267503637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74324229782322285511669091 111486344673483428267503637)
            ·
              refine ⟨5225922406569535700039233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111486344673483428267503637 5225922406569535700039233)
              ·
                refine ⟨3919441804927151775029425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225922406569535700039233 3919441804927151775029425)
                ·
                  refine ⟨2939581353695363831272069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3919441804927151775029425 2939581353695363831272069)
                  ·
                    refine ⟨551171503817880718363513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939581353695363831272069 551171503817880718363513)
                    ·
                      rfl

theorem cell23_3220208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_3220208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220208 prefixEnd_3220208 := by exact prefixLift 3220208
  have htrace : WordTrace (prefixWord ++ tailWord_3220208) baseStart_3220208 baseEnd_3220208 := by
    simpa [prefixWord, tailWord_3220208, baseEnd_3220208] using wordTrace_append hprefix tailTrace_3220208
  have hstable : (prefixWord ++ tailWord_3220208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220208).length < 2 ^ (prefixWord ++ tailWord_3220208).sum := by decide
  have hdescent : baseEnd_3220208 < baseStart_3220208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220228 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3220228 : Nat := 118140960795 + 3220228 * 2 ^ 59
def prefixEnd_3220228 : Nat := 4983230072969 + 3 ^ 40 * 3220228 * 2
def baseEnd_3220228 : Nat := 1653524781066732076840447

theorem tailTrace_3220228 : CollatzResearch.WordTrace tailWord_3220228 prefixEnd_3220228 1653524781066732076840447 := by
  unfold tailWord_3220228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58725682088835701001034669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78300909451780934668046225 58725682088835701001034669)
  ·
    refine ⟨22022130783313387875388001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58725682088835701001034669 22022130783313387875388001)
    ·
      refine ⟨16516598087485040906541001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22022130783313387875388001 16516598087485040906541001)
      ·
        refine ⟨12387448565613780679905751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16516598087485040906541001 12387448565613780679905751)
        ·
          refine ⟨18581172848420671019858627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387448565613780679905751 18581172848420671019858627)
          ·
            refine ⟨27871759272631006529787941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18581172848420671019858627 27871759272631006529787941)
            ·
              refine ⟨5225954863618313724335239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27871759272631006529787941 5225954863618313724335239)
              ·
                refine ⟨7838932295427470586502859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225954863618313724335239 7838932295427470586502859)
                ·
                  refine ⟨11758398443141205879754289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838932295427470586502859 11758398443141205879754289)
                  ·
                    refine ⟨8818798832355904409815717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11758398443141205879754289 8818798832355904409815717)
                    ·
                      refine ⟨1653524781066732076840447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8818798832355904409815717 1653524781066732076840447)
                      ·
                        rfl

theorem cell23_3220228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3220228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220228 prefixEnd_3220228 := by exact prefixLift 3220228
  have htrace : WordTrace (prefixWord ++ tailWord_3220228) baseStart_3220228 baseEnd_3220228 := by
    simpa [prefixWord, tailWord_3220228, baseEnd_3220228] using wordTrace_append hprefix tailTrace_3220228
  have hstable : (prefixWord ++ tailWord_3220228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220228).length < 2 ^ (prefixWord ++ tailWord_3220228).sum := by decide
  have hdescent : baseEnd_3220228 < baseStart_3220228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220248 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3220248 : Nat := 118140960795 + 3220248 * 2 ^ 59
def prefixEnd_3220248 : Nat := 4983230072969 + 3 ^ 40 * 3220248 * 2
def baseEnd_3220248 : Nat := 1653535050679821998590355

theorem tailTrace_3220248 : CollatzResearch.WordTrace tailWord_3220248 prefixEnd_3220248 1653535050679821998590355 := by
  unfold tailWord_3220248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58726046818799472708898699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78301395758399296945198265 58726046818799472708898699)
  ·
    refine ⟨88089070228199209063348049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58726046818799472708898699 88089070228199209063348049)
    ·
      refine ⟨66066802671149406797511037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88089070228199209063348049 66066802671149406797511037)
      ·
        refine ⟨24775051001681027549066639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66066802671149406797511037 24775051001681027549066639)
        ·
          refine ⟨37162576502521541323599959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24775051001681027549066639 37162576502521541323599959)
          ·
            refine ⟨55743864753782311985399939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37162576502521541323599959 55743864753782311985399939)
            ·
              refine ⟨83615797130673467978099909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55743864753782311985399939 83615797130673467978099909)
              ·
                refine ⟨15677961962001275245893733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83615797130673467978099909 15677961962001275245893733)
                ·
                  refine ⟨2939617867875239108605075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15677961962001275245893733 2939617867875239108605075)
                  ·
                    refine ⟨4409426801812858662907613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2939617867875239108605075 4409426801812858662907613)
                    ·
                      refine ⟨1653535050679821998590355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409426801812858662907613 1653535050679821998590355)
                      ·
                        rfl

theorem cell23_3220248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3220248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220248 prefixEnd_3220248 := by exact prefixLift 3220248
  have htrace : WordTrace (prefixWord ++ tailWord_3220248) baseStart_3220248 baseEnd_3220248 := by
    simpa [prefixWord, tailWord_3220248, baseEnd_3220248] using wordTrace_append hprefix tailTrace_3220248
  have hstable : (prefixWord ++ tailWord_3220248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220248).length < 2 ^ (prefixWord ++ tailWord_3220248).sum := by decide
  have hdescent : baseEnd_3220248 < baseStart_3220248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220252 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3220252 : Nat := 118140960795 + 3220252 * 2 ^ 59
def prefixEnd_3220252 : Nat := 4983230072969 + 3 ^ 40 * 3220252 * 2
def baseEnd_3220252 : Nat := 1653537104602439982940337

theorem tailTrace_3220252 : CollatzResearch.WordTrace tailWord_3220252 prefixEnd_3220252 1653537104602439982940337 := by
  unfold tailWord_3220252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58726119764792227050471505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78301493019722969400628673 58726119764792227050471505)
  ·
    refine ⟨44044589823594170287853629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58726119764792227050471505 44044589823594170287853629)
    ·
      refine ⟨16516721183847813857945111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44044589823594170287853629 16516721183847813857945111)
      ·
        refine ⟨24775081775771720786917667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16516721183847813857945111 24775081775771720786917667)
        ·
          refine ⟨37162622663657581180376501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24775081775771720786917667 37162622663657581180376501)
          ·
            refine ⟨3483995874717898235660297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37162622663657581180376501 3483995874717898235660297)
            ·
              refine ⟨2612996906038423676745223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483995874717898235660297 2612996906038423676745223)
              ·
                refine ⟨3919495359057635515117835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612996906038423676745223 3919495359057635515117835)
                ·
                  refine ⟨5879243038586453272676753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919495359057635515117835 5879243038586453272676753)
                  ·
                    refine ⟨4409432278939839954507565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879243038586453272676753 4409432278939839954507565)
                    ·
                      refine ⟨1653537104602439982940337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409432278939839954507565 1653537104602439982940337)
                      ·
                        rfl

theorem cell23_3220252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3220252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220252 prefixEnd_3220252 := by exact prefixLift 3220252
  have htrace : WordTrace (prefixWord ++ tailWord_3220252) baseStart_3220252 baseEnd_3220252 := by
    simpa [prefixWord, tailWord_3220252, baseEnd_3220252] using wordTrace_append hprefix tailTrace_3220252
  have hstable : (prefixWord ++ tailWord_3220252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220252).length < 2 ^ (prefixWord ++ tailWord_3220252).sum := by decide
  have hdescent : baseEnd_3220252 < baseStart_3220252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220282 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_3220282 : Nat := 118140960795 + 3220282 * 2 ^ 59
def prefixEnd_3220282 : Nat := 4983230072969 + 3 ^ 40 * 3220282 * 2
def baseEnd_3220282 : Nat := 1653552509022074865565199

theorem tailTrace_3220282 : CollatzResearch.WordTrace tailWord_3220282 prefixEnd_3220282 1653552509022074865565199 := by
  unfold tailWord_3220282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363333429868942306133775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78302222479650512816356733 29363333429868942306133775)
  ·
    refine ⟨44045000144803413459200663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29363333429868942306133775 44045000144803413459200663)
    ·
      refine ⟨66067500217205120188800995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44045000144803413459200663 66067500217205120188800995)
      ·
        refine ⟨99101250325807680283201493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66067500217205120188800995 99101250325807680283201493)
        ·
          refine ⟨2322685554511117506637535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99101250325807680283201493 2322685554511117506637535)
          ·
            refine ⟨3484028331766676259956303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322685554511117506637535 3484028331766676259956303)
            ·
              refine ⟨5226042497650014389934455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484028331766676259956303 5226042497650014389934455)
              ·
                refine ⟨7839063746475021584901683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226042497650014389934455 7839063746475021584901683)
                ·
                  refine ⟨11758595619712532377352525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839063746475021584901683 11758595619712532377352525)
                  ·
                    refine ⟨4409473357392199641507197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11758595619712532377352525 4409473357392199641507197)
                    ·
                      refine ⟨1653552509022074865565199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409473357392199641507197 1653552509022074865565199)
                      ·
                        rfl

theorem cell23_3220282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_3220282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220282 prefixEnd_3220282 := by exact prefixLift 3220282
  have htrace : WordTrace (prefixWord ++ tailWord_3220282) baseStart_3220282 baseEnd_3220282 := by
    simpa [prefixWord, tailWord_3220282, baseEnd_3220282] using wordTrace_append hprefix tailTrace_3220282
  have hstable : (prefixWord ++ tailWord_3220282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220282).length < 2 ^ (prefixWord ++ tailWord_3220282).sum := by decide
  have hdescent : baseEnd_3220282 < baseStart_3220282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220291 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_3220291 : Nat := 118140960795 + 3220291 * 2 ^ 59
def prefixEnd_3220291 : Nat := 4983230072969 + 3 ^ 40 * 3220291 * 2
def baseEnd_3220291 : Nat := 1653557130347965330352657

theorem tailTrace_3220291 : CollatzResearch.WordTrace tailWord_3220291 prefixEnd_3220291 1653557130347965330352657 := by
  unfold tailWord_3220291
  simp only [CollatzResearch.WordTrace]
  refine ⟨117453661976443163761612727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78302441317628775841075151 117453661976443163761612727)
  ·
    refine ⟨176180492964664745642419091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117453661976443163761612727 176180492964664745642419091)
    ·
      refine ⟨264270739446997118463628637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176180492964664745642419091 264270739446997118463628637)
      ·
        refine ⟨99101527292623919423860739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264270739446997118463628637 99101527292623919423860739)
        ·
          refine ⟨148652290938935879135791109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99101527292623919423860739 148652290938935879135791109)
          ·
            refine ⟨27872304551050477337960833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148652290938935879135791109 27872304551050477337960833)
            ·
              refine ⟨20904228413287858003470625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27872304551050477337960833 20904228413287858003470625)
              ·
                refine ⟨15678171309965893502602969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20904228413287858003470625 15678171309965893502602969)
                ·
                  refine ⟨11758628482474420126952227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15678171309965893502602969 11758628482474420126952227)
                  ·
                    refine ⟨17637942723711630190428341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11758628482474420126952227 17637942723711630190428341)
                    ·
                      refine ⟨1653557130347965330352657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17637942723711630190428341 1653557130347965330352657)
                      ·
                        rfl

theorem cell23_3220291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_3220291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220291 prefixEnd_3220291 := by exact prefixLift 3220291
  have htrace : WordTrace (prefixWord ++ tailWord_3220291) baseStart_3220291 baseEnd_3220291 := by
    simpa [prefixWord, tailWord_3220291, baseEnd_3220291] using wordTrace_append hprefix tailTrace_3220291
  have hstable : (prefixWord ++ tailWord_3220291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220291).length < 2 ^ (prefixWord ++ tailWord_3220291).sum := by decide
  have hdescent : baseEnd_3220291 < baseStart_3220291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220328 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 7]
def baseStart_3220328 : Nat := 118140960795 + 3220328 * 2 ^ 59
def prefixEnd_3220328 : Nat := 4983230072969 + 3 ^ 40 * 3220328 * 2
def baseEnd_3220328 : Nat := 183730681014686853954443

theorem tailTrace_3220328 : CollatzResearch.WordTrace tailWord_3220328 prefixEnd_3220328 183730681014686853954443 := by
  unfold tailWord_3220328
  simp only [CollatzResearch.WordTrace]
  refine ⟨58727505738654559540354819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78303340984872746053806425 58727505738654559540354819)
  ·
    refine ⟨88091258607981839310532229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58727505738654559540354819 88091258607981839310532229)
    ·
      refine ⟨16517110988996594870724793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88091258607981839310532229 16517110988996594870724793)
      ·
        refine ⟨12387833241747446153043595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16517110988996594870724793 12387833241747446153043595)
        ·
          refine ⟨18581749862621169229565393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387833241747446153043595 18581749862621169229565393)
          ·
            refine ⟨13936312396965876922174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18581749862621169229565393 13936312396965876922174045)
            ·
              refine ⟨5226117148862203845815267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13936312396965876922174045 5226117148862203845815267)
              ·
                refine ⟨7839175723293305768722901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226117148862203845815267 7839175723293305768722901)
                ·
                  refine ⟨183730681014686853954443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7839175723293305768722901 183730681014686853954443)
                  ·
                    rfl

theorem cell23_3220328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_3220328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220328 prefixEnd_3220328 := by exact prefixLift 3220328
  have htrace : WordTrace (prefixWord ++ tailWord_3220328) baseStart_3220328 baseEnd_3220328 := by
    simpa [prefixWord, tailWord_3220328, baseEnd_3220328] using wordTrace_append hprefix tailTrace_3220328
  have hstable : (prefixWord ++ tailWord_3220328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220328).length < 2 ^ (prefixWord ++ tailWord_3220328).sum := by decide
  have hdescent : baseEnd_3220328 < baseStart_3220328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220338 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3220338 : Nat := 118140960795 + 3220338 * 2 ^ 59
def prefixEnd_3220338 : Nat := 4983230072969 + 3 ^ 40 * 3220338 * 2
def baseEnd_3220338 : Nat := 1653581263938726646464941

theorem tailTrace_3220338 : CollatzResearch.WordTrace tailWord_3220338 prefixEnd_3220338 1653581263938726646464941 := by
  unfold tailWord_3220338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363844051818222697143417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78303584138181927192382445 29363844051818222697143417)
  ·
    refine ⟨22022883038863667022857563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29363844051818222697143417 22022883038863667022857563)
    ·
      refine ⟨33034324558295500534286345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22022883038863667022857563 33034324558295500534286345)
      ·
        refine ⟨24775743418721625400714759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33034324558295500534286345 24775743418721625400714759)
        ·
          refine ⟨37163615128082438101072139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24775743418721625400714759 37163615128082438101072139)
          ·
            refine ⟨55745422692123657151608209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37163615128082438101072139 55745422692123657151608209)
            ·
              refine ⟨41809067019092742863706157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55745422692123657151608209 41809067019092742863706157)
              ·
                refine ⟨15678400132159778573889809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41809067019092742863706157 15678400132159778573889809)
                ·
                  refine ⟨11758800099119833930417357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15678400132159778573889809 11758800099119833930417357)
                  ·
                    refine ⟨4409550037169937723906509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11758800099119833930417357 4409550037169937723906509)
                    ·
                      refine ⟨1653581263938726646464941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4409550037169937723906509 1653581263938726646464941)
                      ·
                        rfl

theorem cell23_3220338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3220338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220338 prefixEnd_3220338 := by exact prefixLift 3220338
  have htrace : WordTrace (prefixWord ++ tailWord_3220338) baseStart_3220338 baseEnd_3220338 := by
    simpa [prefixWord, tailWord_3220338, baseEnd_3220338] using wordTrace_append hprefix tailTrace_3220338
  have hstable : (prefixWord ++ tailWord_3220338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220338).length < 2 ^ (prefixWord ++ tailWord_3220338).sum := by decide
  have hdescent : baseEnd_3220338 < baseStart_3220338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220405 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3220405 : Nat := 118140960795 + 3220405 * 2 ^ 59
def prefixEnd_3220405 : Nat := 4983230072969 + 3 ^ 40 * 3220405 * 2
def baseEnd_3220405 : Nat := 551205222380859294775711

theorem tailTrace_3220405 : CollatzResearch.WordTrace tailWord_3220405 prefixEnd_3220405 551205222380859294775711 := by
  unfold tailWord_3220405
  simp only [CollatzResearch.WordTrace]
  refine ⟨117457819898030161231262669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78305213265353440820841779 117457819898030161231262669)
  ·
    refine ⟨44046682461761310461723501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117457819898030161231262669 44046682461761310461723501)
    ·
      refine ⟨16517505923160491423146313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44046682461761310461723501 16517505923160491423146313)
      ·
        refine ⟨12388129442370368567359735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16517505923160491423146313 12388129442370368567359735)
        ·
          refine ⟨18582194163555552851039603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388129442370368567359735 18582194163555552851039603)
          ·
            refine ⟨27873291245333329276559405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18582194163555552851039603 27873291245333329276559405)
            ·
              refine ⟨10452484216999998478709777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27873291245333329276559405 10452484216999998478709777)
              ·
                refine ⟨7839363162749998859032333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10452484216999998478709777 7839363162749998859032333)
                ·
                  refine ⟨2939761186031249572137125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7839363162749998859032333 2939761186031249572137125)
                  ·
                    refine ⟨551205222380859294775711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939761186031249572137125 551205222380859294775711)
                    ·
                      rfl

theorem cell23_3220405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3220405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220405 prefixEnd_3220405 := by exact prefixLift 3220405
  have htrace : WordTrace (prefixWord ++ tailWord_3220405) baseStart_3220405 baseEnd_3220405 := by
    simpa [prefixWord, tailWord_3220405, baseEnd_3220405] using wordTrace_append hprefix tailTrace_3220405
  have hstable : (prefixWord ++ tailWord_3220405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220405).length < 2 ^ (prefixWord ++ tailWord_3220405).sum := by decide
  have hdescent : baseEnd_3220405 < baseStart_3220405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220465 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_3220465 : Nat := 118140960795 + 3220465 * 2 ^ 59
def prefixEnd_3220465 : Nat := 4983230072969 + 3 ^ 40 * 3220465 * 2
def baseEnd_3220465 : Nat := 551215491993949216525619

theorem tailTrace_3220465 : CollatzResearch.WordTrace tailWord_3220465 prefixEnd_3220465 551215491993949216525619 := by
  unfold tailWord_3220465
  simp only [CollatzResearch.WordTrace]
  refine ⟨117460008277812791478446849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78306672185208527652297899 117460008277812791478446849)
  ·
    refine ⟨88095006208359593608835137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117460008277812791478446849 88095006208359593608835137)
    ·
      refine ⟨66071254656269695206626353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88095006208359593608835137 66071254656269695206626353)
      ·
        refine ⟨49553440992202271404969765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66071254656269695206626353 49553440992202271404969765)
        ·
          refine ⟨9291270186037925888431831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49553440992202271404969765 9291270186037925888431831)
          ·
            refine ⟨13936905279056888832647747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291270186037925888431831 13936905279056888832647747)
            ·
              refine ⟨20905357918585333248971621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936905279056888832647747 20905357918585333248971621)
              ·
                refine ⟨3919754609734749984182179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20905357918585333248971621 3919754609734749984182179)
                ·
                  refine ⟨5879631914602124976273269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919754609734749984182179 5879631914602124976273269)
                  ·
                    refine ⟨551215491993949216525619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5879631914602124976273269 551215491993949216525619)
                    ·
                      rfl

theorem cell23_3220465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_3220465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220465 prefixEnd_3220465 := by exact prefixLift 3220465
  have htrace : WordTrace (prefixWord ++ tailWord_3220465) baseStart_3220465 baseEnd_3220465 := by
    simpa [prefixWord, tailWord_3220465, baseEnd_3220465] using wordTrace_append hprefix tailTrace_3220465
  have hstable : (prefixWord ++ tailWord_3220465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220465).length < 2 ^ (prefixWord ++ tailWord_3220465).sum := by decide
  have hdescent : baseEnd_3220465 < baseStart_3220465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220485 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_3220485 : Nat := 118140960795 + 3220485 * 2 ^ 59
def prefixEnd_3220485 : Nat := 4983230072969 + 3 ^ 40 * 3220485 * 2
def baseEnd_3220485 : Nat := 1653656745594937571326765

theorem tailTrace_3220485 : CollatzResearch.WordTrace tailWord_3220485 prefixEnd_3220485 1653656745594937571326765 := by
  unfold tailWord_3220485
  simp only [CollatzResearch.WordTrace]
  refine ⟨117460737737740334894174909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78307158491826889929449939 117460737737740334894174909)
  ·
    refine ⟨44047776651652625585315591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117460737737740334894174909 44047776651652625585315591)
    ·
      refine ⟨66071664977478938377973387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44047776651652625585315591 66071664977478938377973387)
      ·
        refine ⟨99107497466218407566960081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66071664977478938377973387 99107497466218407566960081)
        ·
          refine ⟨74330623099663805675220061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99107497466218407566960081 74330623099663805675220061)
          ·
            refine ⟨27873983662373927128207523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74330623099663805675220061 27873983662373927128207523)
            ·
              refine ⟨41810975493560890692311285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27873983662373927128207523 41810975493560890692311285)
              ·
                refine ⟨3919778952521333502404183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41810975493560890692311285 3919778952521333502404183)
                ·
                  refine ⟨5879668428782000253606275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919778952521333502404183 5879668428782000253606275)
                  ·
                    refine ⟨8819502643173000380409413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5879668428782000253606275 8819502643173000380409413)
                    ·
                      refine ⟨1653656745594937571326765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819502643173000380409413 1653656745594937571326765)
                      ·
                        rfl

theorem cell23_3220485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_3220485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220485 prefixEnd_3220485 := by exact prefixLift 3220485
  have htrace : WordTrace (prefixWord ++ tailWord_3220485) baseStart_3220485 baseEnd_3220485 := by
    simpa [prefixWord, tailWord_3220485, baseEnd_3220485] using wordTrace_append hprefix tailTrace_3220485
  have hstable : (prefixWord ++ tailWord_3220485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220485).length < 2 ^ (prefixWord ++ tailWord_3220485).sum := by decide
  have hdescent : baseEnd_3220485 < baseStart_3220485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220519 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3220519 : Nat := 118140960795 + 3220519 * 2 ^ 59
def prefixEnd_3220519 : Nat := 4983230072969 + 3 ^ 40 * 3220519 * 2
def baseEnd_3220519 : Nat := 1653674203937190438301609

theorem tailTrace_3220519 : CollatzResearch.WordTrace tailWord_3220519 prefixEnd_3220519 1653674203937190438301609 := by
  unfold tailWord_3220519
  simp only [CollatzResearch.WordTrace]
  refine ⟨117461977819617158700912611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78307985213078105800608407 117461977819617158700912611)
  ·
    refine ⟨176192966729425738051368917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117461977819617158700912611 176192966729425738051368917)
    ·
      refine ⟨4129522657720915735578959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 176192966729425738051368917 4129522657720915735578959)
      ·
        refine ⟨6194283986581373603368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129522657720915735578959 6194283986581373603368439)
        ·
          refine ⟨9291425979872060405052659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194283986581373603368439 9291425979872060405052659)
          ·
            refine ⟨13937138969808090607578989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291425979872060405052659 13937138969808090607578989)
            ·
              refine ⟨5226427113678033977842121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13937138969808090607578989 5226427113678033977842121)
              ·
                refine ⟨3919820335258525483381591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5226427113678033977842121 3919820335258525483381591)
                ·
                  refine ⟨5879730502887788225072387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919820335258525483381591 5879730502887788225072387)
                  ·
                    refine ⟨8819595754331682337608581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5879730502887788225072387 8819595754331682337608581)
                    ·
                      refine ⟨1653674203937190438301609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819595754331682337608581 1653674203937190438301609)
                      ·
                        rfl

theorem cell23_3220519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3220519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220519 prefixEnd_3220519 := by exact prefixLift 3220519
  have htrace : WordTrace (prefixWord ++ tailWord_3220519) baseStart_3220519 baseEnd_3220519 := by
    simpa [prefixWord, tailWord_3220519, baseEnd_3220519] using wordTrace_append hprefix tailTrace_3220519
  have hstable : (prefixWord ++ tailWord_3220519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220519).length < 2 ^ (prefixWord ++ tailWord_3220519).sum := by decide
  have hdescent : baseEnd_3220519 < baseStart_3220519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220532 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3220532 : Nat := 118140960795 + 3220532 * 2 ^ 59
def prefixEnd_3220532 : Nat := 4983230072969 + 3 ^ 40 * 3220532 * 2
def baseEnd_3220532 : Nat := 1653680879185698887439049

theorem tailTrace_3220532 : CollatzResearch.WordTrace tailWord_3220532 prefixEnd_3220532 1653680879185698887439049 := by
  unfold tailWord_3220532
  simp only [CollatzResearch.WordTrace]
  refine ⟨58731225984285030960567925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78308301312380041280757233 58731225984285030960567925)
  ·
    refine ⟨5506052436026721652553243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58731225984285030960567925 5506052436026721652553243)
    ·
      refine ⟨8259078654040082478829865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5506052436026721652553243 8259078654040082478829865)
      ·
        refine ⟨6194308990530061859122399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8259078654040082478829865 6194308990530061859122399)
        ·
          refine ⟨9291463485795092788683599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194308990530061859122399 9291463485795092788683599)
          ·
            refine ⟨13937195228692639183025399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291463485795092788683599 13937195228692639183025399)
            ·
              refine ⟨20905792843038958774538099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13937195228692639183025399 20905792843038958774538099)
              ·
                refine ⟨31358689264558438161807149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20905792843038958774538099 31358689264558438161807149)
                ·
                  refine ⟨11759508474209414310677681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31358689264558438161807149 11759508474209414310677681)
                  ·
                    refine ⟨8819631355657060733008261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759508474209414310677681 8819631355657060733008261)
                    ·
                      refine ⟨1653680879185698887439049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819631355657060733008261 1653680879185698887439049)
                      ·
                        rfl

theorem cell23_3220532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3220532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220532 prefixEnd_3220532 := by exact prefixLift 3220532
  have htrace : WordTrace (prefixWord ++ tailWord_3220532) baseStart_3220532 baseEnd_3220532 := by
    simpa [prefixWord, tailWord_3220532, baseEnd_3220532] using wordTrace_append hprefix tailTrace_3220532
  have hstable : (prefixWord ++ tailWord_3220532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220532).length < 2 ^ (prefixWord ++ tailWord_3220532).sum := by decide
  have hdescent : baseEnd_3220532 < baseStart_3220532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220566 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3220566 : Nat := 118140960795 + 3220566 * 2 ^ 59
def prefixEnd_3220566 : Nat := 4983230072969 + 3 ^ 40 * 3220566 * 2
def baseEnd_3220566 : Nat := 1653698337527951754413893

theorem tailTrace_3220566 : CollatzResearch.WordTrace tailWord_3220566 prefixEnd_3220566 1653698337527951754413893 := by
  unfold tailWord_3220566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341480753152930357992097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78309128033631257151915701 7341480753152930357992097)
  ·
    refine ⟨5506110564864697768494073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341480753152930357992097 5506110564864697768494073)
    ·
      refine ⟨4129582923648523326370555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5506110564864697768494073 4129582923648523326370555)
      ·
        refine ⟨6194374385472784989555833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129582923648523326370555 6194374385472784989555833)
        ·
          refine ⟨4645780789104588742166875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194374385472784989555833 4645780789104588742166875)
          ·
            refine ⟨6968671183656883113250313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645780789104588742166875 6968671183656883113250313)
            ·
              refine ⟨5226503387742662334937735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6968671183656883113250313 5226503387742662334937735)
              ·
                refine ⟨7839755081613993502406603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226503387742662334937735 7839755081613993502406603)
                ·
                  refine ⟨11759632622420990253609905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839755081613993502406603 11759632622420990253609905)
                  ·
                    refine ⟨8819724466815742690207429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759632622420990253609905 8819724466815742690207429)
                    ·
                      refine ⟨1653698337527951754413893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819724466815742690207429 1653698337527951754413893)
                      ·
                        rfl

theorem cell23_3220566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3220566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220566 prefixEnd_3220566 := by exact prefixLift 3220566
  have htrace : WordTrace (prefixWord ++ tailWord_3220566) baseStart_3220566 baseEnd_3220566 := by
    simpa [prefixWord, tailWord_3220566, baseEnd_3220566] using wordTrace_append hprefix tailTrace_3220566
  have hstable : (prefixWord ++ tailWord_3220566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220566).length < 2 ^ (prefixWord ++ tailWord_3220566).sum := by decide
  have hdescent : baseEnd_3220566 < baseStart_3220566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220592 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2]
def baseStart_3220592 : Nat := 118140960795 + 3220592 * 2 ^ 59
def prefixEnd_3220592 : Nat := 4983230072969 + 3 ^ 40 * 3220592 * 2
def baseEnd_3220592 : Nat := 1653711688024968652688773

theorem tailTrace_3220592 : CollatzResearch.WordTrace tailWord_3220592 prefixEnd_3220592 1653711688024968652688773 := by
  unfold tailWord_3220592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58732320174176346084160015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78309760232235128112213353 58732320174176346084160015)
  ·
    refine ⟨88098480261264519126240023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58732320174176346084160015 88098480261264519126240023)
    ·
      refine ⟨132147720391896778689360035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88098480261264519126240023 132147720391896778689360035)
      ·
        refine ⟨198221580587845168034040053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132147720391896778689360035 198221580587845168034040053)
        ·
          refine ⟨18583273180110484503191255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198221580587845168034040053 18583273180110484503191255)
          ·
            refine ⟨27874909770165726754786883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18583273180110484503191255 27874909770165726754786883)
            ·
              refine ⟨41812364655248590132180325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27874909770165726754786883 41812364655248590132180325)
              ·
                refine ⟨7839818372859110649783811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41812364655248590132180325 7839818372859110649783811)
                ·
                  refine ⟨11759727559288665974675717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839818372859110649783811 11759727559288665974675717)
                  ·
                    refine ⟨2204948917366624870251697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11759727559288665974675717 2204948917366624870251697)
                    ·
                      refine ⟨1653711688024968652688773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204948917366624870251697 1653711688024968652688773)
                      ·
                        rfl

theorem cell23_3220592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 4, 2].length) (baseStart_3220592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220592 prefixEnd_3220592 := by exact prefixLift 3220592
  have htrace : WordTrace (prefixWord ++ tailWord_3220592) baseStart_3220592 baseEnd_3220592 := by
    simpa [prefixWord, tailWord_3220592, baseEnd_3220592] using wordTrace_append hprefix tailTrace_3220592
  have hstable : (prefixWord ++ tailWord_3220592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220592).length < 2 ^ (prefixWord ++ tailWord_3220592).sum := by decide
  have hdescent : baseEnd_3220592 < baseStart_3220592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220605 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3220605 : Nat := 118140960795 + 3220605 * 2 ^ 59
def prefixEnd_3220605 : Nat := 4983230072969 + 3 ^ 40 * 3220605 * 2
def baseEnd_3220605 : Nat := 1653718363273477101826213

theorem tailTrace_3220605 : CollatzResearch.WordTrace tailWord_3220605 prefixEnd_3220605 1653718363273477101826213 := by
  unfold tailWord_3220605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117465114497305595388543269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78310076331537063592362179 117465114497305595388543269)
  ·
    refine ⟨22024708968244799135351863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117465114497305595388543269 22024708968244799135351863)
    ·
      refine ⟨33037063452367198703027795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024708968244799135351863 33037063452367198703027795)
      ·
        refine ⟨49555595178550798054541693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33037063452367198703027795 49555595178550798054541693)
        ·
          refine ⟨18583348191956549270453135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49555595178550798054541693 18583348191956549270453135)
          ·
            refine ⟨27875022287934823905679703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18583348191956549270453135 27875022287934823905679703)
            ·
              refine ⟨41812533431902235858519555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27875022287934823905679703 41812533431902235858519555)
              ·
                refine ⟨62718800147853353787779333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41812533431902235858519555 62718800147853353787779333)
                ·
                  refine ⟨11759775027722503835208625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62718800147853353787779333 11759775027722503835208625)
                  ·
                    refine ⟨8819831270791877876406469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759775027722503835208625 8819831270791877876406469)
                    ·
                      refine ⟨1653718363273477101826213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819831270791877876406469 1653718363273477101826213)
                      ·
                        rfl

theorem cell23_3220605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3220605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220605 prefixEnd_3220605 := by exact prefixLift 3220605
  have htrace : WordTrace (prefixWord ++ tailWord_3220605) baseStart_3220605 baseEnd_3220605 := by
    simpa [prefixWord, tailWord_3220605, baseEnd_3220605] using wordTrace_append hprefix tailTrace_3220605
  have hstable : (prefixWord ++ tailWord_3220605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220605).length < 2 ^ (prefixWord ++ tailWord_3220605).sum := by decide
  have hdescent : baseEnd_3220605 < baseStart_3220605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220622 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3220622 : Nat := 118140960795 + 3220622 * 2 ^ 59
def prefixEnd_3220622 : Nat := 4983230072969 + 3 ^ 40 * 3220622 * 2
def baseEnd_3220622 : Nat := 1653727092444603535313635

theorem tailTrace_3220622 : CollatzResearch.WordTrace tailWord_3220622 prefixEnd_3220622 1653727092444603535313635 := by
  unfold tailWord_3220622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683216817280500911489015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78310489692162671527941413 14683216817280500911489015)
  ·
    refine ⟨22024825225920751367233523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14683216817280500911489015 22024825225920751367233523)
    ·
      refine ⟨33037237838881127050850285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024825225920751367233523 33037237838881127050850285)
      ·
        refine ⟨12388964189580422644068857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33037237838881127050850285 12388964189580422644068857)
        ·
          refine ⟨9291723142185316983051643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12388964189580422644068857 9291723142185316983051643)
          ·
            refine ⟨13937584713277975474577465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291723142185316983051643 13937584713277975474577465)
            ·
              refine ⟨10453188534958481605933099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937584713277975474577465 10453188534958481605933099)
              ·
                refine ⟨15679782802437722408899649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453188534958481605933099 15679782802437722408899649)
                ·
                  refine ⟨11759837101828291806674737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15679782802437722408899649 11759837101828291806674737)
                  ·
                    refine ⟨8819877826371218855006053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759837101828291806674737 8819877826371218855006053)
                    ·
                      refine ⟨1653727092444603535313635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8819877826371218855006053 1653727092444603535313635)
                      ·
                        rfl

theorem cell23_3220622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3220622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220622 prefixEnd_3220622 := by exact prefixLift 3220622
  have htrace : WordTrace (prefixWord ++ tailWord_3220622) baseStart_3220622 baseEnd_3220622 := by
    simpa [prefixWord, tailWord_3220622, baseEnd_3220622] using wordTrace_append hprefix tailTrace_3220622
  have hstable : (prefixWord ++ tailWord_3220622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220622).length < 2 ^ (prefixWord ++ tailWord_3220622).sum := by decide
  have hdescent : baseEnd_3220622 < baseStart_3220622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220626 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3220626 : Nat := 118140960795 + 3220626 * 2 ^ 59
def prefixEnd_3220626 : Nat := 4983230072969 + 3 ^ 40 * 3220626 * 2
def baseEnd_3220626 : Nat := 1653729146367221519663617

theorem tailTrace_3220626 : CollatzResearch.WordTrace tailWord_3220626 prefixEnd_3220626 1653729146367221519663617 := by
  unfold tailWord_3220626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29366470107557378993764433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78310586953486343983371821 29366470107557378993764433)
  ·
    refine ⟨22024852580668034245323325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29366470107557378993764433 22024852580668034245323325)
    ·
      refine ⟨8259319717750512841996247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22024852580668034245323325 8259319717750512841996247)
      ·
        refine ⟨12388979576625769262994371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8259319717750512841996247 12388979576625769262994371)
        ·
          refine ⟨18583469364938653894491557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388979576625769262994371 18583469364938653894491557)
          ·
            refine ⟨3484400505925997605217167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18583469364938653894491557 3484400505925997605217167)
            ·
              refine ⟨5226600758888996407825751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484400505925997605217167 5226600758888996407825751)
              ·
                refine ⟨7839901138333494611738627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226600758888996407825751 7839901138333494611738627)
                ·
                  refine ⟨11759851707500241917607941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839901138333494611738627 11759851707500241917607941)
                  ·
                    refine ⟨2204972195156295359551489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11759851707500241917607941 2204972195156295359551489)
                    ·
                      refine ⟨1653729146367221519663617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2204972195156295359551489 1653729146367221519663617)
                      ·
                        rfl

theorem cell23_3220626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3220626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220626 prefixEnd_3220626 := by exact prefixLift 3220626
  have htrace : WordTrace (prefixWord ++ tailWord_3220626) baseStart_3220626 baseEnd_3220626 := by
    simpa [prefixWord, tailWord_3220626, baseEnd_3220626] using wordTrace_append hprefix tailTrace_3220626
  have hstable : (prefixWord ++ tailWord_3220626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220626).length < 2 ^ (prefixWord ++ tailWord_3220626).sum := by decide
  have hdescent : baseEnd_3220626 < baseStart_3220626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220645 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_3220645 : Nat := 118140960795 + 3220645 * 2 ^ 59
def prefixEnd_3220645 : Nat := 4983230072969 + 3 ^ 40 * 3220645 * 2
def baseEnd_3220645 : Nat := 551246300833218981775343

theorem tailTrace_3220645 : CollatzResearch.WordTrace tailWord_3220645 prefixEnd_3220645 551246300833218981775343 := by
  unfold tailWord_3220645
  simp only [CollatzResearch.WordTrace]
  refine ⟨117466573417160682219999389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78311048944773788146666259 117466573417160682219999389)
  ·
    refine ⟨44049965031435255832499771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117466573417160682219999389 44049965031435255832499771)
    ·
      refine ⟨66074947547152883748749657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44049965031435255832499771 66074947547152883748749657)
      ·
        refine ⟨49556210660364662811562243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66074947547152883748749657 49556210660364662811562243)
        ·
          refine ⟨74334315990546994217343365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49556210660364662811562243 74334315990546994217343365)
          ·
            refine ⟨13937684248227561415751881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74334315990546994217343365 13937684248227561415751881)
            ·
              refine ⟨10453263186170671061813911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937684248227561415751881 10453263186170671061813911)
              ·
                refine ⟨15679894779256006592720867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453263186170671061813911 15679894779256006592720867)
                ·
                  refine ⟨23519842168884009889081301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15679894779256006592720867 23519842168884009889081301)
                  ·
                    refine ⟨551246300833218981775343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23519842168884009889081301 551246300833218981775343)
                    ·
                      rfl

theorem cell23_3220645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_3220645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220645 prefixEnd_3220645 := by exact prefixLift 3220645
  have htrace : WordTrace (prefixWord ++ tailWord_3220645) baseStart_3220645 baseEnd_3220645 := by
    simpa [prefixWord, tailWord_3220645, baseEnd_3220645] using wordTrace_append hprefix tailTrace_3220645
  have hstable : (prefixWord ++ tailWord_3220645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220645).length < 2 ^ (prefixWord ++ tailWord_3220645).sum := by decide
  have hdescent : baseEnd_3220645 < baseStart_3220645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220672 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_3220672 : Nat := 118140960795 + 3220672 * 2 ^ 59
def prefixEnd_3220672 : Nat := 4983230072969 + 3 ^ 40 * 3220672 * 2
def baseEnd_3220672 : Nat := 1653752766477328339688405

theorem tailTrace_3220672 : CollatzResearch.WordTrace tailWord_3220672 prefixEnd_3220672 1653752766477328339688405 := by
  unfold tailWord_3220672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58733779094031432915616135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78311705458708577220821513 58733779094031432915616135)
  ·
    refine ⟨88100668641047149373424203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58733779094031432915616135 88100668641047149373424203)
    ·
      refine ⟨132151002961570724060136305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88100668641047149373424203 132151002961570724060136305)
      ·
        refine ⟨99113252221178043045102229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132151002961570724060136305 99113252221178043045102229)
        ·
          refine ⟨4645933697867720767739167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99113252221178043045102229 4645933697867720767739167)
          ·
            refine ⟨6968900546801581151608751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645933697867720767739167 6968900546801581151608751)
            ·
              refine ⟨10453350820202371727413127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968900546801581151608751 10453350820202371727413127)
              ·
                refine ⟨15680026230303557591119691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453350820202371727413127 15680026230303557591119691)
                ·
                  refine ⟨23520039345455336386679537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15680026230303557591119691 23520039345455336386679537)
                  ·
                    refine ⟨17640029509091502290009653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23520039345455336386679537 17640029509091502290009653)
                    ·
                      refine ⟨1653752766477328339688405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17640029509091502290009653 1653752766477328339688405)
                      ·
                        rfl

theorem cell23_3220672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_3220672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220672 prefixEnd_3220672 := by exact prefixLift 3220672
  have htrace : WordTrace (prefixWord ++ tailWord_3220672) baseStart_3220672 baseEnd_3220672 := by
    simpa [prefixWord, tailWord_3220672, baseEnd_3220672] using wordTrace_append hprefix tailTrace_3220672
  have hstable : (prefixWord ++ tailWord_3220672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220672).length < 2 ^ (prefixWord ++ tailWord_3220672).sum := by decide
  have hdescent : baseEnd_3220672 < baseStart_3220672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220695 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3220695 : Nat := 118140960795 + 3220695 * 2 ^ 59
def prefixEnd_3220695 : Nat := 4983230072969 + 3 ^ 40 * 3220695 * 2
def baseEnd_3220695 : Nat := 1653764576532381749700799

theorem tailTrace_3220695 : CollatzResearch.WordTrace tailWord_3220695 prefixEnd_3220695 1653764576532381749700799 := by
  unfold tailWord_3220695
  simp only [CollatzResearch.WordTrace]
  refine ⟨117468397066979540759319539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78312264711319693839546359 117468397066979540759319539)
  ·
    refine ⟨176202595600469311138979309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117468397066979540759319539 176202595600469311138979309)
    ·
      refine ⟨66075973350175991677117241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176202595600469311138979309 66075973350175991677117241)
      ·
        refine ⟨49556980012631993757837931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66075973350175991677117241 49556980012631993757837931)
        ·
          refine ⟨74335470018947990636756897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49556980012631993757837931 74335470018947990636756897)
          ·
            refine ⟨55751602514210992977567673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74335470018947990636756897 55751602514210992977567673)
            ·
              refine ⟨41813701885658244733175755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55751602514210992977567673 41813701885658244733175755)
              ·
                refine ⟨62720552828487367099763633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41813701885658244733175755 62720552828487367099763633)
                ·
                  refine ⟨47040414621365525324822725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62720552828487367099763633 47040414621365525324822725)
                  ·
                    refine ⟨8820077741506035998404261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47040414621365525324822725 8820077741506035998404261)
                    ·
                      refine ⟨1653764576532381749700799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8820077741506035998404261 1653764576532381749700799)
                      ·
                        rfl

theorem cell23_3220695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3220695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220695 prefixEnd_3220695 := by exact prefixLift 3220695
  have htrace : WordTrace (prefixWord ++ tailWord_3220695) baseStart_3220695 baseEnd_3220695 := by
    simpa [prefixWord, tailWord_3220695, baseEnd_3220695] using wordTrace_append hprefix tailTrace_3220695
  have hstable : (prefixWord ++ tailWord_3220695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220695).length < 2 ^ (prefixWord ++ tailWord_3220695).sum := by decide
  have hdescent : baseEnd_3220695 < baseStart_3220695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220745 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3220745 : Nat := 118140960795 + 3220745 * 2 ^ 59
def prefixEnd_3220745 : Nat := 4983230072969 + 3 ^ 40 * 3220745 * 2
def baseEnd_3220745 : Nat := 1653790250565106554075569

theorem tailTrace_3220745 : CollatzResearch.WordTrace tailWord_3220745 prefixEnd_3220745 1653790250565106554075569 := by
  unfold tailWord_3220745
  simp only [CollatzResearch.WordTrace]
  refine ⟨117470220716798399298639689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78313480477865599532426459 117470220716798399298639689)
  ·
    refine ⟨88102665537598799473979767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117470220716798399298639689 88102665537598799473979767)
    ·
      refine ⟨132153998306398199210969651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88102665537598799473979767 132153998306398199210969651)
      ·
        refine ⟨198230997459597298816454477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132153998306398199210969651 198230997459597298816454477)
        ·
          refine ⟨74336624047348987056170429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198230997459597298816454477 74336624047348987056170429)
          ·
            refine ⟨27876234017755870146063911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74336624047348987056170429 27876234017755870146063911)
            ·
              refine ⟨41814351026633805219095867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27876234017755870146063911 41814351026633805219095867)
              ·
                refine ⟨62721526539950707828643801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41814351026633805219095867 62721526539950707828643801)
                ·
                  refine ⟨47041144904963030871482851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62721526539950707828643801 47041144904963030871482851)
                  ·
                    refine ⟨70561717357444546307224277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47041144904963030871482851 70561717357444546307224277)
                    ·
                      refine ⟨1653790250565106554075569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70561717357444546307224277 1653790250565106554075569)
                      ·
                        rfl

theorem cell23_3220745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3220745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220745 prefixEnd_3220745 := by exact prefixLift 3220745
  have htrace : WordTrace (prefixWord ++ tailWord_3220745) baseStart_3220745 baseEnd_3220745 := by
    simpa [prefixWord, tailWord_3220745, baseEnd_3220745] using wordTrace_append hprefix tailTrace_3220745
  have hstable : (prefixWord ++ tailWord_3220745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220745).length < 2 ^ (prefixWord ++ tailWord_3220745).sum := by decide
  have hdescent : baseEnd_3220745 < baseStart_3220745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220759 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3220759 : Nat := 118140960795 + 3220759 * 2 ^ 59
def prefixEnd_3220759 : Nat := 4983230072969 + 3 ^ 40 * 3220759 * 2
def baseEnd_3220759 : Nat := 1653797439294269499300505

theorem tailTrace_3220759 : CollatzResearch.WordTrace tailWord_3220759 prefixEnd_3220759 1653797439294269499300505 := by
  unfold tailWord_3220759
  simp only [CollatzResearch.WordTrace]
  refine ⟨117470731338747679689649331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78313820892498453126432887 117470731338747679689649331)
  ·
    refine ⟨176206097008121519534473997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117470731338747679689649331 176206097008121519534473997)
    ·
      refine ⟨66077286378045569825427749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176206097008121519534473997 66077286378045569825427749)
      ·
        refine ⟨12389491195883544342267703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66077286378045569825427749 12389491195883544342267703)
        ·
          refine ⟨18584236793825316513401555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12389491195883544342267703 18584236793825316513401555)
          ·
            refine ⟨27876355190737974770102333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18584236793825316513401555 27876355190737974770102333)
            ·
              refine ⟨10453633196526740538788375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27876355190737974770102333 10453633196526740538788375)
              ·
                refine ⟨15680449794790110808182563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453633196526740538788375 15680449794790110808182563)
                ·
                  refine ⟨23520674692185166212273845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15680449794790110808182563 23520674692185166212273845)
                  ·
                    refine ⟨2205063252392359332400673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23520674692185166212273845 2205063252392359332400673)
                    ·
                      refine ⟨1653797439294269499300505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205063252392359332400673 1653797439294269499300505)
                      ·
                        rfl

theorem cell23_3220759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3220759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220759 prefixEnd_3220759 := by exact prefixLift 3220759
  have htrace : WordTrace (prefixWord ++ tailWord_3220759) baseStart_3220759 baseEnd_3220759 := by
    simpa [prefixWord, tailWord_3220759, baseEnd_3220759] using wordTrace_append hprefix tailTrace_3220759
  have hstable : (prefixWord ++ tailWord_3220759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220759).length < 2 ^ (prefixWord ++ tailWord_3220759).sum := by decide
  have hdescent : baseEnd_3220759 < baseStart_3220759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220799 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 6]
def baseStart_3220799 : Nat := 118140960795 + 3220799 * 2 ^ 59
def prefixEnd_3220799 : Nat := 4983230072969 + 3 ^ 40 * 3220799 * 2
def baseEnd_3220799 : Nat := 551272659506816447600107

theorem tailTrace_3220799 : CollatzResearch.WordTrace tailWord_3220799 prefixEnd_3220799 551272659506816447600107 := by
  unfold tailWord_3220799
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472190258602766521105451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78314793505735177680736967 117472190258602766521105451)
  ·
    refine ⟨176208285387904149781658177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117472190258602766521105451 176208285387904149781658177)
    ·
      refine ⟨132156214040928112336243633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176208285387904149781658177 132156214040928112336243633)
      ·
        refine ⟨99117160530696084252182725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132156214040928112336243633 99117160530696084252182725)
        ·
          refine ⟨18584467599505515797284261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99117160530696084252182725 18584467599505515797284261)
          ·
            refine ⟨3484587674907284211990799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18584467599505515797284261 3484587674907284211990799)
            ·
              refine ⟨5226881512360926317986199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484587674907284211990799 5226881512360926317986199)
              ·
                refine ⟨7840322268541389476979299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226881512360926317986199 7840322268541389476979299)
                ·
                  refine ⟨11760483402812084215468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7840322268541389476979299 11760483402812084215468949)
                  ·
                    refine ⟨551272659506816447600107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11760483402812084215468949 551272659506816447600107)
                    ·
                      rfl

theorem cell23_3220799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_3220799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220799 prefixEnd_3220799 := by exact prefixLift 3220799
  have htrace : WordTrace (prefixWord ++ tailWord_3220799) baseStart_3220799 baseEnd_3220799 := by
    simpa [prefixWord, tailWord_3220799, baseEnd_3220799] using wordTrace_append hprefix tailTrace_3220799
  have hstable : (prefixWord ++ tailWord_3220799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220799).length < 2 ^ (prefixWord ++ tailWord_3220799).sum := by decide
  have hdescent : baseEnd_3220799 < baseStart_3220799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220809 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_3220809 : Nat := 118140960795 + 3220809 * 2 ^ 59
def prefixEnd_3220809 : Nat := 4983230072969 + 3 ^ 40 * 3220809 * 2
def baseEnd_3220809 : Nat := 1653823113326994303675275

theorem tailTrace_3220809 : CollatzResearch.WordTrace tailWord_3220809 prefixEnd_3220809 1653823113326994303675275 := by
  unfold tailWord_3220809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472554988566538228969481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78315036659044358819312987 117472554988566538228969481)
  ·
    refine ⟨88104416241424903671727111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117472554988566538228969481 88104416241424903671727111)
    ·
      refine ⟨132156624362137355507590667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88104416241424903671727111 132156624362137355507590667)
      ·
        refine ⟨198234936543206033261386001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132156624362137355507590667 198234936543206033261386001)
        ·
          refine ⟨148676202407404524946039501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198234936543206033261386001 148676202407404524946039501)
          ·
            refine ⟨55753575902776696854764813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148676202407404524946039501 55753575902776696854764813)
            ·
              refine ⟨20907590963541261320536805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55753575902776696854764813 20907590963541261320536805)
              ·
                refine ⟨3920173305663986497600651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20907590963541261320536805 3920173305663986497600651)
                ·
                  refine ⟨5880259958495979746400977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920173305663986497600651 5880259958495979746400977)
                  ·
                    refine ⟨4410194968871984809800733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880259958495979746400977 4410194968871984809800733)
                    ·
                      refine ⟨1653823113326994303675275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410194968871984809800733 1653823113326994303675275)
                      ·
                        rfl

theorem cell23_3220809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_3220809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220809 prefixEnd_3220809 := by exact prefixLift 3220809
  have htrace : WordTrace (prefixWord ++ tailWord_3220809) baseStart_3220809 baseEnd_3220809 := by
    simpa [prefixWord, tailWord_3220809, baseEnd_3220809] using wordTrace_append hprefix tailTrace_3220809
  have hstable : (prefixWord ++ tailWord_3220809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220809).length < 2 ^ (prefixWord ++ tailWord_3220809).sum := by decide
  have hdescent : baseEnd_3220809 < baseStart_3220809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220812 : List Nat := [2, 2, 1, 3, 2, 3, 1, 9]
def baseStart_3220812 : Nat := 118140960795 + 3220812 * 2 ^ 59
def prefixEnd_3220812 : Nat := 4983230072969 + 3 ^ 40 * 3220812 * 2
def baseEnd_3220812 : Nat := 61252764954405844145843

theorem tailTrace_3220812 : CollatzResearch.WordTrace tailWord_3220812 prefixEnd_3220812 61252764954405844145843 := by
  unfold tailWord_3220812
  simp only [CollatzResearch.WordTrace]
  refine ⟨58736332203777834870664345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78315109605037113160885793 58736332203777834870664345)
  ·
    refine ⟨44052249152833376152998259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58736332203777834870664345 44052249152833376152998259)
    ·
      refine ⟨66078373729250064229497389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44052249152833376152998259 66078373729250064229497389)
      ·
        refine ⟨24779390148468774086061521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66078373729250064229497389 24779390148468774086061521)
        ·
          refine ⟨18584542611351580564546141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24779390148468774086061521 18584542611351580564546141)
          ·
            refine ⟨6969203479256842711704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18584542611351580564546141 6969203479256842711704803)
            ·
              refine ⟨10453805218885264067557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969203479256842711704803 10453805218885264067557205)
              ·
                refine ⟨61252764954405844145843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10453805218885264067557205 61252764954405844145843)
                ·
                  rfl

theorem cell23_3220812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 9].length) (baseStart_3220812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220812 prefixEnd_3220812 := by exact prefixLift 3220812
  have htrace : WordTrace (prefixWord ++ tailWord_3220812) baseStart_3220812 baseEnd_3220812 := by
    simpa [prefixWord, tailWord_3220812, baseEnd_3220812] using wordTrace_append hprefix tailTrace_3220812
  have hstable : (prefixWord ++ tailWord_3220812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220812).length < 2 ^ (prefixWord ++ tailWord_3220812).sum := by decide
  have hdescent : baseEnd_3220812 < baseStart_3220812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220840 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3220840 : Nat := 118140960795 + 3220840 * 2 ^ 59
def prefixEnd_3220840 : Nat := 4983230072969 + 3 ^ 40 * 3220840 * 2
def baseEnd_3220840 : Nat := 1653839031227283682387633

theorem tailTrace_3220840 : CollatzResearch.WordTrace tailWord_3220840 prefixEnd_3220840 1653839031227283682387633 := by
  unfold tailWord_3220840
  simp only [CollatzResearch.WordTrace]
  refine ⟨58736842825727115261673987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78315790434302820348898649 58736842825727115261673987)
  ·
    refine ⟨88105264238590672892510981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58736842825727115261673987 88105264238590672892510981)
    ·
      refine ⟨16519737044735751167345809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88105264238590672892510981 16519737044735751167345809)
      ·
        refine ⟨12389802783551813375509357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16519737044735751167345809 12389802783551813375509357)
        ·
          refine ⟨4646176043831930015816009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12389802783551813375509357 4646176043831930015816009)
          ·
            refine ⟨3484632032873947511862007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646176043831930015816009 3484632032873947511862007)
            ·
              refine ⟨5226948049310921267793011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484632032873947511862007 5226948049310921267793011)
              ·
                refine ⟨7840422073966381901689517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226948049310921267793011 7840422073966381901689517)
                ·
                  refine ⟨2940158277737393213133569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7840422073966381901689517 2940158277737393213133569)
                  ·
                    refine ⟨2205118708303044909850177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2940158277737393213133569 2205118708303044909850177)
                    ·
                      refine ⟨1653839031227283682387633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205118708303044909850177 1653839031227283682387633)
                      ·
                        rfl

theorem cell23_3220840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3220840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220840 prefixEnd_3220840 := by exact prefixLift 3220840
  have htrace : WordTrace (prefixWord ++ tailWord_3220840) baseStart_3220840 baseEnd_3220840 := by
    simpa [prefixWord, tailWord_3220840, baseEnd_3220840] using wordTrace_append hprefix tailTrace_3220840
  have hstable : (prefixWord ++ tailWord_3220840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220840).length < 2 ^ (prefixWord ++ tailWord_3220840).sum := by decide
  have hdescent : baseEnd_3220840 < baseStart_3220840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220846 : List Nat := [4, 1, 2, 4, 1, 1, 2, 8]
def baseStart_3220846 : Nat := 118140960795 + 3220846 * 2 ^ 59
def prefixEnd_3220846 : Nat := 4983230072969 + 3 ^ 40 * 3220846 * 2
def baseEnd_3220846 : Nat := 61253411559674468848615

theorem tailTrace_3220846 : CollatzResearch.WordTrace tailWord_3220846 prefixEnd_3220846 61253411559674468848615 := by
  unfold tailWord_3220846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684238061179061693508299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78315936326288329032044261 14684238061179061693508299)
  ·
    refine ⟨22026357091768592540262449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14684238061179061693508299 22026357091768592540262449)
    ·
      refine ⟨16519767818826444405196837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22026357091768592540262449 16519767818826444405196837)
      ·
        refine ⟨3097456466029958325974407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16519767818826444405196837 3097456466029958325974407)
        ·
          refine ⟨4646184699044937488961611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097456466029958325974407 4646184699044937488961611)
          ·
            refine ⟨6969277048567406233442417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646184699044937488961611 6969277048567406233442417)
            ·
              refine ⟨5226957786425554675081813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969277048567406233442417 5226957786425554675081813)
              ·
                refine ⟨61253411559674468848615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5226957786425554675081813 61253411559674468848615)
                ·
                  rfl

theorem cell23_3220846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_3220846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220846 prefixEnd_3220846 := by exact prefixLift 3220846
  have htrace : WordTrace (prefixWord ++ tailWord_3220846) baseStart_3220846 baseEnd_3220846 := by
    simpa [prefixWord, tailWord_3220846, baseEnd_3220846] using wordTrace_append hprefix tailTrace_3220846
  have hstable : (prefixWord ++ tailWord_3220846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220846).length < 2 ^ (prefixWord ++ tailWord_3220846).sum := by decide
  have hdescent : baseEnd_3220846 < baseStart_3220846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220913 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3220913 : Nat := 118140960795 + 3220913 * 2 ^ 59
def prefixEnd_3220913 : Nat := 4983230072969 + 3 ^ 40 * 3220913 * 2
def baseEnd_3220913 : Nat := 1653876515315061896774797

theorem tailTrace_3220913 : CollatzResearch.WordTrace tailWord_3220913 prefixEnd_3220913 1653876515315061896774797 := by
  unfold tailWord_3220913
  simp only [CollatzResearch.WordTrace]
  refine ⟨117476348180189763990755393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78317565453459842660503595 117476348180189763990755393)
  ·
    refine ⟨88107261135142322993066545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117476348180189763990755393 88107261135142322993066545)
    ·
      refine ⟨66080445851356742244799909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88107261135142322993066545 66080445851356742244799909)
      ·
        refine ⟨12390083597129389170899983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66080445851356742244799909 12390083597129389170899983)
        ·
          refine ⟨18585125395694083756349975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390083597129389170899983 18585125395694083756349975)
          ·
            refine ⟨27877688093541125634524963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585125395694083756349975 27877688093541125634524963)
            ·
              refine ⟨41816532140311688451787445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27877688093541125634524963 41816532140311688451787445)
              ·
                refine ⟨3920299888154220792355073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41816532140311688451787445 3920299888154220792355073)
                ·
                  refine ⟨2940224916115665594266305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920299888154220792355073 2940224916115665594266305)
                  ·
                    refine ⟨2205168687086749195699729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2940224916115665594266305 2205168687086749195699729)
                    ·
                      refine ⟨1653876515315061896774797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205168687086749195699729 1653876515315061896774797)
                      ·
                        rfl

theorem cell23_3220913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3220913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220913 prefixEnd_3220913 := by exact prefixLift 3220913
  have htrace : WordTrace (prefixWord ++ tailWord_3220913) baseStart_3220913 baseEnd_3220913 := by
    simpa [prefixWord, tailWord_3220913, baseEnd_3220913] using wordTrace_append hprefix tailTrace_3220913
  have hstable : (prefixWord ++ tailWord_3220913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220913).length < 2 ^ (prefixWord ++ tailWord_3220913).sum := by decide
  have hdescent : baseEnd_3220913 < baseStart_3220913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220936 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 5]
def baseStart_3220936 : Nat := 118140960795 + 3220936 * 2 ^ 59
def prefixEnd_3220936 : Nat := 4983230072969 + 3 ^ 40 * 3220936 * 2
def baseEnd_3220936 : Nat := 183765369485568367420799

theorem tailTrace_3220936 : CollatzResearch.WordTrace tailWord_3220936 prefixEnd_3220936 183765369485568367420799 := by
  unfold tailWord_3220936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58738593529553219459421331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78318124706070959279228441 58738593529553219459421331)
  ·
    refine ⟨88107890294329829189131997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58738593529553219459421331 88107890294329829189131997)
    ·
      refine ⟨33040458860373685945924499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88107890294329829189131997 33040458860373685945924499)
      ·
        refine ⟨49560688290560528918886749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33040458860373685945924499 49560688290560528918886749)
        ·
          refine ⟨18585258108960198344582531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49560688290560528918886749 18585258108960198344582531)
          ·
            refine ⟨27877887163440297516873797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585258108960198344582531 27877887163440297516873797)
            ·
              refine ⟨5227103843145055784413837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27877887163440297516873797 5227103843145055784413837)
              ·
                refine ⟨1960163941179395919155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5227103843145055784413837 1960163941179395919155189)
                ·
                  refine ⟨183765369485568367420799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1960163941179395919155189 183765369485568367420799)
                  ·
                    rfl

theorem cell23_3220936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 5].length) (baseStart_3220936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220936 prefixEnd_3220936 := by exact prefixLift 3220936
  have htrace : WordTrace (prefixWord ++ tailWord_3220936) baseStart_3220936 baseEnd_3220936 := by
    simpa [prefixWord, tailWord_3220936, baseEnd_3220936] using wordTrace_append hprefix tailTrace_3220936
  have hstable : (prefixWord ++ tailWord_3220936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220936).length < 2 ^ (prefixWord ++ tailWord_3220936).sum := by decide
  have hdescent : baseEnd_3220936 < baseStart_3220936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220949 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3220949 : Nat := 118140960795 + 3220949 * 2 ^ 59
def prefixEnd_3220949 : Nat := 4983230072969 + 3 ^ 40 * 3220949 * 2
def baseEnd_3220949 : Nat := 551298333539541251974877

theorem tailTrace_3220949 : CollatzResearch.WordTrace tailWord_3220949 prefixEnd_3220949 551298333539541251974877 := by
  unfold tailWord_3220949
  simp only [CollatzResearch.WordTrace]
  refine ⟨117477661208059342139065901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78318440805372894759377267 117477661208059342139065901)
  ·
    refine ⟨44054122953022253302149713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117477661208059342139065901 44054122953022253302149713)
    ·
      refine ⟨33040592214766689976612285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44054122953022253302149713 33040592214766689976612285)
      ·
        refine ⟨12390222080537508741229607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33040592214766689976612285 12390222080537508741229607)
        ·
          refine ⟨18585333120806263111844411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390222080537508741229607 18585333120806263111844411)
          ·
            refine ⟨27877999681209394667766617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585333120806263111844411 27877999681209394667766617)
            ·
              refine ⟨20908499760907046000824963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27877999681209394667766617 20908499760907046000824963)
              ·
                refine ⟨31362749641360569001237445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20908499760907046000824963 31362749641360569001237445)
                ·
                  refine ⟨5880515557755106687732021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31362749641360569001237445 5880515557755106687732021)
                  ·
                    refine ⟨551298333539541251974877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5880515557755106687732021 551298333539541251974877)
                    ·
                      rfl

theorem cell23_3220949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3220949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220949 prefixEnd_3220949 := by exact prefixLift 3220949
  have htrace : WordTrace (prefixWord ++ tailWord_3220949) baseStart_3220949 baseEnd_3220949 := by
    simpa [prefixWord, tailWord_3220949, baseEnd_3220949] using wordTrace_append hprefix tailTrace_3220949
  have hstable : (prefixWord ++ tailWord_3220949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220949).length < 2 ^ (prefixWord ++ tailWord_3220949).sum := by decide
  have hdescent : baseEnd_3220949 < baseStart_3220949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220979 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 5, 4]
def baseStart_3220979 : Nat := 118140960795 + 3220979 * 2 ^ 59
def prefixEnd_3220979 : Nat := 4983230072969 + 3 ^ 40 * 3220979 * 2
def baseEnd_3220979 : Nat := 551303468346086212849831

theorem tailTrace_3220979 : CollatzResearch.WordTrace tailWord_3220979 prefixEnd_3220979 551303468346086212849831 := by
  unfold tailWord_3220979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478755397950657262657991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78319170265300438175105327 117478755397950657262657991)
  ·
    refine ⟨176218133096925985893986987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117478755397950657262657991 176218133096925985893986987)
    ·
      refine ⟨264327199645388978840980481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176218133096925985893986987 264327199645388978840980481)
      ·
        refine ⟨198245399734041734130735361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264327199645388978840980481 198245399734041734130735361)
        ·
          refine ⟨148684049800531300598051521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198245399734041734130735361 148684049800531300598051521)
          ·
            refine ⟨111513037350398475448538641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148684049800531300598051521 111513037350398475448538641)
            ·
              refine ⟨83634778012798856586403981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111513037350398475448538641 83634778012798856586403981)
              ·
                refine ⟨31363041754799571219901493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83634778012798856586403981 31363041754799571219901493)
                ·
                  refine ⟨2940285164512459801865765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31363041754799571219901493 2940285164512459801865765)
                  ·
                    refine ⟨551303468346086212849831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2940285164512459801865765 551303468346086212849831)
                    ·
                      rfl

theorem cell23_3220979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 4].length) (baseStart_3220979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3220979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3220979 prefixEnd_3220979 := by exact prefixLift 3220979
  have htrace : WordTrace (prefixWord ++ tailWord_3220979) baseStart_3220979 baseEnd_3220979 := by
    simpa [prefixWord, tailWord_3220979, baseEnd_3220979] using wordTrace_append hprefix tailTrace_3220979
  have hstable : (prefixWord ++ tailWord_3220979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220979).length < 2 ^ (prefixWord ++ tailWord_3220979).sum := by decide
  have hdescent : baseEnd_3220979 < baseStart_3220979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221009 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 6]
def baseStart_3221009 : Nat := 118140960795 + 3221009 * 2 ^ 59
def prefixEnd_3221009 : Nat := 4983230072969 + 3 ^ 40 * 3221009 * 2
def baseEnd_3221009 : Nat := 183769534384210391241595

theorem tailTrace_3221009 : CollatzResearch.WordTrace tailWord_3221009 prefixEnd_3221009 183769534384210391241595 := by
  unfold tailWord_3221009
  simp only [CollatzResearch.WordTrace]
  refine ⟨117479849587841972386250081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78319899725227981590833387 117479849587841972386250081)
  ·
    refine ⟨88109887190881479289687561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117479849587841972386250081 88109887190881479289687561)
    ·
      refine ⟨66082415393161109467265671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88109887190881479289687561 66082415393161109467265671)
      ·
        refine ⟨99123623089741664200898507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66082415393161109467265671 99123623089741664200898507)
        ·
          refine ⟨148685434634612496301347761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99123623089741664200898507 148685434634612496301347761)
          ·
            refine ⟨111514075975959372226010821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148685434634612496301347761 111514075975959372226010821)
            ·
              refine ⟨20908889245492382292377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111514075975959372226010821 20908889245492382292377029)
              ·
                refine ⟨3920416733529821679820693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20908889245492382292377029 3920416733529821679820693)
                ·
                  refine ⟨183769534384210391241595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3920416733529821679820693 183769534384210391241595)
                  ·
                    rfl

theorem cell23_3221009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_3221009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221009 prefixEnd_3221009 := by exact prefixLift 3221009
  have htrace : WordTrace (prefixWord ++ tailWord_3221009) baseStart_3221009 baseEnd_3221009 := by
    simpa [prefixWord, tailWord_3221009, baseEnd_3221009] using wordTrace_append hprefix tailTrace_3221009
  have hstable : (prefixWord ++ tailWord_3221009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221009).length < 2 ^ (prefixWord ++ tailWord_3221009).sum := by decide
  have hdescent : baseEnd_3221009 < baseStart_3221009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221013 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_3221013 : Nat := 118140960795 + 3221013 * 2 ^ 59
def prefixEnd_3221013 : Nat := 4983230072969 + 3 ^ 40 * 3221013 * 2
def baseEnd_3221013 : Nat := 551309287793503835174779

theorem tailTrace_3221013 : CollatzResearch.WordTrace tailWord_3221013 prefixEnd_3221013 551309287793503835174779 := by
  unfold tailWord_3221013
  simp only [CollatzResearch.WordTrace]
  refine ⟨117479995479827481069395693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78319996986551654046263795 117479995479827481069395693)
  ·
    refine ⟨44054998304935305401023385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117479995479827481069395693 44054998304935305401023385)
    ·
      refine ⟨33041248728701479050767539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44054998304935305401023385 33041248728701479050767539)
      ·
        refine ⟨49561873093052218576151309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33041248728701479050767539 49561873093052218576151309)
        ·
          refine ⟨18585702409894581966056741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49561873093052218576151309 18585702409894581966056741)
          ·
            refine ⟨3484819201855234118635639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18585702409894581966056741 3484819201855234118635639)
            ·
              refine ⟨5227228802782851177953459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484819201855234118635639 5227228802782851177953459)
              ·
                refine ⟨7840843204174276766930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227228802782851177953459 7840843204174276766930189)
                ·
                  refine ⟨2940316201565353787598821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7840843204174276766930189 2940316201565353787598821)
                  ·
                    refine ⟨551309287793503835174779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2940316201565353787598821 551309287793503835174779)
                    ·
                      rfl

theorem cell23_3221013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_3221013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221013 prefixEnd_3221013 := by exact prefixLift 3221013
  have htrace : WordTrace (prefixWord ++ tailWord_3221013) baseStart_3221013 baseEnd_3221013 := by
    simpa [prefixWord, tailWord_3221013, baseEnd_3221013] using wordTrace_append hprefix tailTrace_3221013
  have hstable : (prefixWord ++ tailWord_3221013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221013).length < 2 ^ (prefixWord ++ tailWord_3221013).sum := by decide
  have hdescent : baseEnd_3221013 < baseStart_3221013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221076 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3221076 : Nat := 118140960795 + 3221076 * 2 ^ 59
def prefixEnd_3221076 : Nat := 4983230072969 + 3 ^ 40 * 3221076 * 2
def baseEnd_3221076 : Nat := 1653960212661744759036547

theorem tailTrace_3221076 : CollatzResearch.WordTrace tailWord_3221076 prefixEnd_3221076 1653960212661744759036547 := by
  unfold tailWord_3221076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58741146639299621414469541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78321528852399495219292721 58741146639299621414469541)
  ·
    refine ⟨11013964994868679015213039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58741146639299621414469541 11013964994868679015213039)
    ·
      refine ⟨16520947492303018522819559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11013964994868679015213039 16520947492303018522819559)
      ·
        refine ⟨24781421238454527784229339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16520947492303018522819559 24781421238454527784229339)
        ·
          refine ⟨37172131857681791676344009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24781421238454527784229339 37172131857681791676344009)
          ·
            refine ⟨27879098893261343757258007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37172131857681791676344009 27879098893261343757258007)
            ·
              refine ⟨41818648339892015635887011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27879098893261343757258007 41818648339892015635887011)
              ·
                refine ⟨62727972509838023453830517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41818648339892015635887011 62727972509838023453830517)
                ·
                  refine ⟨5880747422797314698796611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62727972509838023453830517 5880747422797314698796611)
                  ·
                    refine ⟨8821121134195972048194917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5880747422797314698796611 8821121134195972048194917)
                    ·
                      refine ⟨1653960212661744759036547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8821121134195972048194917 1653960212661744759036547)
                      ·
                        rfl

theorem cell23_3221076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3221076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221076 prefixEnd_3221076 := by exact prefixLift 3221076
  have htrace : WordTrace (prefixWord ++ tailWord_3221076) baseStart_3221076 baseEnd_3221076 := by
    simpa [prefixWord, tailWord_3221076, baseEnd_3221076] using wordTrace_append hprefix tailTrace_3221076
  have hstable : (prefixWord ++ tailWord_3221076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221076).length < 2 ^ (prefixWord ++ tailWord_3221076).sum := by decide
  have hdescent : baseEnd_3221076 < baseStart_3221076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221110 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3221110 : Nat := 118140960795 + 3221110 * 2 ^ 59
def prefixEnd_3221110 : Nat := 4983230072969 + 3 ^ 40 * 3221110 * 2
def baseEnd_3221110 : Nat := 1653977671003997626011391

theorem tailTrace_3221110 : CollatzResearch.WordTrace tailWord_3221110 prefixEnd_3221110 1653977671003997626011391 := by
  unfold tailWord_3221110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342720835029754164729799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78322355573650711090451189 7342720835029754164729799)
  ·
    refine ⟨11014081252544631247094699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7342720835029754164729799 11014081252544631247094699)
    ·
      refine ⟨16521121878816946870642049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014081252544631247094699 16521121878816946870642049)
      ·
        refine ⟨12390841409112710152981537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521121878816946870642049 12390841409112710152981537)
        ·
          refine ⟨9293131056834532614736153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12390841409112710152981537 9293131056834532614736153)
          ·
            refine ⟨6969848292625899461052115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293131056834532614736153 6969848292625899461052115)
            ·
              refine ⟨10454772438938849191578173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969848292625899461052115 10454772438938849191578173)
              ·
                refine ⟨3920539664602068446841815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10454772438938849191578173 3920539664602068446841815)
                ·
                  refine ⟨5880809496903102670262723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920539664602068446841815 5880809496903102670262723)
                  ·
                    refine ⟨8821214245354654005394085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5880809496903102670262723 8821214245354654005394085)
                    ·
                      refine ⟨1653977671003997626011391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8821214245354654005394085 1653977671003997626011391)
                      ·
                        rfl

theorem cell23_3221110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3221110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221110 prefixEnd_3221110 := by exact prefixLift 3221110
  have htrace : WordTrace (prefixWord ++ tailWord_3221110) baseStart_3221110 baseEnd_3221110 := by
    simpa [prefixWord, tailWord_3221110, baseEnd_3221110] using wordTrace_append hprefix tailTrace_3221110
  have hstable : (prefixWord ++ tailWord_3221110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221110).length < 2 ^ (prefixWord ++ tailWord_3221110).sum := by decide
  have hdescent : baseEnd_3221110 < baseStart_3221110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221113 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3221113 : Nat := 118140960795 + 3221113 * 2 ^ 59
def prefixEnd_3221113 : Nat := 4983230072969 + 3 ^ 40 * 3221113 * 2
def baseEnd_3221113 : Nat := 1653979211445961114273877

theorem tailTrace_3221113 : CollatzResearch.WordTrace tailWord_3221113 prefixEnd_3221113 1653979211445961114273877 := by
  unfold tailWord_3221113
  simp only [CollatzResearch.WordTrace]
  refine ⟨117483642779465198148035993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78322428519643465432023995 117483642779465198148035993)
  ·
    refine ⟨88112732084598898611026995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117483642779465198148035993 88112732084598898611026995)
    ·
      refine ⟨132169098126898347916540493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88112732084598898611026995 132169098126898347916540493)
      ·
        refine ⟨49563411797586880468702685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132169098126898347916540493 49563411797586880468702685)
        ·
          refine ⟨18586279424095080175763507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49563411797586880468702685 18586279424095080175763507)
          ·
            refine ⟨27879419136142620263645261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18586279424095080175763507 27879419136142620263645261)
            ·
              refine ⟨10454782176053482598866973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27879419136142620263645261 10454782176053482598866973)
              ·
                refine ⟨3920543316020055974575115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10454782176053482598866973 3920543316020055974575115)
                ·
                  refine ⟨5880814974030083961862673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920543316020055974575115 5880814974030083961862673)
                  ·
                    refine ⟨4410611230522562971397005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880814974030083961862673 4410611230522562971397005)
                    ·
                      refine ⟨1653979211445961114273877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410611230522562971397005 1653979211445961114273877)
                      ·
                        rfl

theorem cell23_3221113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3221113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221113 prefixEnd_3221113 := by exact prefixLift 3221113
  have htrace : WordTrace (prefixWord ++ tailWord_3221113) baseStart_3221113 baseEnd_3221113 := by
    simpa [prefixWord, tailWord_3221113, baseEnd_3221113] using wordTrace_append hprefix tailTrace_3221113
  have hstable : (prefixWord ++ tailWord_3221113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221113).length < 2 ^ (prefixWord ++ tailWord_3221113).sum := by decide
  have hdescent : baseEnd_3221113 < baseStart_3221113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221127 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_3221127 : Nat := 118140960795 + 3221127 * 2 ^ 59
def prefixEnd_3221127 : Nat := 4983230072969 + 3 ^ 40 * 3221127 * 2
def baseEnd_3221127 : Nat := 1653986400175124059498813

theorem tailTrace_3221127 : CollatzResearch.WordTrace tailWord_3221127 prefixEnd_3221127 1653986400175124059498813 := by
  unfold tailWord_3221127
  simp only [CollatzResearch.WordTrace]
  refine ⟨117484153401414478539045635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78322768934276319026030423 117484153401414478539045635)
  ·
    refine ⟨176226230102121717808568453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117484153401414478539045635 176226230102121717808568453)
    ·
      refine ⟨33042418144147822089106585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176226230102121717808568453 33042418144147822089106585)
      ·
        refine ⟨24781813608110866566829939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33042418144147822089106585 24781813608110866566829939)
        ·
          refine ⟨37172720412166299850244909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24781813608110866566829939 37172720412166299850244909)
          ·
            refine ⟨13939770154562362443841841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37172720412166299850244909 13939770154562362443841841)
            ·
              refine ⟨10454827615921771832881381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13939770154562362443841841 10454827615921771832881381)
              ·
                refine ⟨1960280177985332218665259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10454827615921771832881381 1960280177985332218665259)
                ·
                  refine ⟨2940420266977998327997889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960280177985332218665259 2940420266977998327997889)
                  ·
                    refine ⟨2205315200233498745998417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2940420266977998327997889 2205315200233498745998417)
                    ·
                      refine ⟨1653986400175124059498813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205315200233498745998417 1653986400175124059498813)
                      ·
                        rfl

theorem cell23_3221127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_3221127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221127 prefixEnd_3221127 := by exact prefixLift 3221127
  have htrace : WordTrace (prefixWord ++ tailWord_3221127) baseStart_3221127 baseEnd_3221127 := by
    simpa [prefixWord, tailWord_3221127, baseEnd_3221127] using wordTrace_append hprefix tailTrace_3221127
  have hstable : (prefixWord ++ tailWord_3221127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221127).length < 2 ^ (prefixWord ++ tailWord_3221127).sum := by decide
  have hdescent : baseEnd_3221127 < baseStart_3221127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221129 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_3221129 : Nat := 118140960795 + 3221129 * 2 ^ 59
def prefixEnd_3221129 : Nat := 4983230072969 + 3 ^ 40 * 3221129 * 2
def baseEnd_3221129 : Nat := 551329142378811017224601

theorem tailTrace_3221129 : CollatzResearch.WordTrace tailWord_3221129 prefixEnd_3221129 551329142378811017224601 := by
  unfold tailWord_3221129
  simp only [CollatzResearch.WordTrace]
  refine ⟨117484226347407232880618441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78322817564938155253745627 117484226347407232880618441)
  ·
    refine ⟨88113169760555424660463831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117484226347407232880618441 88113169760555424660463831)
    ·
      refine ⟨132169754640833136990695747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88113169760555424660463831 132169754640833136990695747)
      ·
        refine ⟨198254631961249705486043621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132169754640833136990695747 198254631961249705486043621)
        ·
          refine ⟨37172743492734319778633179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198254631961249705486043621 37172743492734319778633179)
          ·
            refine ⟨55759115239101479667949769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37172743492734319778633179 55759115239101479667949769)
            ·
              refine ⟨41819336429326109750962327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55759115239101479667949769 41819336429326109750962327)
              ·
                refine ⟨62729004643989164626443491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41819336429326109750962327 62729004643989164626443491)
                ·
                  refine ⟨94093506965983746939665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62729004643989164626443491 94093506965983746939665237)
                  ·
                    refine ⟨551329142378811017224601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94093506965983746939665237 551329142378811017224601)
                    ·
                      rfl

theorem cell23_3221129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_3221129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221129 prefixEnd_3221129 := by exact prefixLift 3221129
  have htrace : WordTrace (prefixWord ++ tailWord_3221129) baseStart_3221129 baseEnd_3221129 := by
    simpa [prefixWord, tailWord_3221129, baseEnd_3221129] using wordTrace_append hprefix tailTrace_3221129
  have hstable : (prefixWord ++ tailWord_3221129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221129).length < 2 ^ (prefixWord ++ tailWord_3221129).sum := by decide
  have hdescent : baseEnd_3221129 < baseStart_3221129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221139 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_3221139 : Nat := 118140960795 + 3221139 * 2 ^ 59
def prefixEnd_3221139 : Nat := 4983230072969 + 3 ^ 40 * 3221139 * 2
def baseEnd_3221139 : Nat := 1653992561942978012548757

theorem tailTrace_3221139 : CollatzResearch.WordTrace tailWord_3221139 prefixEnd_3221139 1653992561942978012548757 := by
  unfold tailWord_3221139
  simp only [CollatzResearch.WordTrace]
  refine ⟨117484591077371004588482471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78323060718247336392321647 117484591077371004588482471)
  ·
    refine ⟨176226886616056506882723707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117484591077371004588482471 176226886616056506882723707)
    ·
      refine ⟨264340329924084760324085561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176226886616056506882723707 264340329924084760324085561)
      ·
        refine ⟨198255247443063570243064171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264340329924084760324085561 198255247443063570243064171)
        ·
          refine ⟨297382871164595355364596257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198255247443063570243064171 297382871164595355364596257)
          ·
            refine ⟨223037153373446516523447193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297382871164595355364596257 223037153373446516523447193)
            ·
              refine ⟨167277865030084887392585395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223037153373446516523447193 167277865030084887392585395)
              ·
                refine ⟨250916797545127331088878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167277865030084887392585395 250916797545127331088878093)
                ·
                  refine ⟨94093799079422749158329285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250916797545127331088878093 94093799079422749158329285)
                  ·
                    refine ⟨17642587327391765467186741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94093799079422749158329285 17642587327391765467186741)
                    ·
                      refine ⟨1653992561942978012548757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17642587327391765467186741 1653992561942978012548757)
                      ·
                        rfl

theorem cell23_3221139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_3221139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221139 prefixEnd_3221139 := by exact prefixLift 3221139
  have htrace : WordTrace (prefixWord ++ tailWord_3221139) baseStart_3221139 baseEnd_3221139 := by
    simpa [prefixWord, tailWord_3221139, baseEnd_3221139] using wordTrace_append hprefix tailTrace_3221139
  have hstable : (prefixWord ++ tailWord_3221139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221139).length < 2 ^ (prefixWord ++ tailWord_3221139).sum := by decide
  have hdescent : baseEnd_3221139 < baseStart_3221139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221143 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3221143 : Nat := 118140960795 + 3221143 * 2 ^ 59
def prefixEnd_3221143 : Nat := 4983230072969 + 3 ^ 40 * 3221143 * 2
def baseEnd_3221143 : Nat := 1653994615865595996898739

theorem tailTrace_3221143 : CollatzResearch.WordTrace tailWord_3221143 prefixEnd_3221143 1653994615865595996898739 := by
  unfold tailWord_3221143
  simp only [CollatzResearch.WordTrace]
  refine ⟨117484736969356513271628083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78323157979571008847752055 117484736969356513271628083)
  ·
    refine ⟨176227105454034769907442125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117484736969356513271628083 176227105454034769907442125)
    ·
      refine ⟨66085164545263038715290797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176227105454034769907442125 66085164545263038715290797)
      ·
        refine ⟨24781936704473639518234049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66085164545263038715290797 24781936704473639518234049)
        ·
          refine ⟨18586452528355229638675537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24781936704473639518234049 18586452528355229638675537)
          ·
            refine ⟨13939839396266422229006653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18586452528355229638675537 13939839396266422229006653)
            ·
              refine ⟨5227439773599908335877495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13939839396266422229006653 5227439773599908335877495)
              ·
                refine ⟨7841159660399862503816243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227439773599908335877495 7841159660399862503816243)
                ·
                  refine ⟨11761739490599793755724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841159660399862503816243 11761739490599793755724365)
                  ·
                    refine ⟨4410652308974922658396637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11761739490599793755724365 4410652308974922658396637)
                    ·
                      refine ⟨1653994615865595996898739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410652308974922658396637 1653994615865595996898739)
                      ·
                        rfl

theorem cell23_3221143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3221143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221143 prefixEnd_3221143 := by exact prefixLift 3221143
  have htrace : WordTrace (prefixWord ++ tailWord_3221143) baseStart_3221143 baseEnd_3221143 := by
    simpa [prefixWord, tailWord_3221143, baseEnd_3221143] using wordTrace_append hprefix tailTrace_3221143
  have hstable : (prefixWord ++ tailWord_3221143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221143).length < 2 ^ (prefixWord ++ tailWord_3221143).sum := by decide
  have hdescent : baseEnd_3221143 < baseStart_3221143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221150 : List Nat := [4, 3, 1, 1, 1, 4, 2, 7]
def baseStart_3221150 : Nat := 118140960795 + 3221150 * 2 ^ 59
def prefixEnd_3221150 : Nat := 4983230072969 + 3 ^ 40 * 3221150 * 2
def baseEnd_3221150 : Nat := 61259192971488054426341

theorem tailTrace_3221150 : CollatzResearch.WordTrace tailWord_3221150 prefixEnd_3221150 61259192971488054426341 := by
  unfold tailWord_3221150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14685624035041394183391613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78323328186887435644755269 14685624035041394183391613)
  ·
    refine ⟨5507109013140522818771855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14685624035041394183391613 5507109013140522818771855)
    ·
      refine ⟨8260663519710784228157783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507109013140522818771855 8260663519710784228157783)
      ·
        refine ⟨12390995279566176342236675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8260663519710784228157783 12390995279566176342236675)
        ·
          refine ⟨18586492919349264513355013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390995279566176342236675 18586492919349264513355013)
          ·
            refine ⟨3484967422377987096254065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18586492919349264513355013 3484967422377987096254065)
            ·
              refine ⟨2613725566783490322190549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484967422377987096254065 2613725566783490322190549)
              ·
                refine ⟨61259192971488054426341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2613725566783490322190549 61259192971488054426341)
                ·
                  rfl

theorem cell23_3221150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_3221150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221150 prefixEnd_3221150 := by exact prefixLift 3221150
  have htrace : WordTrace (prefixWord ++ tailWord_3221150) baseStart_3221150 baseEnd_3221150 := by
    simpa [prefixWord, tailWord_3221150, baseEnd_3221150] using wordTrace_append hprefix tailTrace_3221150
  have hstable : (prefixWord ++ tailWord_3221150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221150).length < 2 ^ (prefixWord ++ tailWord_3221150).sum := by decide
  have hdescent : baseEnd_3221150 < baseStart_3221150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221156 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3221156 : Nat := 118140960795 + 3221156 * 2 ^ 59
def prefixEnd_3221156 : Nat := 4983230072969 + 3 ^ 40 * 3221156 * 2
def baseEnd_3221156 : Nat := 1654001291114104446036179

theorem tailTrace_3221156 : CollatzResearch.WordTrace tailWord_3221156 prefixEnd_3221156 1654001291114104446036179 := by
  unfold tailWord_3221156
  simp only [CollatzResearch.WordTrace]
  refine ⟨58742605559154708245925661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78323474078872944327900881 58742605559154708245925661)
  ·
    refine ⟨22028477084683015592222123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58742605559154708245925661 22028477084683015592222123)
    ·
      refine ⟨33042715627024523388333185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22028477084683015592222123 33042715627024523388333185)
      ·
        refine ⟨24782036720268392541249889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33042715627024523388333185 24782036720268392541249889)
        ·
          refine ⟨18586527540201294405937417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24782036720268392541249889 18586527540201294405937417)
          ·
            refine ⟨13939895655150970804453063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18586527540201294405937417 13939895655150970804453063)
            ·
              refine ⟨20909843482726456206679595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13939895655150970804453063 20909843482726456206679595)
              ·
                refine ⟨31364765224089684310019393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20909843482726456206679595 31364765224089684310019393)
                ·
                  refine ⟨23523573918067263232514545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31364765224089684310019393 23523573918067263232514545)
                  ·
                    refine ⟨17642680438550447424385909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23523573918067263232514545 17642680438550447424385909)
                    ·
                      refine ⟨1654001291114104446036179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17642680438550447424385909 1654001291114104446036179)
                      ·
                        rfl

theorem cell23_3221156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3221156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221156 prefixEnd_3221156 := by exact prefixLift 3221156
  have htrace : WordTrace (prefixWord ++ tailWord_3221156) baseStart_3221156 baseEnd_3221156 := by
    simpa [prefixWord, tailWord_3221156, baseEnd_3221156] using wordTrace_append hprefix tailTrace_3221156
  have hstable : (prefixWord ++ tailWord_3221156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221156).length < 2 ^ (prefixWord ++ tailWord_3221156).sum := by decide
  have hdescent : baseEnd_3221156 < baseStart_3221156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221170 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_3221170 : Nat := 118140960795 + 3221170 * 2 ^ 59
def prefixEnd_3221170 : Nat := 4983230072969 + 3 ^ 40 * 3221170 * 2
def baseEnd_3221170 : Nat := 1654008479843267391261115

theorem tailTrace_3221170 : CollatzResearch.WordTrace tailWord_3221170 prefixEnd_3221170 1654008479843267391261115 := by
  unfold tailWord_3221170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371430435064674220715241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78323814493505797921907309 29371430435064674220715241)
  ·
    refine ⟨22028572826298505665536431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29371430435064674220715241 22028572826298505665536431)
    ·
      refine ⟨33042859239447758498304647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22028572826298505665536431 33042859239447758498304647)
      ·
        refine ⟨49564288859171637747456971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33042859239447758498304647 49564288859171637747456971)
        ·
          refine ⟨74346433288757456621185457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49564288859171637747456971 74346433288757456621185457)
          ·
            refine ⟨55759824966568092465889093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74346433288757456621185457 55759824966568092465889093)
            ·
              refine ⟨10454967181231517337354205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55759824966568092465889093 10454967181231517337354205)
              ·
                refine ⟨3920612692961819001507827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10454967181231517337354205 3920612692961819001507827)
                ·
                  refine ⟨5880919039442728502261741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920612692961819001507827 5880919039442728502261741)
                  ·
                    refine ⟨2205344639791023188348153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5880919039442728502261741 2205344639791023188348153)
                    ·
                      refine ⟨1654008479843267391261115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205344639791023188348153 1654008479843267391261115)
                      ·
                        rfl

theorem cell23_3221170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_3221170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221170 prefixEnd_3221170 := by exact prefixLift 3221170
  have htrace : WordTrace (prefixWord ++ tailWord_3221170) baseStart_3221170 baseEnd_3221170 := by
    simpa [prefixWord, tailWord_3221170, baseEnd_3221170] using wordTrace_append hprefix tailTrace_3221170
  have hstable : (prefixWord ++ tailWord_3221170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221170).length < 2 ^ (prefixWord ++ tailWord_3221170).sum := by decide
  have hdescent : baseEnd_3221170 < baseStart_3221170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221194 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_3221194 : Nat := 118140960795 + 3221194 * 2 ^ 59
def prefixEnd_3221194 : Nat := 4983230072969 + 3 ^ 40 * 3221194 * 2
def baseEnd_3221194 : Nat := 1654020803378975297361005

theorem tailTrace_3221194 : CollatzResearch.WordTrace tailWord_3221194 prefixEnd_3221194 1654020803378975297361005 := by
  unfold tailWord_3221194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371649273042937245433659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78324398061447832654489757 29371649273042937245433659)
  ·
    refine ⟨44057473909564405868150489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29371649273042937245433659 44057473909564405868150489)
    ·
      refine ⟨33043105432173304401112867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44057473909564405868150489 33043105432173304401112867)
      ·
        refine ⟨49564658148259956601669301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33043105432173304401112867 49564658148259956601669301)
        ·
          refine ⟨4646686701399370931406497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49564658148259956601669301 4646686701399370931406497)
          ·
            refine ⟨3485015026049528198554873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646686701399370931406497 3485015026049528198554873)
            ·
              refine ⟨2613761269537146148916155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485015026049528198554873 2613761269537146148916155)
              ·
                refine ⟨3920641904305719223374233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613761269537146148916155 3920641904305719223374233)
                ·
                  refine ⟨2940481428229289417530675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920641904305719223374233 2940481428229289417530675)
                  ·
                    refine ⟨4410722142343934126296013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2940481428229289417530675 4410722142343934126296013)
                    ·
                      refine ⟨1654020803378975297361005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410722142343934126296013 1654020803378975297361005)
                      ·
                        rfl

theorem cell23_3221194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_3221194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221194 prefixEnd_3221194 := by exact prefixLift 3221194
  have htrace : WordTrace (prefixWord ++ tailWord_3221194) baseStart_3221194 baseEnd_3221194 := by
    simpa [prefixWord, tailWord_3221194, baseEnd_3221194] using wordTrace_append hprefix tailTrace_3221194
  have hstable : (prefixWord ++ tailWord_3221194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221194).length < 2 ^ (prefixWord ++ tailWord_3221194).sum := by decide
  have hdescent : baseEnd_3221194 < baseStart_3221194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221204 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3221204 : Nat := 118140960795 + 3221204 * 2 ^ 59
def prefixEnd_3221204 : Nat := 4983230072969 + 3 ^ 40 * 3221204 * 2
def baseEnd_3221204 : Nat := 1654025938185520258235959

theorem tailTrace_3221204 : CollatzResearch.WordTrace tailWord_3221204 prefixEnd_3221204 1654025938185520258235959 := by
  unfold tailWord_3221204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58743480911067760344799333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78324641214757013793065777 58743480911067760344799333)
  ·
    refine ⟨11014402670825205064649875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58743480911067760344799333 11014402670825205064649875)
    ·
      refine ⟨16521604006237807596974813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014402670825205064649875 16521604006237807596974813)
      ·
        refine ⟨6195601502339177848865555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16521604006237807596974813 6195601502339177848865555)
        ·
          refine ⟨9293402253508766773298333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195601502339177848865555 9293402253508766773298333)
          ·
            refine ⟨3485025845065787539986875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9293402253508766773298333 3485025845065787539986875)
            ·
              refine ⟨5227538767598681309980313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485025845065787539986875 5227538767598681309980313)
              ·
                refine ⟨3920654075699010982485235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5227538767598681309980313 3920654075699010982485235)
                ·
                  refine ⟨5880981113548516473727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920654075699010982485235 5880981113548516473727853)
                  ·
                    refine ⟨2205367917580693677647945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5880981113548516473727853 2205367917580693677647945)
                    ·
                      refine ⟨1654025938185520258235959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205367917580693677647945 1654025938185520258235959)
                      ·
                        rfl

theorem cell23_3221204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3221204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221204 prefixEnd_3221204 := by exact prefixLift 3221204
  have htrace : WordTrace (prefixWord ++ tailWord_3221204) baseStart_3221204 baseEnd_3221204 := by
    simpa [prefixWord, tailWord_3221204, baseEnd_3221204] using wordTrace_append hprefix tailTrace_3221204
  have hstable : (prefixWord ++ tailWord_3221204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221204).length < 2 ^ (prefixWord ++ tailWord_3221204).sum := by decide
  have hdescent : baseEnd_3221204 < baseStart_3221204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221250 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3221250 : Nat := 118140960795 + 3221250 * 2 ^ 59
def prefixEnd_3221250 : Nat := 4983230072969 + 3 ^ 40 * 3221250 * 2
def baseEnd_3221250 : Nat := 1654049558295627078260747

theorem tailTrace_3221250 : CollatzResearch.WordTrace tailWord_3221250 prefixEnd_3221250 1654049558295627078260747 := by
  unfold tailWord_3221250
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372159894992217636443301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78325759719979247030515469 29372159894992217636443301)
  ·
    refine ⟨5507279980311040806833119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29372159894992217636443301 5507279980311040806833119)
    ·
      refine ⟨8260919970466561210249679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507279980311040806833119 8260919970466561210249679)
      ·
        refine ⟨12391379955699841815374519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8260919970466561210249679 12391379955699841815374519)
        ·
          refine ⟨18587069933549762723061779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391379955699841815374519 18587069933549762723061779)
          ·
            refine ⟨27880604900324644084592669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587069933549762723061779 27880604900324644084592669)
            ·
              refine ⟨10455226837621741531722251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27880604900324644084592669 10455226837621741531722251)
              ·
                refine ⟨15682840256432612297583377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10455226837621741531722251 15682840256432612297583377)
                ·
                  refine ⟨11762130192324459223187533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15682840256432612297583377 11762130192324459223187533)
                  ·
                    refine ⟨4410798822121672208695325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11762130192324459223187533 4410798822121672208695325)
                    ·
                      refine ⟨1654049558295627078260747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410798822121672208695325 1654049558295627078260747)
                      ·
                        rfl

theorem cell23_3221250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3221250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221250 prefixEnd_3221250 := by exact prefixLift 3221250
  have htrace : WordTrace (prefixWord ++ tailWord_3221250) baseStart_3221250 baseEnd_3221250 := by
    simpa [prefixWord, tailWord_3221250, baseEnd_3221250] using wordTrace_append hprefix tailTrace_3221250
  have hstable : (prefixWord ++ tailWord_3221250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221250).length < 2 ^ (prefixWord ++ tailWord_3221250).sum := by decide
  have hdescent : baseEnd_3221250 < baseStart_3221250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221310 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3221310 : Nat := 118140960795 + 3221310 * 2 ^ 59
def prefixEnd_3221310 : Nat := 4983230072969 + 3 ^ 40 * 3221310 * 2
def baseEnd_3221310 : Nat := 1654080367134896843510471

theorem tailTrace_3221310 : CollatzResearch.WordTrace tailWord_3221310 prefixEnd_3221310 1654080367134896843510471 := by
  unfold tailWord_3221310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686353494968937599119673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78327218639834333861971589 14686353494968937599119673)
  ·
    refine ⟨11014765121226703199339755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14686353494968937599119673 11014765121226703199339755)
    ·
      refine ⟨16522147681840054799009633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014765121226703199339755 16522147681840054799009633)
      ·
        refine ⟨12391610761380041099257225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16522147681840054799009633 12391610761380041099257225)
        ·
          refine ⟨9293708071035030824442919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12391610761380041099257225 9293708071035030824442919)
          ·
            refine ⟨13940562106552546236664379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293708071035030824442919 13940562106552546236664379)
            ·
              refine ⟨20910843159828819354996569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13940562106552546236664379 20910843159828819354996569)
              ·
                refine ⟨15683132369871614516247427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20910843159828819354996569 15683132369871614516247427)
                ·
                  refine ⟨23524698554807421774371141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15683132369871614516247427 23524698554807421774371141)
                  ·
                    refine ⟨4410880979026391582694589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23524698554807421774371141 4410880979026391582694589)
                    ·
                      refine ⟨1654080367134896843510471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410880979026391582694589 1654080367134896843510471)
                      ·
                        rfl

theorem cell23_3221310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3221310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221310 prefixEnd_3221310 := by exact prefixLift 3221310
  have htrace : WordTrace (prefixWord ++ tailWord_3221310) baseStart_3221310 baseEnd_3221310 := by
    simpa [prefixWord, tailWord_3221310, baseEnd_3221310] using wordTrace_append hprefix tailTrace_3221310
  have hstable : (prefixWord ++ tailWord_3221310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221310).length < 2 ^ (prefixWord ++ tailWord_3221310).sum := by decide
  have hdescent : baseEnd_3221310 < baseStart_3221310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221357 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3221357 : Nat := 118140960795 + 3221357 * 2 ^ 59
def prefixEnd_3221357 : Nat := 4983230072969 + 3 ^ 40 * 3221357 * 2
def baseEnd_3221357 : Nat := 1654104500725658159622755

theorem tailTrace_3221357 : CollatzResearch.WordTrace tailWord_3221357 prefixEnd_3221357 1654104500725658159622755 := by
  unfold tailWord_3221357
  simp only [CollatzResearch.WordTrace]
  refine ⟨117492542190581227819918325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78328361460387485213278883 117492542190581227819918325)
  ·
    refine ⟨11014925830366990108117343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117492542190581227819918325 11014925830366990108117343)
    ·
      refine ⟨16522388745550485162176015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014925830366990108117343 16522388745550485162176015)
      ·
        refine ⟨24783583118325727743264023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522388745550485162176015 24783583118325727743264023)
        ·
          refine ⟨37175374677488591614896035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24783583118325727743264023 37175374677488591614896035)
          ·
            refine ⟨55763062016232887422344053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175374677488591614896035 55763062016232887422344053)
            ·
              refine ⟨5227787064021833195844755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55763062016232887422344053 5227787064021833195844755)
              ·
                refine ⟨7841680596032749793767133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227787064021833195844755 7841680596032749793767133)
                ·
                  refine ⟨2940630223512281172662675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7841680596032749793767133 2940630223512281172662675)
                  ·
                    refine ⟨4410945335268421758994013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2940630223512281172662675 4410945335268421758994013)
                    ·
                      refine ⟨1654104500725658159622755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4410945335268421758994013 1654104500725658159622755)
                      ·
                        rfl

theorem cell23_3221357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3221357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221357 prefixEnd_3221357 := by exact prefixLift 3221357
  have htrace : WordTrace (prefixWord ++ tailWord_3221357) baseStart_3221357 baseEnd_3221357 := by
    simpa [prefixWord, tailWord_3221357, baseEnd_3221357] using wordTrace_append hprefix tailTrace_3221357
  have hstable : (prefixWord ++ tailWord_3221357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221357).length < 2 ^ (prefixWord ++ tailWord_3221357).sum := by decide
  have hdescent : baseEnd_3221357 < baseStart_3221357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221363 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4]
def baseStart_3221363 : Nat := 118140960795 + 3221363 * 2 ^ 59
def prefixEnd_3221363 : Nat := 4983230072969 + 3 ^ 40 * 3221363 * 2
def baseEnd_3221363 : Nat := 1654107581609585136147727

theorem tailTrace_3221363 : CollatzResearch.WordTrace tailWord_3221363 prefixEnd_3221363 1654107581609585136147727 := by
  unfold tailWord_3221363
  simp only [CollatzResearch.WordTrace]
  refine ⟨117492761028559490844636743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78328507352372993896424495 117492761028559490844636743)
  ·
    refine ⟨176239141542839236266955115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117492761028559490844636743 176239141542839236266955115)
    ·
      refine ⟨264358712314258854400432673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176239141542839236266955115 264358712314258854400432673)
      ·
        refine ⟨198269034235694140800324505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264358712314258854400432673 198269034235694140800324505)
        ·
          refine ⟨148701775676770605600243379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198269034235694140800324505 148701775676770605600243379)
          ·
            refine ⟨223052663515155908400365069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148701775676770605600243379 223052663515155908400365069)
            ·
              refine ⟨83644748818183465650136901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223052663515155908400365069 83644748818183465650136901)
              ·
                refine ⟨15683390403409399809400669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83644748818183465650136901 15683390403409399809400669)
                ·
                  refine ⟨5881271401278524928525251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15683390403409399809400669 5881271401278524928525251)
                  ·
                    refine ⟨8821907101917787392787877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881271401278524928525251 8821907101917787392787877)
                    ·
                      refine ⟨1654107581609585136147727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8821907101917787392787877 1654107581609585136147727)
                      ·
                        rfl

theorem cell23_3221363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_3221363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221363 prefixEnd_3221363 := by exact prefixLift 3221363
  have htrace : WordTrace (prefixWord ++ tailWord_3221363) baseStart_3221363 baseEnd_3221363 := by
    simpa [prefixWord, tailWord_3221363, baseEnd_3221363] using wordTrace_append hprefix tailTrace_3221363
  have hstable : (prefixWord ++ tailWord_3221363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221363).length < 2 ^ (prefixWord ++ tailWord_3221363).sum := by decide
  have hdescent : baseEnd_3221363 < baseStart_3221363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221373 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_3221373 : Nat := 118140960795 + 3221373 * 2 ^ 59
def prefixEnd_3221373 : Nat := 4983230072969 + 3 ^ 40 * 3221373 * 2
def baseEnd_3221373 : Nat := 551370905472043365674227

theorem tailTrace_3221373 : CollatzResearch.WordTrace tailWord_3221373 prefixEnd_3221373 551370905472043365674227 := by
  unfold tailWord_3221373
  simp only [CollatzResearch.WordTrace]
  refine ⟨117493125758523262552500773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78328750505682175035000515 117493125758523262552500773)
  ·
    refine ⟨22029961079723111728593895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117493125758523262552500773 22029961079723111728593895)
    ·
      refine ⟨33044941619584667592890843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22029961079723111728593895 33044941619584667592890843)
      ·
        refine ⟨49567412429377001389336265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33044941619584667592890843 49567412429377001389336265)
        ·
          refine ⟨37175559322032751042002199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49567412429377001389336265 37175559322032751042002199)
          ·
            refine ⟨55763338983049126563003299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175559322032751042002199 55763338983049126563003299)
            ·
              refine ⟨83645008474573689844504949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55763338983049126563003299 83645008474573689844504949)
              ·
                refine ⟨7841719544491283422922339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83645008474573689844504949 7841719544491283422922339)
                ·
                  refine ⟨11762579316736925134383509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841719544491283422922339 11762579316736925134383509)
                  ·
                    refine ⟨551370905472043365674227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11762579316736925134383509 551370905472043365674227)
                    ·
                      rfl

theorem cell23_3221373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_3221373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221373 prefixEnd_3221373 := by exact prefixLift 3221373
  have htrace : WordTrace (prefixWord ++ tailWord_3221373) baseStart_3221373 baseEnd_3221373 := by
    simpa [prefixWord, tailWord_3221373, baseEnd_3221373] using wordTrace_append hprefix tailTrace_3221373
  have hstable : (prefixWord ++ tailWord_3221373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221373).length < 2 ^ (prefixWord ++ tailWord_3221373).sum := by decide
  have hdescent : baseEnd_3221373 < baseStart_3221373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221377 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3221377 : Nat := 118140960795 + 3221377 * 2 ^ 59
def prefixEnd_3221377 : Nat := 4983230072969 + 3 ^ 40 * 3221377 * 2
def baseEnd_3221377 : Nat := 551371590112916027124221

theorem tailTrace_3221377 : CollatzResearch.WordTrace tailWord_3221377 prefixEnd_3221377 551371590112916027124221 := by
  unfold tailWord_3221377
  simp only [CollatzResearch.WordTrace]
  refine ⟨117493271650508771235646385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78328847767005847490430923 117493271650508771235646385)
  ·
    refine ⟨88119953737881578426734789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117493271650508771235646385 88119953737881578426734789)
    ·
      refine ⟨16522491325852795955012773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88119953737881578426734789 16522491325852795955012773)
      ·
        refine ⟨3097967123597399241564895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16522491325852795955012773 3097967123597399241564895)
        ·
          refine ⟨4646950685396098862347343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097967123597399241564895 4646950685396098862347343)
          ·
            refine ⟨6970426028094148293521015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646950685396098862347343 6970426028094148293521015)
            ·
              refine ⟨10455639042141222440281523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970426028094148293521015 10455639042141222440281523)
              ·
                refine ⟨15683458563211833660422285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10455639042141222440281523 15683458563211833660422285)
                ·
                  refine ⟨5881296961204437622658357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15683458563211833660422285 5881296961204437622658357)
                  ·
                    refine ⟨551371590112916027124221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5881296961204437622658357 551371590112916027124221)
                    ·
                      rfl

theorem cell23_3221377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3221377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221377 prefixEnd_3221377 := by exact prefixLift 3221377
  have htrace : WordTrace (prefixWord ++ tailWord_3221377) baseStart_3221377 baseEnd_3221377 := by
    simpa [prefixWord, tailWord_3221377, baseEnd_3221377] using wordTrace_append hprefix tailTrace_3221377
  have hstable : (prefixWord ++ tailWord_3221377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221377).length < 2 ^ (prefixWord ++ tailWord_3221377).sum := by decide
  have hdescent : baseEnd_3221377 < baseStart_3221377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221380 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_3221380 : Nat := 118140960795 + 3221380 * 2 ^ 59
def prefixEnd_3221380 : Nat := 4983230072969 + 3 ^ 40 * 3221380 * 2
def baseEnd_3221380 : Nat := 1654116310780711569635149

theorem tailTrace_3221380 : CollatzResearch.WordTrace tailWord_3221380 prefixEnd_3221380 1654116310780711569635149 := by
  unfold tailWord_3221380
  simp only [CollatzResearch.WordTrace]
  refine ⟨58746690534748951374002797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78328920712998601832003729 58746690534748951374002797)
  ·
    refine ⟨22030008950530856765251049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58746690534748951374002797 22030008950530856765251049)
    ·
      refine ⟨16522506712898142573938287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22030008950530856765251049 16522506712898142573938287)
      ·
        refine ⟨24783760069347213860907431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522506712898142573938287 24783760069347213860907431)
        ·
          refine ⟨37175640104020820791361147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24783760069347213860907431 37175640104020820791361147)
          ·
            refine ⟨55763460156031231187041721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175640104020820791361147 55763460156031231187041721)
            ·
              refine ⟨41822595117023423390281291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55763460156031231187041721 41822595117023423390281291)
              ·
                refine ⟨62733892675535135085421937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41822595117023423390281291 62733892675535135085421937)
                ·
                  refine ⟨47050419506651351314066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62733892675535135085421937 47050419506651351314066453)
                  ·
                    refine ⟨2205488414374282092846865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47050419506651351314066453 2205488414374282092846865)
                    ·
                      refine ⟨1654116310780711569635149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205488414374282092846865 1654116310780711569635149)
                      ·
                        rfl

theorem cell23_3221380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_3221380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221380 prefixEnd_3221380 := by exact prefixLift 3221380
  have htrace : WordTrace (prefixWord ++ tailWord_3221380) baseStart_3221380 baseEnd_3221380 := by
    simpa [prefixWord, tailWord_3221380, baseEnd_3221380] using wordTrace_append hprefix tailTrace_3221380
  have hstable : (prefixWord ++ tailWord_3221380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221380).length < 2 ^ (prefixWord ++ tailWord_3221380).sum := by decide
  have hdescent : baseEnd_3221380 < baseStart_3221380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221384 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_3221384 : Nat := 118140960795 + 3221384 * 2 ^ 59
def prefixEnd_3221384 : Nat := 4983230072969 + 3 ^ 40 * 3221384 * 2
def baseEnd_3221384 : Nat := 1654118364703329553985131

theorem tailTrace_3221384 : CollatzResearch.WordTrace tailWord_3221384 prefixEnd_3221384 1654118364703329553985131 := by
  unfold tailWord_3221384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58746763480741705715575603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78329017974322274287434137 58746763480741705715575603)
  ·
    refine ⟨88120145221112558573363405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58746763480741705715575603 88120145221112558573363405)
    ·
      refine ⟨33045054457917209465011277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88120145221112558573363405 33045054457917209465011277)
      ·
        refine ⟨12391895421718953549379229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33045054457917209465011277 12391895421718953549379229)
        ·
          refine ⟨4646960783144607581017211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12391895421718953549379229 4646960783144607581017211)
          ·
            refine ⟨6970441174716911371525817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646960783144607581017211 6970441174716911371525817)
            ·
              refine ⟨5227830881037683528644363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6970441174716911371525817 5227830881037683528644363)
              ·
                refine ⟨7841746321556525292966545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227830881037683528644363 7841746321556525292966545)
                ·
                  refine ⟨5881309741167393969724909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7841746321556525292966545 5881309741167393969724909)
                  ·
                    refine ⟨2205491152937772738646841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5881309741167393969724909 2205491152937772738646841)
                    ·
                      refine ⟨1654118364703329553985131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205491152937772738646841 1654118364703329553985131)
                      ·
                        rfl

theorem cell23_3221384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_3221384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221384 prefixEnd_3221384 := by exact prefixLift 3221384
  have htrace : WordTrace (prefixWord ++ tailWord_3221384) baseStart_3221384 baseEnd_3221384 := by
    simpa [prefixWord, tailWord_3221384, baseEnd_3221384] using wordTrace_append hprefix tailTrace_3221384
  have hstable : (prefixWord ++ tailWord_3221384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221384).length < 2 ^ (prefixWord ++ tailWord_3221384).sum := by decide
  have hdescent : baseEnd_3221384 < baseStart_3221384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221393 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3221393 : Nat := 118140960795 + 3221393 * 2 ^ 59
def prefixEnd_3221393 : Nat := 4983230072969 + 3 ^ 40 * 3221393 * 2
def baseEnd_3221393 : Nat := 1654122986029220018772589

theorem tailTrace_3221393 : CollatzResearch.WordTrace tailWord_3221393 prefixEnd_3221393 1654122986029220018772589 := by
  unfold tailWord_3221393
  simp only [CollatzResearch.WordTrace]
  refine ⟨117493855218450805968228833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78329236812300537312152555 117493855218450805968228833)
  ·
    refine ⟨88120391413838104476171625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117493855218450805968228833 88120391413838104476171625)
    ·
      refine ⟨66090293560378578357128719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88120391413838104476171625 66090293560378578357128719)
      ·
        refine ⟨99135440340567867535693079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66090293560378578357128719 99135440340567867535693079)
        ·
          refine ⟨148703160510851801303539619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99135440340567867535693079 148703160510851801303539619)
          ·
            refine ⟨223054740766277701955309429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148703160510851801303539619 223054740766277701955309429)
            ·
              refine ⟨20911381946838534558310259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223054740766277701955309429 20911381946838534558310259)
              ·
                refine ⟨31367072920257801837465389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20911381946838534558310259 31367072920257801837465389)
                ·
                  refine ⟨11762652345096675689049521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31367072920257801837465389 11762652345096675689049521)
                  ·
                    refine ⟨8821989258822506766787141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11762652345096675689049521 8821989258822506766787141)
                    ·
                      refine ⟨1654122986029220018772589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8821989258822506766787141 1654122986029220018772589)
                      ·
                        rfl

theorem cell23_3221393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3221393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221393 prefixEnd_3221393 := by exact prefixLift 3221393
  have htrace : WordTrace (prefixWord ++ tailWord_3221393) baseStart_3221393 baseEnd_3221393 := by
    simpa [prefixWord, tailWord_3221393, baseEnd_3221393] using wordTrace_append hprefix tailTrace_3221393
  have hstable : (prefixWord ++ tailWord_3221393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221393).length < 2 ^ (prefixWord ++ tailWord_3221393).sum := by decide
  have hdescent : baseEnd_3221393 < baseStart_3221393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221394 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3221394 : Nat := 118140960795 + 3221394 * 2 ^ 59
def prefixEnd_3221394 : Nat := 4983230072969 + 3 ^ 40 * 3221394 * 2
def baseEnd_3221394 : Nat := 551374499836624838286695

theorem tailTrace_3221394 : CollatzResearch.WordTrace tailWord_3221394 prefixEnd_3221394 551374499836624838286695 := by
  unfold tailWord_3221394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373472922861795784753809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78329261127631455426010157 29373472922861795784753809)
  ·
    refine ⟨22030104692146346838565357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29373472922861795784753809 22030104692146346838565357)
    ·
      refine ⟨8261289259554880064462009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22030104692146346838565357 8261289259554880064462009)
      ·
        refine ⟨6195966944666160048346507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8261289259554880064462009 6195966944666160048346507)
        ·
          refine ⟨9293950416999240072519761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195966944666160048346507 9293950416999240072519761)
          ·
            refine ⟨6970462812749430054389821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293950416999240072519761 6970462812749430054389821)
            ·
              refine ⟨2613923554781036270396183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6970462812749430054389821 2613923554781036270396183)
              ·
                refine ⟨3920885332171554405594275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613923554781036270396183 3920885332171554405594275)
                ·
                  refine ⟨5881327998257331608391413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920885332171554405594275 5881327998257331608391413)
                  ·
                    refine ⟨551374499836624838286695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5881327998257331608391413 551374499836624838286695)
                    ·
                      rfl

theorem cell23_3221394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3221394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221394 prefixEnd_3221394 := by exact prefixLift 3221394
  have htrace : WordTrace (prefixWord ++ tailWord_3221394) baseStart_3221394 baseEnd_3221394 := by
    simpa [prefixWord, tailWord_3221394, baseEnd_3221394] using wordTrace_append hprefix tailTrace_3221394
  have hstable : (prefixWord ++ tailWord_3221394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221394).length < 2 ^ (prefixWord ++ tailWord_3221394).sum := by decide
  have hdescent : baseEnd_3221394 < baseStart_3221394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221397 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_3221397 : Nat := 118140960795 + 3221397 * 2 ^ 59
def prefixEnd_3221397 : Nat := 4983230072969 + 3 ^ 40 * 3221397 * 2
def baseEnd_3221397 : Nat := 1654125039951838003122571

theorem tailTrace_3221397 : CollatzResearch.WordTrace tailWord_3221397 prefixEnd_3221397 1654125039951838003122571 := by
  unfold tailWord_3221397
  simp only [CollatzResearch.WordTrace]
  refine ⟨117494001110436314651374445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78329334073624209767582963 117494001110436314651374445)
  ·
    refine ⟨44060250416413617994265417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117494001110436314651374445 44060250416413617994265417)
    ·
      refine ⟨33045187812310213495699063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44060250416413617994265417 33045187812310213495699063)
      ·
        refine ⟨49567781718465320243548595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33045187812310213495699063 49567781718465320243548595)
        ·
          refine ⟨74351672577697980365322893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49567781718465320243548595 74351672577697980365322893)
          ·
            refine ⟨27881877216636742636996085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74351672577697980365322893 27881877216636742636996085)
            ·
              refine ⟨2613925989059694622218383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27881877216636742636996085 2613925989059694622218383)
              ·
                refine ⟨3920888983589541933327575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613925989059694622218383 3920888983589541933327575)
                ·
                  refine ⟨5881333475384312899991363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920888983589541933327575 5881333475384312899991363)
                  ·
                    refine ⟨8822000213076469349987045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881333475384312899991363 8822000213076469349987045)
                    ·
                      refine ⟨1654125039951838003122571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8822000213076469349987045 1654125039951838003122571)
                      ·
                        rfl

theorem cell23_3221397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_3221397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221397 prefixEnd_3221397 := by exact prefixLift 3221397
  have htrace : WordTrace (prefixWord ++ tailWord_3221397) baseStart_3221397 baseEnd_3221397 := by
    simpa [prefixWord, tailWord_3221397, baseEnd_3221397] using wordTrace_append hprefix tailTrace_3221397
  have hstable : (prefixWord ++ tailWord_3221397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221397).length < 2 ^ (prefixWord ++ tailWord_3221397).sum := by decide
  have hdescent : baseEnd_3221397 < baseStart_3221397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221433 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_3221433 : Nat := 118140960795 + 3221433 * 2 ^ 59
def prefixEnd_3221433 : Nat := 4983230072969 + 3 ^ 40 * 3221433 * 2
def baseEnd_3221433 : Nat := 551381175085133287424135

theorem tailTrace_3221433 : CollatzResearch.WordTrace tailWord_3221433 prefixEnd_3221433 551381175085133287424135 := by
  unfold tailWord_3221433
  simp only [CollatzResearch.WordTrace]
  refine ⟨117495314138305892799684953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78330209425537261866456635 117495314138305892799684953)
  ·
    refine ⟨88121485603729419599763715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117495314138305892799684953 88121485603729419599763715)
    ·
      refine ⟨132182228405594129399645573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88121485603729419599763715 132182228405594129399645573)
      ·
        refine ⟨24784167826048899262433545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132182228405594129399645573 24784167826048899262433545)
        ·
          refine ⟨18588125869536674446825159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24784167826048899262433545 18588125869536674446825159)
          ·
            refine ⟨27882188804305011670237739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18588125869536674446825159 27882188804305011670237739)
            ·
              refine ⟨41823283206457517505356609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27882188804305011670237739 41823283206457517505356609)
              ·
                refine ⟨31367462404843138129017457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41823283206457517505356609 31367462404843138129017457)
                ·
                  refine ⟨23525596803632353596763093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31367462404843138129017457 23525596803632353596763093)
                  ·
                    refine ⟨551381175085133287424135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23525596803632353596763093 551381175085133287424135)
                    ·
                      rfl

theorem cell23_3221433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_3221433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221433 prefixEnd_3221433 := by exact prefixLift 3221433
  have htrace : WordTrace (prefixWord ++ tailWord_3221433) baseStart_3221433 baseEnd_3221433 := by
    simpa [prefixWord, tailWord_3221433, baseEnd_3221433] using wordTrace_append hprefix tailTrace_3221433
  have hstable : (prefixWord ++ tailWord_3221433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221433).length < 2 ^ (prefixWord ++ tailWord_3221433).sum := by decide
  have hdescent : baseEnd_3221433 < baseStart_3221433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221463 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 6]
def baseStart_3221463 : Nat := 118140960795 + 3221463 * 2 ^ 59
def prefixEnd_3221463 : Nat := 4983230072969 + 3 ^ 40 * 3221463 * 2
def baseEnd_3221463 : Nat := 551386309891678248299089

theorem tailTrace_3221463 : CollatzResearch.WordTrace tailWord_3221463 prefixEnd_3221463 551386309891678248299089 := by
  unfold tailWord_3221463
  simp only [CollatzResearch.WordTrace]
  refine ⟨117496408328197207923277043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78330938885464805282184695 117496408328197207923277043)
  ·
    refine ⟨176244612492295811884915565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117496408328197207923277043 176244612492295811884915565)
    ·
      refine ⟨66091729684610929456843337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176244612492295811884915565 66091729684610929456843337)
      ·
        refine ⟨49568797263458197092632503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66091729684610929456843337 49568797263458197092632503)
        ·
          refine ⟨74353195895187295638948755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49568797263458197092632503 74353195895187295638948755)
          ·
            refine ⟨111529793842780943458423133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74353195895187295638948755 111529793842780943458423133)
            ·
              refine ⟨41823672691042853796908675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111529793842780943458423133 41823672691042853796908675)
              ·
                refine ⟨62735509036564280695363013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41823672691042853796908675 62735509036564280695363013)
                ·
                  refine ⟨11762907944355802630380565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62735509036564280695363013 11762907944355802630380565)
                  ·
                    refine ⟨551386309891678248299089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11762907944355802630380565 551386309891678248299089)
                    ·
                      rfl

theorem cell23_3221463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_3221463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221463 prefixEnd_3221463 := by exact prefixLift 3221463
  have htrace : WordTrace (prefixWord ++ tailWord_3221463) baseStart_3221463 baseEnd_3221463 := by
    simpa [prefixWord, tailWord_3221463, baseEnd_3221463] using wordTrace_append hprefix tailTrace_3221463
  have hstable : (prefixWord ++ tailWord_3221463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221463).length < 2 ^ (prefixWord ++ tailWord_3221463).sum := by decide
  have hdescent : baseEnd_3221463 < baseStart_3221463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221513 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3221513 : Nat := 118140960795 + 3221513 * 2 ^ 59
def prefixEnd_3221513 : Nat := 4983230072969 + 3 ^ 40 * 3221513 * 2
def baseEnd_3221513 : Nat := 1654184603707759549272037

theorem tailTrace_3221513 : CollatzResearch.WordTrace tailWord_3221513 prefixEnd_3221513 1654184603707759549272037 := by
  unfold tailWord_3221513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117498231978016066462597193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78332154652010710975064795 117498231978016066462597193)
  ·
    refine ⟨88123673983512049846947895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117498231978016066462597193 88123673983512049846947895)
    ·
      refine ⟨132185510975268074770421843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88123673983512049846947895 132185510975268074770421843)
      ·
        refine ⟨198278266462902112155632765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132185510975268074770421843 198278266462902112155632765)
        ·
          refine ⟨74354349923588292058362287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198278266462902112155632765 74354349923588292058362287)
          ·
            refine ⟨111531524885382438087543431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74354349923588292058362287 111531524885382438087543431)
            ·
              refine ⟨167297287328073657131315147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111531524885382438087543431 167297287328073657131315147)
              ·
                refine ⟨250945930992110485696972721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167297287328073657131315147 250945930992110485696972721)
                ·
                  refine ⟨188209448244082864272729541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250945930992110485696972721 188209448244082864272729541)
                  ·
                    refine ⟨35289271545765537051136789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188209448244082864272729541 35289271545765537051136789)
                    ·
                      refine ⟨1654184603707759549272037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35289271545765537051136789 1654184603707759549272037)
                      ·
                        rfl

theorem cell23_3221513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3221513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221513 prefixEnd_3221513 := by exact prefixLift 3221513
  have htrace : WordTrace (prefixWord ++ tailWord_3221513) baseStart_3221513 baseEnd_3221513 := by
    simpa [prefixWord, tailWord_3221513, baseEnd_3221513] using wordTrace_append hprefix tailTrace_3221513
  have hstable : (prefixWord ++ tailWord_3221513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221513).length < 2 ^ (prefixWord ++ tailWord_3221513).sum := by decide
  have hdescent : baseEnd_3221513 < baseStart_3221513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221574 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3221574 : Nat := 118140960795 + 3221574 * 2 ^ 59
def prefixEnd_3221574 : Nat := 4983230072969 + 3 ^ 40 * 3221574 * 2
def baseEnd_3221574 : Nat := 551405308675894603536419

theorem tailTrace_3221574 : CollatzResearch.WordTrace tailWord_3221574 prefixEnd_3221574 551405308675894603536419 := by
  unfold tailWord_3221574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671889275962346058767743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78333637887196715920378517 3671889275962346058767743)
  ·
    refine ⟨5507833913943519088151615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671889275962346058767743 5507833913943519088151615)
    ·
      refine ⟨8261750870915278632227423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507833913943519088151615 8261750870915278632227423)
      ·
        refine ⟨12392626306372917948341135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8261750870915278632227423 12392626306372917948341135)
        ·
          refine ⟨18588939459559376922511703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392626306372917948341135 18588939459559376922511703)
          ·
            refine ⟨27883409189339065383767555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18588939459559376922511703 27883409189339065383767555)
            ·
              refine ⟨41825113784008598075651333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27883409189339065383767555 41825113784008598075651333)
              ·
                refine ⟨7842208834501612139184625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41825113784008598075651333 7842208834501612139184625)
                ·
                  refine ⟨5881656625876209104388469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842208834501612139184625 5881656625876209104388469)
                  ·
                    refine ⟨551405308675894603536419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5881656625876209104388469 551405308675894603536419)
                    ·
                      rfl

theorem cell23_3221574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3221574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221574 prefixEnd_3221574 := by exact prefixLift 3221574
  have htrace : WordTrace (prefixWord ++ tailWord_3221574) baseStart_3221574 baseEnd_3221574 := by
    simpa [prefixWord, tailWord_3221574, baseEnd_3221574] using wordTrace_append hprefix tailTrace_3221574
  have hstable : (prefixWord ++ tailWord_3221574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221574).length < 2 ^ (prefixWord ++ tailWord_3221574).sum := by decide
  have hdescent : baseEnd_3221574 < baseStart_3221574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221577 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 4, 2]
def baseStart_3221577 : Nat := 118140960795 + 3221577 * 2 ^ 59
def prefixEnd_3221577 : Nat := 4983230072969 + 3 ^ 40 * 3221577 * 2
def baseEnd_3221577 : Nat := 1654217466469647298871743

theorem tailTrace_3221577 : CollatzResearch.WordTrace tailWord_3221577 prefixEnd_3221577 1654217466469647298871743 := by
  unfold tailWord_3221577
  simp only [CollatzResearch.WordTrace]
  refine ⟨117500566249784205392926985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78333710833189470261951323 117500566249784205392926985)
  ·
    refine ⟨88125424687338154044695239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117500566249784205392926985 88125424687338154044695239)
    ·
      refine ⟨132188137031007231067042859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88125424687338154044695239 132188137031007231067042859)
      ·
        refine ⟨198282205546510846600564289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132188137031007231067042859 198282205546510846600564289)
        ·
          refine ⟨148711654159883134950423217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198282205546510846600564289 148711654159883134950423217)
          ·
            refine ⟨111533740619912351212817413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148711654159883134950423217 111533740619912351212817413)
            ·
              refine ⟨20912576366233565852403265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111533740619912351212817413 20912576366233565852403265)
              ·
                refine ⟨15684432274675174389302449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20912576366233565852403265 15684432274675174389302449)
                ·
                  refine ⟨11763324206006380791976837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15684432274675174389302449 11763324206006380791976837)
                  ·
                    refine ⟨2205623288626196398495657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11763324206006380791976837 2205623288626196398495657)
                    ·
                      refine ⟨1654217466469647298871743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205623288626196398495657 1654217466469647298871743)
                      ·
                        rfl

theorem cell23_3221577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 4, 2].length) (baseStart_3221577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221577 prefixEnd_3221577 := by exact prefixLift 3221577
  have htrace : WordTrace (prefixWord ++ tailWord_3221577) baseStart_3221577 baseEnd_3221577 := by
    simpa [prefixWord, tailWord_3221577, baseEnd_3221577] using wordTrace_append hprefix tailTrace_3221577
  have hstable : (prefixWord ++ tailWord_3221577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221577).length < 2 ^ (prefixWord ++ tailWord_3221577).sum := by decide
  have hdescent : baseEnd_3221577 < baseStart_3221577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221664 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_3221664 : Nat := 118140960795 + 3221664 * 2 ^ 59
def prefixEnd_3221664 : Nat := 4983230072969 + 3 ^ 40 * 3221664 * 2
def baseEnd_3221664 : Nat := 551420713095529486161281

theorem tailTrace_3221664 : CollatzResearch.WordTrace tailWord_3221664 prefixEnd_3221664 551420713095529486161281 := by
  unfold tailWord_3221664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58751869700234509625672023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78335826266979346167562697 58751869700234509625672023)
  ·
    refine ⟨88127804550351764438508035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58751869700234509625672023 88127804550351764438508035)
    ·
      refine ⟨132191706825527646657762053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88127804550351764438508035 132191706825527646657762053)
      ·
        refine ⟨24785945029786433748330385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132191706825527646657762053 24785945029786433748330385)
        ·
          refine ⟨18589458772339825311247789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24785945029786433748330385 18589458772339825311247789)
          ·
            refine ⟨6971047039627434491717921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18589458772339825311247789 6971047039627434491717921)
            ·
              refine ⟨5228285279720575868788441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6971047039627434491717921 5228285279720575868788441)
              ·
                refine ⟨3921213959790431901591331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228285279720575868788441 3921213959790431901591331)
                ·
                  refine ⟨5881820939685647852386997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921213959790431901591331 5881820939685647852386997)
                  ·
                    refine ⟨551420713095529486161281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5881820939685647852386997 551420713095529486161281)
                    ·
                      rfl

theorem cell23_3221664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_3221664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221664 prefixEnd_3221664 := by exact prefixLift 3221664
  have htrace : WordTrace (prefixWord ++ tailWord_3221664) baseStart_3221664 baseEnd_3221664 := by
    simpa [prefixWord, tailWord_3221664, baseEnd_3221664] using wordTrace_append hprefix tailTrace_3221664
  have hstable : (prefixWord ++ tailWord_3221664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221664).length < 2 ^ (prefixWord ++ tailWord_3221664).sum := by decide
  have hdescent : baseEnd_3221664 < baseStart_3221664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_3221680 : Nat := 118140960795 + 3221680 * 2 ^ 59
def prefixEnd_3221680 : Nat := 4983230072969 + 3 ^ 40 * 3221680 * 2
def baseEnd_3221680 : Nat := 1654270354977060395883769

theorem tailTrace_3221680 : CollatzResearch.WordTrace tailWord_3221680 prefixEnd_3221680 1654270354977060395883769 := by
  unfold tailWord_3221680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752161484205526991963247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78336215312274035989284329 58752161484205526991963247)
  ·
    refine ⟨88128242226308290487944871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58752161484205526991963247 88128242226308290487944871)
    ·
      refine ⟨132192363339462435731917307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88128242226308290487944871 132192363339462435731917307)
      ·
        refine ⟨198288545009193653597875961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132192363339462435731917307 198288545009193653597875961)
        ·
          refine ⟨148716408756895240198406971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198288545009193653597875961 148716408756895240198406971)
          ·
            refine ⟨223074613135342860297610457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148716408756895240198406971 223074613135342860297610457)
            ·
              refine ⟨167305959851507145223207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223074613135342860297610457 167305959851507145223207843)
              ·
                refine ⟨250958939777260717834811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167305959851507145223207843 250958939777260717834811765)
                ·
                  refine ⟨23527400604118192297013603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250958939777260717834811765 23527400604118192297013603)
                  ·
                    refine ⟨35291100906177288445520405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23527400604118192297013603 35291100906177288445520405)
                    ·
                      refine ⟨1654270354977060395883769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35291100906177288445520405 1654270354977060395883769)
                      ·
                        rfl

theorem cell23_3221680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_3221680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221680 prefixEnd_3221680 := by exact prefixLift 3221680
  have htrace : WordTrace (prefixWord ++ tailWord_3221680) baseStart_3221680 baseEnd_3221680 := by
    simpa [prefixWord, tailWord_3221680, baseEnd_3221680] using wordTrace_append hprefix tailTrace_3221680
  have hstable : (prefixWord ++ tailWord_3221680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221680).length < 2 ^ (prefixWord ++ tailWord_3221680).sum := by decide
  have hdescent : baseEnd_3221680 < baseStart_3221680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221687 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3221687 : Nat := 118140960795 + 3221687 * 2 ^ 59
def prefixEnd_3221687 : Nat := 4983230072969 + 3 ^ 40 * 3221687 * 2
def baseEnd_3221687 : Nat := 1654273949341641868496237

theorem tailTrace_3221687 : CollatzResearch.WordTrace tailWord_3221687 prefixEnd_3221687 1654273949341641868496237 := by
  unfold tailWord_3221687
  simp only [CollatzResearch.WordTrace]
  refine ⟨117504578279385694179431315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78336385519590462786287543 117504578279385694179431315)
  ·
    refine ⟨176256867419078541269146973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117504578279385694179431315 176256867419078541269146973)
    ·
      refine ⟨66096325282154452975930115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176256867419078541269146973 66096325282154452975930115)
      ·
        refine ⟨99144487923231679463895173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66096325282154452975930115 99144487923231679463895173)
        ·
          refine ⟨18589591485605939899480345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99144487923231679463895173 18589591485605939899480345)
          ·
            refine ⟨13942193614204454924610259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18589591485605939899480345 13942193614204454924610259)
            ·
              refine ⟨20913290421306682386915389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13942193614204454924610259 20913290421306682386915389)
              ·
                refine ⟨7842483907990005895093271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20913290421306682386915389 7842483907990005895093271)
                ·
                  refine ⟨11763725861985008842639907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842483907990005895093271 11763725861985008842639907)
                  ·
                    refine ⟨17645588792977513263959861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11763725861985008842639907 17645588792977513263959861)
                    ·
                      refine ⟨1654273949341641868496237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17645588792977513263959861 1654273949341641868496237)
                      ·
                        rfl

theorem cell23_3221687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3221687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221687 prefixEnd_3221687 := by exact prefixLift 3221687
  have htrace : WordTrace (prefixWord ++ tailWord_3221687) baseStart_3221687 baseEnd_3221687 := by
    simpa [prefixWord, tailWord_3221687, baseEnd_3221687] using wordTrace_append hprefix tailTrace_3221687
  have hstable : (prefixWord ++ tailWord_3221687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221687).length < 2 ^ (prefixWord ++ tailWord_3221687).sum := by decide
  have hdescent : baseEnd_3221687 < baseStart_3221687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221690 : List Nat := [3, 1, 1, 1, 2, 2, 13]
def baseStart_3221690 : Nat := 118140960795 + 3221690 * 2 ^ 59
def prefixEnd_3221690 : Nat := 4983230072969 + 3 ^ 40 * 3221690 * 2
def baseEnd_3221690 : Nat := 20423154194859325392083

theorem tailTrace_3221690 : CollatzResearch.WordTrace tailWord_3221690 prefixEnd_3221690 20423154194859325392083 := by
  unfold tailWord_3221690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29376171924593706422947631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78336458465583217127860349 29376171924593706422947631)
  ·
    refine ⟨44064257886890559634421447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29376171924593706422947631 44064257886890559634421447)
    ·
      refine ⟨66096386830335839451632171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44064257886890559634421447 66096386830335839451632171)
      ·
        refine ⟨99144580245503759177448257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66096386830335839451632171 99144580245503759177448257)
        ·
          refine ⟨74358435184127819383086193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99144580245503759177448257 74358435184127819383086193)
          ·
            refine ⟨55768826388095864537314645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74358435184127819383086193 55768826388095864537314645)
            ·
              refine ⟨20423154194859325392083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 55768826388095864537314645 20423154194859325392083)
              ·
                rfl

theorem cell23_3221690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 13].length) (baseStart_3221690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221690 prefixEnd_3221690 := by exact prefixLift 3221690
  have htrace : WordTrace (prefixWord ++ tailWord_3221690) baseStart_3221690 baseEnd_3221690 := by
    simpa [prefixWord, tailWord_3221690, baseEnd_3221690] using wordTrace_append hprefix tailTrace_3221690
  have hstable : (prefixWord ++ tailWord_3221690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221690).length < 2 ^ (prefixWord ++ tailWord_3221690).sum := by decide
  have hdescent : baseEnd_3221690 < baseStart_3221690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221701 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_3221701 : Nat := 118140960795 + 3221701 * 2 ^ 59
def prefixEnd_3221701 : Nat := 4983230072969 + 3 ^ 40 * 3221701 * 2
def baseEnd_3221701 : Nat := 1654281138070804813721173

theorem tailTrace_3221701 : CollatzResearch.WordTrace tailWord_3221701 prefixEnd_3221701 1654281138070804813721173 := by
  unfold tailWord_3221701
  simp only [CollatzResearch.WordTrace]
  refine ⟨117505088901334974570440957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78336725934223316380293971 117505088901334974570440957)
  ·
    refine ⟨44064408338000615463915359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117505088901334974570440957 44064408338000615463915359)
    ·
      refine ⟨66096612507000923195873039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44064408338000615463915359 66096612507000923195873039)
      ·
        refine ⟨99144918760501384793809559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66096612507000923195873039 99144918760501384793809559)
        ·
          refine ⟨148717378140752077190714339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99144918760501384793809559 148717378140752077190714339)
          ·
            refine ⟨223076067211128115786071509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148717378140752077190714339 223076067211128115786071509)
            ·
              refine ⟨5228345325260815213736051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223076067211128115786071509 5228345325260815213736051)
              ·
                refine ⟨7842517987891222820604077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228345325260815213736051 7842517987891222820604077)
                ·
                  refine ⟨2940944245459208557726529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7842517987891222820604077 2940944245459208557726529)
                  ·
                    refine ⟨2205708184094406418294897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2940944245459208557726529 2205708184094406418294897)
                    ·
                      refine ⟨1654281138070804813721173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205708184094406418294897 1654281138070804813721173)
                      ·
                        rfl

theorem cell23_3221701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_3221701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221701 prefixEnd_3221701 := by exact prefixLift 3221701
  have htrace : WordTrace (prefixWord ++ tailWord_3221701) baseStart_3221701 baseEnd_3221701 := by
    simpa [prefixWord, tailWord_3221701, baseEnd_3221701] using wordTrace_append hprefix tailTrace_3221701
  have hstable : (prefixWord ++ tailWord_3221701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221701).length < 2 ^ (prefixWord ++ tailWord_3221701).sum := by decide
  have hdescent : baseEnd_3221701 < baseStart_3221701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221718 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3221718 : Nat := 118140960795 + 3221718 * 2 ^ 59
def prefixEnd_3221718 : Nat := 4983230072969 + 3 ^ 40 * 3221718 * 2
def baseEnd_3221718 : Nat := 1654289867241931247208595

theorem tailTrace_3221718 : CollatzResearch.WordTrace tailWord_3221718 prefixEnd_3221718 1654289867241931247208595 := by
  unfold tailWord_3221718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344106808892086654613113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78337139294848924315873205 7344106808892086654613113)
  ·
    refine ⟨5508080106669064990959835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7344106808892086654613113 5508080106669064990959835)
    ·
      refine ⟨8262120160003597486439753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508080106669064990959835 8262120160003597486439753)
      ·
        refine ⟨6196590120002698114829815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262120160003597486439753 6196590120002698114829815)
        ·
          refine ⟨9294885180004047172244723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196590120002698114829815 9294885180004047172244723)
          ·
            refine ⟨13942327770006070758367085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294885180004047172244723 13942327770006070758367085)
            ·
              refine ⟨5228372913752276534387657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13942327770006070758367085 5228372913752276534387657)
              ·
                refine ⟨3921279685314207400790743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228372913752276534387657 3921279685314207400790743)
                ·
                  refine ⟨5881919527971311101186115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921279685314207400790743 5881919527971311101186115)
                  ·
                    refine ⟨8822879291956966651779173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881919527971311101186115 8822879291956966651779173)
                    ·
                      refine ⟨1654289867241931247208595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8822879291956966651779173 1654289867241931247208595)
                      ·
                        rfl

theorem cell23_3221718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3221718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221718 prefixEnd_3221718 := by exact prefixLift 3221718
  have htrace : WordTrace (prefixWord ++ tailWord_3221718) baseStart_3221718 baseEnd_3221718 := by
    simpa [prefixWord, tailWord_3221718, baseEnd_3221718] using wordTrace_append hprefix tailTrace_3221718
  have hstable : (prefixWord ++ tailWord_3221718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221718).length < 2 ^ (prefixWord ++ tailWord_3221718).sum := by decide
  have hdescent : baseEnd_3221718 < baseStart_3221718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221731 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3221731 : Nat := 118140960795 + 3221731 * 2 ^ 59
def prefixEnd_3221731 : Nat := 4983230072969 + 3 ^ 40 * 3221731 * 2
def baseEnd_3221731 : Nat := 1654296542490439696346035

theorem tailTrace_3221731 : CollatzResearch.WordTrace tailWord_3221731 prefixEnd_3221731 1654296542490439696346035 := by
  unfold tailWord_3221731
  simp only [CollatzResearch.WordTrace]
  refine ⟨117506183091226289694033047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78337455394150859796022031 117506183091226289694033047)
  ·
    refine ⟨176259274636839434541049571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117506183091226289694033047 176259274636839434541049571)
    ·
      refine ⟨264388911955259151811574357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176259274636839434541049571 264388911955259151811574357)
      ·
        refine ⟨3098307561975693185291887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 264388911955259151811574357 3098307561975693185291887)
        ·
          refine ⟨4647461342963539777937831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098307561975693185291887 4647461342963539777937831)
          ·
            refine ⟨6971192014445309666906747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647461342963539777937831 6971192014445309666906747)
            ·
              refine ⟨10456788021667964500360121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971192014445309666906747 10456788021667964500360121)
              ·
                refine ⟨7842591016250973375270091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456788021667964500360121 7842591016250973375270091)
                ·
                  refine ⟨11763886524376460062905137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842591016250973375270091 11763886524376460062905137)
                  ·
                    refine ⟨8822914893282345047178853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11763886524376460062905137 8822914893282345047178853)
                    ·
                      refine ⟨1654296542490439696346035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8822914893282345047178853 1654296542490439696346035)
                      ·
                        rfl

theorem cell23_3221731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3221731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221731 prefixEnd_3221731 := by exact prefixLift 3221731
  have htrace : WordTrace (prefixWord ++ tailWord_3221731) baseStart_3221731 baseEnd_3221731 := by
    simpa [prefixWord, tailWord_3221731, baseEnd_3221731] using wordTrace_append hprefix tailTrace_3221731
  have hstable : (prefixWord ++ tailWord_3221731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221731).length < 2 ^ (prefixWord ++ tailWord_3221731).sum := by decide
  have hdescent : baseEnd_3221731 < baseStart_3221731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221791 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 4, 2]
def baseStart_3221791 : Nat := 118140960795 + 3221791 * 2 ^ 59
def prefixEnd_3221791 : Nat := 4983230072969 + 3 ^ 40 * 3221791 * 2
def baseEnd_3221791 : Nat := 1654327351329709461595759

theorem tailTrace_3221791 : CollatzResearch.WordTrace tailWord_3221791 prefixEnd_3221791 1654327351329709461595759 := by
  unfold tailWord_3221791
  simp only [CollatzResearch.WordTrace]
  refine ⟨117508371471008919941217227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78338914314005946627478151 117508371471008919941217227)
  ·
    refine ⟨176262557206513379911825841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117508371471008919941217227 176262557206513379911825841)
    ·
      refine ⟨132196917904885034933869381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176262557206513379911825841 132196917904885034933869381)
      ·
        refine ⟨24786922107165944050100509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132196917904885034933869381 24786922107165944050100509)
        ·
          refine ⟨9295095790187229018787691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24786922107165944050100509 9295095790187229018787691)
          ·
            refine ⟨13942643685280843528181537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295095790187229018787691 13942643685280843528181537)
            ·
              refine ⟨10456982763960632646136153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13942643685280843528181537 10456982763960632646136153)
              ·
                refine ⟨7842737072970474484602115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456982763960632646136153 7842737072970474484602115)
                ·
                  refine ⟨11764105609455711726903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842737072970474484602115 11764105609455711726903173)
                  ·
                    refine ⟨2205769801772945948794345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11764105609455711726903173 2205769801772945948794345)
                    ·
                      refine ⟨1654327351329709461595759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205769801772945948794345 1654327351329709461595759)
                      ·
                        rfl

theorem cell23_3221791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_3221791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221791 prefixEnd_3221791 := by exact prefixLift 3221791
  have htrace : WordTrace (prefixWord ++ tailWord_3221791) baseStart_3221791 baseEnd_3221791 := by
    simpa [prefixWord, tailWord_3221791, baseEnd_3221791] using wordTrace_append hprefix tailTrace_3221791
  have hstable : (prefixWord ++ tailWord_3221791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221791).length < 2 ^ (prefixWord ++ tailWord_3221791).sum := by decide
  have hdescent : baseEnd_3221791 < baseStart_3221791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221802 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3221802 : Nat := 118140960795 + 3221802 * 2 ^ 59
def prefixEnd_3221802 : Nat := 4983230072969 + 3 ^ 40 * 3221802 * 2
def baseEnd_3221802 : Nat := 1654332999616908918558209

theorem tailTrace_3221802 : CollatzResearch.WordTrace tailWord_3221802 prefixEnd_3221802 1654332999616908918558209 := by
  unfold tailWord_3221802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377193168492267204966915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78339181782646045879911773 29377193168492267204966915)
  ·
    refine ⟨44065789752738400807450373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29377193168492267204966915 44065789752738400807450373)
    ·
      refine ⟨8262335578638450151396945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44065789752738400807450373 8262335578638450151396945)
      ·
        refine ⟨6196751683978837613547709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262335578638450151396945 6196751683978837613547709)
        ·
          refine ⟨2323781881492064105080391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6196751683978837613547709 2323781881492064105080391)
          ·
            refine ⟨3485672822238096157620587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323781881492064105080391 3485672822238096157620587)
            ·
              refine ⟨5228509233357144236430881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485672822238096157620587 5228509233357144236430881)
              ·
                refine ⟨3921381925017858177323161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228509233357144236430881 3921381925017858177323161)
                ·
                  refine ⟨2941036443763393632992371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921381925017858177323161 2941036443763393632992371)
                  ·
                    refine ⟨4411554665645090449488557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941036443763393632992371 4411554665645090449488557)
                    ·
                      refine ⟨1654332999616908918558209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4411554665645090449488557 1654332999616908918558209)
                      ·
                        rfl

theorem cell23_3221802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3221802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221802 prefixEnd_3221802 := by exact prefixLift 3221802
  have htrace : WordTrace (prefixWord ++ tailWord_3221802) baseStart_3221802 baseEnd_3221802 := by
    simpa [prefixWord, tailWord_3221802, baseEnd_3221802] using wordTrace_append hprefix tailTrace_3221802
  have hstable : (prefixWord ++ tailWord_3221802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221802).length < 2 ^ (prefixWord ++ tailWord_3221802).sum := by decide
  have hdescent : baseEnd_3221802 < baseStart_3221802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221825 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3221825 : Nat := 118140960795 + 3221825 * 2 ^ 59
def prefixEnd_3221825 : Nat := 4983230072969 + 3 ^ 40 * 3221825 * 2
def baseEnd_3221825 : Nat := 1654344809671962328570603

theorem tailTrace_3221825 : CollatzResearch.WordTrace tailWord_3221825 prefixEnd_3221825 1654344809671962328570603 := by
  unfold tailWord_3221825
  simp only [CollatzResearch.WordTrace]
  refine ⟨117509611552885743747954929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78339741035257162498636619 117509611552885743747954929)
  ·
    refine ⟨88132208664664307810966197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117509611552885743747954929 88132208664664307810966197)
    ·
      refine ⟨8262394562312278857278081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88132208664664307810966197 8262394562312278857278081)
      ·
        refine ⟨6196795921734209142958561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262394562312278857278081 6196795921734209142958561)
        ·
          refine ⟨4647596941300656857218921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196795921734209142958561 4647596941300656857218921)
          ·
            refine ⟨3485697705975492642914191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647596941300656857218921 3485697705975492642914191)
            ·
              refine ⟨5228546558963238964371287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485697705975492642914191 5228546558963238964371287)
              ·
                refine ⟨7842819838444858446556931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228546558963238964371287 7842819838444858446556931)
                ·
                  refine ⟨11764229757667287669835397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842819838444858446556931 11764229757667287669835397)
                  ·
                    refine ⟨2205793079562616438094137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11764229757667287669835397 2205793079562616438094137)
                    ·
                      refine ⟨1654344809671962328570603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205793079562616438094137 1654344809671962328570603)
                      ·
                        rfl

theorem cell23_3221825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3221825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221825 prefixEnd_3221825 := by exact prefixLift 3221825
  have htrace : WordTrace (prefixWord ++ tailWord_3221825) baseStart_3221825 baseEnd_3221825 := by
    simpa [prefixWord, tailWord_3221825, baseEnd_3221825] using wordTrace_append hprefix tailTrace_3221825
  have hstable : (prefixWord ++ tailWord_3221825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221825).length < 2 ^ (prefixWord ++ tailWord_3221825).sum := by decide
  have hdescent : baseEnd_3221825 < baseStart_3221825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221827 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 7]
def baseStart_3221827 : Nat := 118140960795 + 3221827 * 2 ^ 59
def prefixEnd_3221827 : Nat := 4983230072969 + 3 ^ 40 * 3221827 * 2
def baseEnd_3221827 : Nat := 551448612211090440248531

theorem tailTrace_3221827 : CollatzResearch.WordTrace tailWord_3221827 prefixEnd_3221827 551448612211090440248531 := by
  unfold tailWord_3221827
  simp only [CollatzResearch.WordTrace]
  refine ⟨117509684498878498089527735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78339789665918998726351823 117509684498878498089527735)
  ·
    refine ⟨176264526748317747134291603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117509684498878498089527735 176264526748317747134291603)
    ·
      refine ⟨264396790122476620701437405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176264526748317747134291603 264396790122476620701437405)
      ·
        refine ⟨99148796295928732763039027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264396790122476620701437405 99148796295928732763039027)
        ·
          refine ⟨148723194443893099144558541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99148796295928732763039027 148723194443893099144558541)
          ·
            refine ⟨55771197916459912179209453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148723194443893099144558541 55771197916459912179209453)
            ·
              refine ⟨20914199218672467067203545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55771197916459912179209453 20914199218672467067203545)
              ·
                refine ⟨15685649414004350300402659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20914199218672467067203545 15685649414004350300402659)
                ·
                  refine ⟨23528474121006525450603989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15685649414004350300402659 23528474121006525450603989)
                  ·
                    refine ⟨551448612211090440248531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23528474121006525450603989 551448612211090440248531)
                    ·
                      rfl

theorem cell23_3221827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_3221827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221827 prefixEnd_3221827 := by exact prefixLift 3221827
  have htrace : WordTrace (prefixWord ++ tailWord_3221827) baseStart_3221827 baseEnd_3221827 := by
    simpa [prefixWord, tailWord_3221827, baseEnd_3221827] using wordTrace_append hprefix tailTrace_3221827
  have hstable : (prefixWord ++ tailWord_3221827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221827).length < 2 ^ (prefixWord ++ tailWord_3221827).sum := by decide
  have hdescent : baseEnd_3221827 < baseStart_3221827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221844 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3221844 : Nat := 118140960795 + 3221844 * 2 ^ 59
def prefixEnd_3221844 : Nat := 4983230072969 + 3 ^ 40 * 3221844 * 2
def baseEnd_3221844 : Nat := 551451521934799251411005

theorem tailTrace_3221844 : CollatzResearch.WordTrace tailWord_3221844 prefixEnd_3221844 551451521934799251411005 := by
  unfold tailWord_3221844
  simp only [CollatzResearch.WordTrace]
  refine ⟨58755152269908454996448293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78340203026544606661931057 58755152269908454996448293)
  ·
    refine ⟨11016591050607835311834055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58755152269908454996448293 11016591050607835311834055)
    ·
      refine ⟨16524886575911752967751083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11016591050607835311834055 16524886575911752967751083)
      ·
        refine ⟨24787329863867629451626625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16524886575911752967751083 24787329863867629451626625)
        ·
          refine ⟨18590497397900722088719969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24787329863867629451626625 18590497397900722088719969)
          ·
            refine ⟨13942873048425541566539977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18590497397900722088719969 13942873048425541566539977)
            ·
              refine ⟨10457154786319156174904983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13942873048425541566539977 10457154786319156174904983)
              ·
                refine ⟨15685732179478734262357475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457154786319156174904983 15685732179478734262357475)
                ·
                  refine ⟨23528598269218101393536213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15685732179478734262357475 23528598269218101393536213)
                  ·
                    refine ⟨551451521934799251411005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23528598269218101393536213 551451521934799251411005)
                    ·
                      rfl

theorem cell23_3221844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3221844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221844 prefixEnd_3221844 := by exact prefixLift 3221844
  have htrace : WordTrace (prefixWord ++ tailWord_3221844) baseStart_3221844 baseEnd_3221844 := by
    simpa [prefixWord, tailWord_3221844, baseEnd_3221844] using wordTrace_append hprefix tailTrace_3221844
  have hstable : (prefixWord ++ tailWord_3221844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221844).length < 2 ^ (prefixWord ++ tailWord_3221844).sum := by decide
  have hdescent : baseEnd_3221844 < baseStart_3221844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221867 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_3221867 : Nat := 118140960795 + 3221867 * 2 ^ 59
def prefixEnd_3221867 : Nat := 4983230072969 + 3 ^ 40 * 3221867 * 2
def baseEnd_3221867 : Nat := 1654366375859451164245409

theorem tailTrace_3221867 : CollatzResearch.WordTrace tailWord_3221867 prefixEnd_3221867 1654366375859451164245409 := by
  unfold tailWord_3221867
  simp only [CollatzResearch.WordTrace]
  refine ⟨117511143418733584920983855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78340762279155723280655903 117511143418733584920983855)
  ·
    refine ⟨176266715128100377381475783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117511143418733584920983855 176266715128100377381475783)
    ·
      refine ⟨264400072692150566072213675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176266715128100377381475783 264400072692150566072213675)
      ·
        refine ⟨396600109038225849108320513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264400072692150566072213675 396600109038225849108320513)
        ·
          refine ⟨297450081778669386831240385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396600109038225849108320513 297450081778669386831240385)
          ·
            refine ⟨223087561334002040123430289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297450081778669386831240385 223087561334002040123430289)
            ·
              refine ⟨167315671000501530092572717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223087561334002040123430289 167315671000501530092572717)
              ·
                refine ⟨62743376625188073784714769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167315671000501530092572717 62743376625188073784714769)
                ·
                  refine ⟨47057532468891055338536077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62743376625188073784714769 47057532468891055338536077)
                  ·
                    refine ⟨17646574675834145751951029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47057532468891055338536077 17646574675834145751951029)
                    ·
                      refine ⟨1654366375859451164245409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17646574675834145751951029 1654366375859451164245409)
                      ·
                        rfl

theorem cell23_3221867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_3221867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221867 prefixEnd_3221867 := by exact prefixLift 3221867
  have htrace : WordTrace (prefixWord ++ tailWord_3221867) baseStart_3221867 baseEnd_3221867 := by
    simpa [prefixWord, tailWord_3221867, baseEnd_3221867] using wordTrace_append hprefix tailTrace_3221867
  have hstable : (prefixWord ++ tailWord_3221867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221867).length < 2 ^ (prefixWord ++ tailWord_3221867).sum := by decide
  have hdescent : baseEnd_3221867 < baseStart_3221867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221884 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3221884 : Nat := 118140960795 + 3221884 * 2 ^ 59
def prefixEnd_3221884 : Nat := 4983230072969 + 3 ^ 40 * 3221884 * 2
def baseEnd_3221884 : Nat := 1654375105030577597732831

theorem tailTrace_3221884 : CollatzResearch.WordTrace tailWord_3221884 prefixEnd_3221884 1654375105030577597732831 := by
  unfold tailWord_3221884
  simp only [CollatzResearch.WordTrace]
  refine ⟨58755881729835998412176353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78341175639781331216235137 58755881729835998412176353)
  ·
    refine ⟨44066911297376998809132265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58755881729835998412176353 44066911297376998809132265)
    ·
      refine ⟨33050183473032749106849199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44066911297376998809132265 33050183473032749106849199)
      ·
        refine ⟨49575275209549123660273799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33050183473032749106849199 49575275209549123660273799)
        ·
          refine ⟨74362912814323685490410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49575275209549123660273799 74362912814323685490410699)
          ·
            refine ⟨111544369221485528235616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74362912814323685490410699 111544369221485528235616049)
            ·
              refine ⟨83658276916114146176712037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111544369221485528235616049 83658276916114146176712037)
              ·
                refine ⟨15685926921771402408133507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83658276916114146176712037 15685926921771402408133507)
                ·
                  refine ⟨23528890382657103612200261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15685926921771402408133507 23528890382657103612200261)
                  ·
                    refine ⟨4411666946748206927287549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23528890382657103612200261 4411666946748206927287549)
                    ·
                      refine ⟨1654375105030577597732831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4411666946748206927287549 1654375105030577597732831)
                      ·
                        rfl

theorem cell23_3221884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3221884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221884 prefixEnd_3221884 := by exact prefixLift 3221884
  have htrace : WordTrace (prefixWord ++ tailWord_3221884) baseStart_3221884 baseEnd_3221884 := by
    simpa [prefixWord, tailWord_3221884, baseEnd_3221884] using wordTrace_append hprefix tailTrace_3221884
  have hstable : (prefixWord ++ tailWord_3221884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221884).length < 2 ^ (prefixWord ++ tailWord_3221884).sum := by decide
  have hdescent : baseEnd_3221884 < baseStart_3221884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221948 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3221948 : Nat := 118140960795 + 3221948 * 2 ^ 59
def prefixEnd_3221948 : Nat := 4983230072969 + 3 ^ 40 * 3221948 * 2
def baseEnd_3221948 : Nat := 1654407967792465347332537

theorem tailTrace_3221948 : CollatzResearch.WordTrace tailWord_3221948 prefixEnd_3221948 1654407967792465347332537 := by
  unfold tailWord_3221948
  simp only [CollatzResearch.WordTrace]
  refine ⟨58757048865720067877341249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78342731820960090503121665 58757048865720067877341249)
  ·
    refine ⟨44067786649290050908005937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58757048865720067877341249 44067786649290050908005937)
    ·
      refine ⟨33050839986967538181004453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44067786649290050908005937 33050839986967538181004453)
      ·
        refine ⟨6197032497556413408938335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33050839986967538181004453 6197032497556413408938335)
        ·
          refine ⟨9295548746334620113407503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197032497556413408938335 9295548746334620113407503)
          ·
            refine ⟨13943323119501930170111255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295548746334620113407503 13943323119501930170111255)
            ·
              refine ⟨20914984679252895255166883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13943323119501930170111255 20914984679252895255166883)
              ·
                refine ⟨31372477018879342882750325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20914984679252895255166883 31372477018879342882750325)
                ·
                  refine ⟨2941169720519938395257843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31372477018879342882750325 2941169720519938395257843)
                  ·
                    refine ⟨4411754580779907592886765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941169720519938395257843 4411754580779907592886765)
                    ·
                      refine ⟨1654407967792465347332537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4411754580779907592886765 1654407967792465347332537)
                      ·
                        rfl

theorem cell23_3221948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3221948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221948 prefixEnd_3221948 := by exact prefixLift 3221948
  have htrace : WordTrace (prefixWord ++ tailWord_3221948) baseStart_3221948 baseEnd_3221948 := by
    simpa [prefixWord, tailWord_3221948, baseEnd_3221948] using wordTrace_append hprefix tailTrace_3221948
  have hstable : (prefixWord ++ tailWord_3221948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221948).length < 2 ^ (prefixWord ++ tailWord_3221948).sum := by decide
  have hdescent : baseEnd_3221948 < baseStart_3221948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221984 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3221984 : Nat := 118140960795 + 3221984 * 2 ^ 59
def prefixEnd_3221984 : Nat := 4983230072969 + 3 ^ 40 * 3221984 * 2
def baseEnd_3221984 : Nat := 1654426453096027206482371

theorem tailTrace_3221984 : CollatzResearch.WordTrace tailWord_3221984 prefixEnd_3221984 1654426453096027206482371 := by
  unfold tailWord_3221984
  simp only [CollatzResearch.WordTrace]
  refine ⟨58757705379654856951496503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78343607172873142601995337 58757705379654856951496503)
  ·
    refine ⟨88136558069482285427244755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58757705379654856951496503 88136558069482285427244755)
    ·
      refine ⟨132204837104223428140867133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88136558069482285427244755 132204837104223428140867133)
      ·
        refine ⟨49576813914083785552825175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132204837104223428140867133 49576813914083785552825175)
        ·
          refine ⟨74365220871125678329237763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49576813914083785552825175 74365220871125678329237763)
          ·
            refine ⟨111547831306688517493856645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74365220871125678329237763 111547831306688517493856645)
            ·
              refine ⟨20915218370004097030098121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111547831306688517493856645 20915218370004097030098121)
              ·
                refine ⟨15686413777503072772573591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20915218370004097030098121 15686413777503072772573591)
                ·
                  refine ⟨23529620666254609158860387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15686413777503072772573591 23529620666254609158860387)
                  ·
                    refine ⟨35294430999381913738290581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23529620666254609158860387 35294430999381913738290581)
                    ·
                      refine ⟨1654426453096027206482371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35294430999381913738290581 1654426453096027206482371)
                      ·
                        rfl

theorem cell23_3221984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3221984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221984 prefixEnd_3221984 := by exact prefixLift 3221984
  have htrace : WordTrace (prefixWord ++ tailWord_3221984) baseStart_3221984 baseEnd_3221984 := by
    simpa [prefixWord, tailWord_3221984, baseEnd_3221984] using wordTrace_append hprefix tailTrace_3221984
  have hstable : (prefixWord ++ tailWord_3221984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221984).length < 2 ^ (prefixWord ++ tailWord_3221984).sum := by decide
  have hdescent : baseEnd_3221984 < baseStart_3221984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221991 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3221991 : Nat := 118140960795 + 3221991 * 2 ^ 59
def prefixEnd_3221991 : Nat := 4983230072969 + 3 ^ 40 * 3221991 * 2
def baseEnd_3221991 : Nat := 1654430047460608679094839

theorem tailTrace_3221991 : CollatzResearch.WordTrace tailWord_3221991 prefixEnd_3221991 1654430047460608679094839 := by
  unfold tailWord_3221991
  simp only [CollatzResearch.WordTrace]
  refine ⟨117515666070284354098497827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78343777380189569398998551 117515666070284354098497827)
  ·
    refine ⟨176273499105426531147746741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117515666070284354098497827 176273499105426531147746741)
    ·
      refine ⟨16525640541133737295101257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176273499105426531147746741 16525640541133737295101257)
      ·
        refine ⟨12394230405850302971325943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16525640541133737295101257 12394230405850302971325943)
        ·
          refine ⟨18591345608775454456988915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12394230405850302971325943 18591345608775454456988915)
          ·
            refine ⟨27887018413163181685483373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18591345608775454456988915 27887018413163181685483373)
            ·
              refine ⟨10457631904936193132056265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27887018413163181685483373 10457631904936193132056265)
              ·
                refine ⟨7843223928702144849042199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10457631904936193132056265 7843223928702144849042199)
                ·
                  refine ⟨11764835893053217273563299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7843223928702144849042199 11764835893053217273563299)
                  ·
                    refine ⟨17647253839579825910344949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11764835893053217273563299 17647253839579825910344949)
                    ·
                      refine ⟨1654430047460608679094839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17647253839579825910344949 1654430047460608679094839)
                      ·
                        rfl

theorem cell23_3221991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3221991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221991 prefixEnd_3221991 := by exact prefixLift 3221991
  have htrace : WordTrace (prefixWord ++ tailWord_3221991) baseStart_3221991 baseEnd_3221991 := by
    simpa [prefixWord, tailWord_3221991, baseEnd_3221991] using wordTrace_append hprefix tailTrace_3221991
  have hstable : (prefixWord ++ tailWord_3221991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221991).length < 2 ^ (prefixWord ++ tailWord_3221991).sum := by decide
  have hdescent : baseEnd_3221991 < baseStart_3221991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221998 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3221998 : Nat := 118140960795 + 3221998 * 2 ^ 59
def prefixEnd_3221998 : Nat := 4983230072969 + 3 ^ 40 * 3221998 * 2
def baseEnd_3221998 : Nat := 551477880608396717235769

theorem tailTrace_3221998 : CollatzResearch.WordTrace tailWord_3221998 prefixEnd_3221998 551477880608396717235769 := by
  unfold tailWord_3221998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689490172657374286750331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78343947587505996196001765 14689490172657374286750331)
  ·
    refine ⟨22034235258986061430125497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14689490172657374286750331 22034235258986061430125497)
    ·
      refine ⟨16525676444239546072594123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22034235258986061430125497 16525676444239546072594123)
      ·
        refine ⟨24788514666359319108891185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16525676444239546072594123 24788514666359319108891185)
        ·
          refine ⟨18591385999769489331668389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24788514666359319108891185 18591385999769489331668389)
          ·
            refine ⟨3485884874956779249687823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18591385999769489331668389 3485884874956779249687823)
            ·
              refine ⟨5228827312435168874531735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485884874956779249687823 5228827312435168874531735)
              ·
                refine ⟨7843240968652753311797603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228827312435168874531735 7843240968652753311797603)
                ·
                  refine ⟨11764861452979129967696405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7843240968652753311797603 11764861452979129967696405)
                  ·
                    refine ⟨551477880608396717235769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11764861452979129967696405 551477880608396717235769)
                    ·
                      rfl

theorem cell23_3221998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3221998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3221998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3221998 prefixEnd_3221998 := by exact prefixLift 3221998
  have htrace : WordTrace (prefixWord ++ tailWord_3221998) baseStart_3221998 baseEnd_3221998 := by
    simpa [prefixWord, tailWord_3221998, baseEnd_3221998] using wordTrace_append hprefix tailTrace_3221998
  have hstable : (prefixWord ++ tailWord_3221998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221998).length < 2 ^ (prefixWord ++ tailWord_3221998).sum := by decide
  have hdescent : baseEnd_3221998 < baseStart_3221998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222008 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3222008 : Nat := 118140960795 + 3222008 * 2 ^ 59
def prefixEnd_3222008 : Nat := 4983230072969 + 3 ^ 40 * 3222008 * 2
def baseEnd_3222008 : Nat := 1654438776631735112582261

theorem tailTrace_3222008 : CollatzResearch.WordTrace tailWord_3222008 prefixEnd_3222008 1654438776631735112582261 := by
  unfold tailWord_3222008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58758143055611383000933339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78344190740815177334577785 58758143055611383000933339)
  ·
    refine ⟨88137214583417074501400009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58758143055611383000933339 88137214583417074501400009)
    ·
      refine ⟨66102910937562805876050007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88137214583417074501400009 66102910937562805876050007)
      ·
        refine ⟨99154366406344208814075011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66102910937562805876050007 99154366406344208814075011)
        ·
          refine ⟨148731549609516313221112517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99154366406344208814075011 148731549609516313221112517)
          ·
            refine ⟨27887165551784308728958597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148731549609516313221112517 27887165551784308728958597)
            ·
              refine ⟨5228843540959557886679737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27887165551784308728958597 5228843540959557886679737)
              ·
                refine ⟨3921632655719668415009803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228843540959557886679737 3921632655719668415009803)
                ·
                  refine ⟨5882448983579502622514705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921632655719668415009803 5882448983579502622514705)
                  ·
                    refine ⟨4411836737684626966886029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5882448983579502622514705 4411836737684626966886029)
                    ·
                      refine ⟨1654438776631735112582261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4411836737684626966886029 1654438776631735112582261)
                      ·
                        rfl

theorem cell23_3222008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3222008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222008 prefixEnd_3222008 := by exact prefixLift 3222008
  have htrace : WordTrace (prefixWord ++ tailWord_3222008) baseStart_3222008 baseEnd_3222008 := by
    simpa [prefixWord, tailWord_3222008, baseEnd_3222008] using wordTrace_append hprefix tailTrace_3222008
  have hstable : (prefixWord ++ tailWord_3222008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222008).length < 2 ^ (prefixWord ++ tailWord_3222008).sum := by decide
  have hdescent : baseEnd_3222008 < baseStart_3222008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222021 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_3222021 : Nat := 118140960795 + 3222021 * 2 ^ 59
def prefixEnd_3222021 : Nat := 4983230072969 + 3 ^ 40 * 3222021 * 2
def baseEnd_3222021 : Nat := 1654445451880243561719701

theorem tailTrace_3222021 : CollatzResearch.WordTrace tailWord_3222021 prefixEnd_3222021 1654445451880243561719701 := by
  unfold tailWord_3222021
  simp only [CollatzResearch.WordTrace]
  refine ⟨117516760260175669222089917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78344506840117112814726611 117516760260175669222089917)
  ·
    refine ⟨44068785097565875958283719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117516760260175669222089917 44068785097565875958283719)
    ·
      refine ⟨66103177646348813937425579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44068785097565875958283719 66103177646348813937425579)
      ·
        refine ⟨99154766469523220906138369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66103177646348813937425579 99154766469523220906138369)
        ·
          refine ⟨74366074852142415679603777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99154766469523220906138369 74366074852142415679603777)
          ·
            refine ⟨55774556139106811759702833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74366074852142415679603777 55774556139106811759702833)
            ·
              refine ⟨41830917104330108819777125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55774556139106811759702833 41830917104330108819777125)
              ·
                refine ⟨7843296957061895403708211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41830917104330108819777125 7843296957061895403708211)
                ·
                  refine ⟨11764945435592843105562317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7843296957061895403708211 11764945435592843105562317)
                  ·
                    refine ⟨4411854538347316164585869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11764945435592843105562317 4411854538347316164585869)
                    ·
                      refine ⟨1654445451880243561719701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4411854538347316164585869 1654445451880243561719701)
                      ·
                        rfl

theorem cell23_3222021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_3222021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222021 prefixEnd_3222021 := by exact prefixLift 3222021
  have htrace : WordTrace (prefixWord ++ tailWord_3222021) baseStart_3222021 baseEnd_3222021 := by
    simpa [prefixWord, tailWord_3222021, baseEnd_3222021] using wordTrace_append hprefix tailTrace_3222021
  have hstable : (prefixWord ++ tailWord_3222021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222021).length < 2 ^ (prefixWord ++ tailWord_3222021).sum := by decide
  have hdescent : baseEnd_3222021 < baseStart_3222021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222024 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3222024 : Nat := 118140960795 + 3222024 * 2 ^ 59
def prefixEnd_3222024 : Nat := 4983230072969 + 3 ^ 40 * 3222024 * 2
def baseEnd_3222024 : Nat := 551482330774069016660729

theorem tailTrace_3222024 : CollatzResearch.WordTrace tailWord_3222024 prefixEnd_3222024 551482330774069016660729 := by
  unfold tailWord_3222024
  simp only [CollatzResearch.WordTrace]
  refine ⟨58758434839582400367224563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78344579786109867156299417 58758434839582400367224563)
  ·
    refine ⟨88137652259373600550836845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58758434839582400367224563 88137652259373600550836845)
    ·
      refine ⟨33051619597265100206563817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88137652259373600550836845 33051619597265100206563817)
      ·
        refine ⟨24788714697948825154922863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33051619597265100206563817 24788714697948825154922863)
        ·
          refine ⟨37183072046923237732384295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788714697948825154922863 37183072046923237732384295)
          ·
            refine ⟨55774608070384856598576443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37183072046923237732384295 55774608070384856598576443)
            ·
              refine ⟨83661912105577284897864665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55774608070384856598576443 83661912105577284897864665)
              ·
                refine ⟨62746434079182963673398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83661912105577284897864665 62746434079182963673398499)
                ·
                  refine ⟨94119651118774445510097749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62746434079182963673398499 94119651118774445510097749)
                  ·
                    refine ⟨551482330774069016660729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94119651118774445510097749 551482330774069016660729)
                    ·
                      rfl

theorem cell23_3222024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3222024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222024 prefixEnd_3222024 := by exact prefixLift 3222024
  have htrace : WordTrace (prefixWord ++ tailWord_3222024) baseStart_3222024 baseEnd_3222024 := by
    simpa [prefixWord, tailWord_3222024, baseEnd_3222024] using wordTrace_append hprefix tailTrace_3222024
  have hstable : (prefixWord ++ tailWord_3222024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222024).length < 2 ^ (prefixWord ++ tailWord_3222024).sum := by decide
  have hdescent : baseEnd_3222024 < baseStart_3222024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222039 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3222039 : Nat := 118140960795 + 3222039 * 2 ^ 59
def prefixEnd_3222039 : Nat := 4983230072969 + 3 ^ 40 * 3222039 * 2
def baseEnd_3222039 : Nat := 1654454694532024491294619

theorem tailTrace_3222039 : CollatzResearch.WordTrace tailWord_3222039 prefixEnd_3222039 1654454694532024491294619 := by
  unfold tailWord_3222039
  simp only [CollatzResearch.WordTrace]
  refine ⟨117517416774110458296245171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78344944516073638864163447 117517416774110458296245171)
  ·
    refine ⟨176276125161165687444367757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117517416774110458296245171 176276125161165687444367757)
    ·
      refine ⟨66103546935437132791637909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176276125161165687444367757 66103546935437132791637909)
      ·
        refine ⟨3098603762598615599608027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66103546935437132791637909 3098603762598615599608027)
        ·
          refine ⟨4647905643897923399412041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098603762598615599608027 4647905643897923399412041)
          ·
            refine ⟨3485929232923442549559031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647905643897923399412041 3485929232923442549559031)
            ·
              refine ⟨5228893849385163824338547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485929232923442549559031 5228893849385163824338547)
              ·
                refine ⟨7843340774077745736507821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228893849385163824338547 7843340774077745736507821)
                ·
                  refine ⟨2941252790279154651190433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7843340774077745736507821 2941252790279154651190433)
                  ·
                    refine ⟨2205939592709365988392825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941252790279154651190433 2205939592709365988392825)
                    ·
                      refine ⟨1654454694532024491294619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205939592709365988392825 1654454694532024491294619)
                      ·
                        rfl

theorem cell23_3222039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3222039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222039 prefixEnd_3222039 := by exact prefixLift 3222039
  have htrace : WordTrace (prefixWord ++ tailWord_3222039) baseStart_3222039 baseEnd_3222039 := by
    simpa [prefixWord, tailWord_3222039, baseEnd_3222039] using wordTrace_append hprefix tailTrace_3222039
  have hstable : (prefixWord ++ tailWord_3222039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222039).length < 2 ^ (prefixWord ++ tailWord_3222039).sum := by decide
  have hdescent : baseEnd_3222039 < baseStart_3222039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222065 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_3222065 : Nat := 118140960795 + 3222065 * 2 ^ 59
def prefixEnd_3222065 : Nat := 4983230072969 + 3 ^ 40 * 3222065 * 2
def baseEnd_3222065 : Nat := 1654468045029041389569499

theorem tailTrace_3222065 : CollatzResearch.WordTrace tailWord_3222065 prefixEnd_3222065 1654468045029041389569499 := by
  unfold tailWord_3222065
  simp only [CollatzResearch.WordTrace]
  refine ⟨117518365072016264736691649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78345576714677509824461099 117518365072016264736691649)
  ·
    refine ⟨88138773804012198552518737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117518365072016264736691649 88138773804012198552518737)
    ·
      refine ⟨66104080353009148914389053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88138773804012198552518737 66104080353009148914389053)
      ·
        refine ⟨24789030132378430842895895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66104080353009148914389053 24789030132378430842895895)
        ·
          refine ⟨37183545198567646264343843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24789030132378430842895895 37183545198567646264343843)
          ·
            refine ⟨55775317797851469396515765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37183545198567646264343843 55775317797851469396515765)
            ·
              refine ⟨5228936043548575255923353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55775317797851469396515765 5228936043548575255923353)
              ·
                refine ⟨3921702032661431441942515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228936043548575255923353 3921702032661431441942515)
                ·
                  refine ⟨5882553048992147162913773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921702032661431441942515 5882553048992147162913773)
                  ·
                    refine ⟨2205957393372055186092665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5882553048992147162913773 2205957393372055186092665)
                    ·
                      refine ⟨1654468045029041389569499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205957393372055186092665 1654468045029041389569499)
                      ·
                        rfl

theorem cell23_3222065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_3222065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222065 prefixEnd_3222065 := by exact prefixLift 3222065
  have htrace : WordTrace (prefixWord ++ tailWord_3222065) baseStart_3222065 baseEnd_3222065 := by
    simpa [prefixWord, tailWord_3222065, baseEnd_3222065] using wordTrace_append hprefix tailTrace_3222065
  have hstable : (prefixWord ++ tailWord_3222065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222065).length < 2 ^ (prefixWord ++ tailWord_3222065).sum := by decide
  have hdescent : baseEnd_3222065 < baseStart_3222065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222095 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 2, 2, 2]
def baseStart_3222095 : Nat := 118140960795 + 3222095 * 2 ^ 59
def prefixEnd_3222095 : Nat := 4983230072969 + 3 ^ 40 * 3222095 * 2
def baseEnd_3222095 : Nat := 1654483449448676272194361

theorem tailTrace_3222095 : CollatzResearch.WordTrace tailWord_3222095 prefixEnd_3222095 1654483449448676272194361 := by
  unfold tailWord_3222095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117519459261907579860283739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78346306174605053240189159 117519459261907579860283739)
  ·
    refine ⟨176279188892861369790425609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117519459261907579860283739 176279188892861369790425609)
    ·
      refine ⟨132209391669646027342819207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176279188892861369790425609 132209391669646027342819207)
      ·
        refine ⟨198314087504469041014228811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132209391669646027342819207 198314087504469041014228811)
        ·
          refine ⟨297471131256703561521343217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198314087504469041014228811 297471131256703561521343217)
          ·
            refine ⟨223103348442527671141007413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297471131256703561521343217 223103348442527671141007413)
            ·
              refine ⟨20915938916486969169469445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223103348442527671141007413 20915938916486969169469445)
              ·
                refine ⟨3921738546841306719275521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20915938916486969169469445 3921738546841306719275521)
                ·
                  refine ⟨2941303910130980039456641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921738546841306719275521 2941303910130980039456641)
                  ·
                    refine ⟨2205977932598235029592481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941303910130980039456641 2205977932598235029592481)
                    ·
                      refine ⟨1654483449448676272194361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2205977932598235029592481 1654483449448676272194361)
                      ·
                        rfl

theorem cell23_3222095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2, 2].length) (baseStart_3222095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222095 prefixEnd_3222095 := by exact prefixLift 3222095
  have htrace : WordTrace (prefixWord ++ tailWord_3222095) baseStart_3222095 baseEnd_3222095 := by
    simpa [prefixWord, tailWord_3222095, baseEnd_3222095] using wordTrace_append hprefix tailTrace_3222095
  have hstable : (prefixWord ++ tailWord_3222095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222095).length < 2 ^ (prefixWord ++ tailWord_3222095).sum := by decide
  have hdescent : baseEnd_3222095 < baseStart_3222095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222131 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 2, 5]
def baseStart_3222131 : Nat := 118140960795 + 3222131 * 2 ^ 59
def prefixEnd_3222131 : Nat := 4983230072969 + 3 ^ 40 * 3222131 * 2
def baseEnd_3222131 : Nat := 551500644917412710448065

theorem tailTrace_3222131 : CollatzResearch.WordTrace tailWord_3222131 prefixEnd_3222131 551500644917412710448065 := by
  unfold tailWord_3222131
  simp only [CollatzResearch.WordTrace]
  refine ⟨117520772289777158008594247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78347181526518105339062831 117520772289777158008594247)
  ·
    refine ⟨176281158434665737012891371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117520772289777158008594247 176281158434665737012891371)
    ·
      refine ⟨264421737651998605519337057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176281158434665737012891371 264421737651998605519337057)
      ·
        refine ⟨198316303238998954139502793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264421737651998605519337057 198316303238998954139502793)
        ·
          refine ⟨148737227429249215604627095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198316303238998954139502793 148737227429249215604627095)
          ·
            refine ⟨223105841143873823406940643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148737227429249215604627095 223105841143873823406940643)
            ·
              refine ⟨334658761715810735110410965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223105841143873823406940643 334658761715810735110410965)
              ·
                refine ⟨7843564727714314104150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 334658761715810735110410965 7843564727714314104150257)
                ·
                  refine ⟨5882673545785735578112693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843564727714314104150257 5882673545785735578112693)
                  ·
                    refine ⟨551500644917412710448065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5882673545785735578112693 551500644917412710448065)
                    ·
                      rfl

theorem cell23_3222131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].length) (baseStart_3222131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222131 prefixEnd_3222131 := by exact prefixLift 3222131
  have htrace : WordTrace (prefixWord ++ tailWord_3222131) baseStart_3222131 baseEnd_3222131 := by
    simpa [prefixWord, tailWord_3222131, baseEnd_3222131] using wordTrace_append hprefix tailTrace_3222131
  have hstable : (prefixWord ++ tailWord_3222131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222131).length < 2 ^ (prefixWord ++ tailWord_3222131).sum := by decide
  have hdescent : baseEnd_3222131 < baseStart_3222131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3]
def baseStart_3222171 : Nat := 118140960795 + 3222171 * 2 ^ 59
def prefixEnd_3222171 : Nat := 4983230072969 + 3 ^ 40 * 3222171 * 2
def baseEnd_3222171 : Nat := 1654522473978417974844011

theorem tailTrace_3222171 : CollatzResearch.WordTrace tailWord_3222171 prefixEnd_3222171 1654522473978417974844011 := by
  unfold tailWord_3222171
  simp only [CollatzResearch.WordTrace]
  refine ⟨117522231209632244840050367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78348154139754829893366911 117522231209632244840050367)
  ·
    refine ⟨176283346814448367260075551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117522231209632244840050367 176283346814448367260075551)
    ·
      refine ⟨264425020221672550890113327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176283346814448367260075551 264425020221672550890113327)
      ·
        refine ⟨396637530332508826335169991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264425020221672550890113327 396637530332508826335169991)
        ·
          refine ⟨594956295498763239502754987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396637530332508826335169991 594956295498763239502754987)
          ·
            refine ⟨892434443248144859254132481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594956295498763239502754987 892434443248144859254132481)
            ·
              refine ⟨669325832436108644440599361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892434443248144859254132481 669325832436108644440599361)
              ·
                refine ⟨501994374327081483330449521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669325832436108644440599361 501994374327081483330449521)
                ·
                  refine ⟨376495780745311112497837141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501994374327081483330449521 376495780745311112497837141)
                  ·
                    refine ⟨4412059930609114599584029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 376495780745311112497837141 4412059930609114599584029)
                    ·
                      refine ⟨1654522473978417974844011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412059930609114599584029 1654522473978417974844011)
                      ·
                        rfl

theorem cell23_3222171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].length) (baseStart_3222171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222171 prefixEnd_3222171 := by exact prefixLift 3222171
  have htrace : WordTrace (prefixWord ++ tailWord_3222171) baseStart_3222171 baseEnd_3222171 := by
    simpa [prefixWord, tailWord_3222171, baseEnd_3222171] using wordTrace_append hprefix tailTrace_3222171
  have hstable : (prefixWord ++ tailWord_3222171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222171).length < 2 ^ (prefixWord ++ tailWord_3222171).sum := by decide
  have hdescent : baseEnd_3222171 < baseStart_3222171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222181 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3222181 : Nat := 118140960795 + 3222181 * 2 ^ 59
def prefixEnd_3222181 : Nat := 4983230072969 + 3 ^ 40 * 3222181 * 2
def baseEnd_3222181 : Nat := 1654527608784962935718965

theorem tailTrace_3222181 : CollatzResearch.WordTrace tailWord_3222181 prefixEnd_3222181 1654527608784962935718965 := by
  unfold tailWord_3222181
  simp only [CollatzResearch.WordTrace]
  refine ⟨117522595939596016547914397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78348397293064011031942931 117522595939596016547914397)
  ·
    refine ⟨44070973477348506205467899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117522595939596016547914397 44070973477348506205467899)
    ·
      refine ⟨66106460216022759308201849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44070973477348506205467899 66106460216022759308201849)
      ·
        refine ⟨49579845162017069481151387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66106460216022759308201849 49579845162017069481151387)
        ·
          refine ⟨74369767743025604221727081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49579845162017069481151387 74369767743025604221727081)
          ·
            refine ⟨55777325807269203166295311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74369767743025604221727081 55777325807269203166295311)
            ·
              refine ⟨83665988710903804749442967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55777325807269203166295311 83665988710903804749442967)
              ·
                refine ⟨125498983066355707124164451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83665988710903804749442967 125498983066355707124164451)
                ·
                  refine ⟨188248474599533560686246677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125498983066355707124164451 188248474599533560686246677)
                  ·
                    refine ⟨8824147246853135657167813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188248474599533560686246677 8824147246853135657167813)
                    ·
                      refine ⟨1654527608784962935718965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8824147246853135657167813 1654527608784962935718965)
                      ·
                        rfl

theorem cell23_3222181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3222181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222181 prefixEnd_3222181 := by exact prefixLift 3222181
  have htrace : WordTrace (prefixWord ++ tailWord_3222181) baseStart_3222181 baseEnd_3222181 := by
    simpa [prefixWord, tailWord_3222181, baseEnd_3222181] using wordTrace_append hprefix tailTrace_3222181
  have hstable : (prefixWord ++ tailWord_3222181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222181).length < 2 ^ (prefixWord ++ tailWord_3222181).sum := by decide
  have hdescent : baseEnd_3222181 < baseStart_3222181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222186 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_3222186 : Nat := 118140960795 + 3222186 * 2 ^ 59
def prefixEnd_3222186 : Nat := 4983230072969 + 3 ^ 40 * 3222186 * 2
def baseEnd_3222186 : Nat := 183836686243137268461827

theorem tailTrace_3222186 : CollatzResearch.WordTrace tailWord_3222186 prefixEnd_3222186 183836686243137268461827 := by
  unfold tailWord_3222186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29380694576144475600461603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78348518869718601601230941 29380694576144475600461603)
  ·
    refine ⟨44071041864216713400692405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29380694576144475600461603 44071041864216713400692405)
    ·
      refine ⟨4131660174770316881314913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44071041864216713400692405 4131660174770316881314913)
      ·
        refine ⟨3098745131077737660986185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131660174770316881314913 3098745131077737660986185)
        ·
          refine ⟨2324058848308303245739639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3098745131077737660986185 2324058848308303245739639)
          ·
            refine ⟨3486088272462454868609459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324058848308303245739639 3486088272462454868609459)
            ·
              refine ⟨5229132408693682302914189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486088272462454868609459 5229132408693682302914189)
              ·
                refine ⟨1960924653260130863592821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5229132408693682302914189 1960924653260130863592821)
                ·
                  refine ⟨183836686243137268461827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1960924653260130863592821 183836686243137268461827)
                  ·
                    rfl

theorem cell23_3222186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_3222186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222186 prefixEnd_3222186 := by exact prefixLift 3222186
  have htrace : WordTrace (prefixWord ++ tailWord_3222186) baseStart_3222186 baseEnd_3222186 := by
    simpa [prefixWord, tailWord_3222186, baseEnd_3222186] using wordTrace_append hprefix tailTrace_3222186
  have hstable : (prefixWord ++ tailWord_3222186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222186).length < 2 ^ (prefixWord ++ tailWord_3222186).sum := by decide
  have hdescent : baseEnd_3222186 < baseStart_3222186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222191 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 8]
def baseStart_3222191 : Nat := 118140960795 + 3222191 * 2 ^ 59
def prefixEnd_3222191 : Nat := 4983230072969 + 3 ^ 40 * 3222191 * 2
def baseEnd_3222191 : Nat := 183836971510167544065991

theorem tailTrace_3222191 : CollatzResearch.WordTrace tailWord_3222191 prefixEnd_3222191 183836971510167544065991 := by
  unfold tailWord_3222191
  simp only [CollatzResearch.WordTrace]
  refine ⟨117522960669559788255778427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78348640446373192170518951 117522960669559788255778427)
  ·
    refine ⟨176284441004339682383667641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117522960669559788255778427 176284441004339682383667641)
    ·
      refine ⟨132213330753254761787750731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176284441004339682383667641 132213330753254761787750731)
      ·
        refine ⟨198319996129882142681626097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132213330753254761787750731 198319996129882142681626097)
        ·
          refine ⟨148739997097411607011219573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198319996129882142681626097 148739997097411607011219573)
          ·
            refine ⟨13944374727882338157301835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148739997097411607011219573 13944374727882338157301835)
            ·
              refine ⟨20916562091823507235952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13944374727882338157301835 20916562091823507235952753)
              ·
                refine ⟨15687421568867630426964565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20916562091823507235952753 15687421568867630426964565)
                ·
                  refine ⟨183836971510167544065991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15687421568867630426964565 183836971510167544065991)
                  ·
                    rfl

theorem cell23_3222191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 8].length) (baseStart_3222191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222191 prefixEnd_3222191 := by exact prefixLift 3222191
  have htrace : WordTrace (prefixWord ++ tailWord_3222191) baseStart_3222191 baseEnd_3222191 := by
    simpa [prefixWord, tailWord_3222191, baseEnd_3222191] using wordTrace_append hprefix tailTrace_3222191
  have hstable : (prefixWord ++ tailWord_3222191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222191).length < 2 ^ (prefixWord ++ tailWord_3222191).sum := by decide
  have hdescent : baseEnd_3222191 < baseStart_3222191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222205 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3222205 : Nat := 118140960795 + 3222205 * 2 ^ 59
def prefixEnd_3222205 : Nat := 4983230072969 + 3 ^ 40 * 3222205 * 2
def baseEnd_3222205 : Nat := 1654539932320670841818855

theorem tailTrace_3222205 : CollatzResearch.WordTrace tailWord_3222205 prefixEnd_3222205 1654539932320670841818855 := by
  unfold tailWord_3222205
  simp only [CollatzResearch.WordTrace]
  refine ⟨117523471291509068646788069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78348980861006045764525379 117523471291509068646788069)
  ·
    refine ⟨22035650867157950371272763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117523471291509068646788069 22035650867157950371272763)
    ·
      refine ⟨33053476300736925556909145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22035650867157950371272763 33053476300736925556909145)
      ·
        refine ⟨24790107225552694167681859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33053476300736925556909145 24790107225552694167681859)
        ·
          refine ⟨37185160838329041251522789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24790107225552694167681859 37185160838329041251522789)
          ·
            refine ⟨6972217657186695234660523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37185160838329041251522789 6972217657186695234660523)
            ·
              refine ⟨10458326485780042851990785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972217657186695234660523 10458326485780042851990785)
              ·
                refine ⟨7843744864335032138993089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10458326485780042851990785 7843744864335032138993089)
                ·
                  refine ⟨5882808648251274104244817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843744864335032138993089 5882808648251274104244817)
                  ·
                    refine ⟨4412106486188455578183613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5882808648251274104244817 4412106486188455578183613)
                    ·
                      refine ⟨1654539932320670841818855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412106486188455578183613 1654539932320670841818855)
                      ·
                        rfl

theorem cell23_3222205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3222205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222205 prefixEnd_3222205 := by exact prefixLift 3222205
  have htrace : WordTrace (prefixWord ++ tailWord_3222205) baseStart_3222205 baseEnd_3222205 := by
    simpa [prefixWord, tailWord_3222205, baseEnd_3222205] using wordTrace_append hprefix tailTrace_3222205
  have hstable : (prefixWord ++ tailWord_3222205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222205).length < 2 ^ (prefixWord ++ tailWord_3222205).sum := by decide
  have hdescent : baseEnd_3222205 < baseStart_3222205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222212 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3222212 : Nat := 118140960795 + 3222212 * 2 ^ 59
def prefixEnd_3222212 : Nat := 4983230072969 + 3 ^ 40 * 3222212 * 2
def baseEnd_3222212 : Nat := 551514508895084104810441

theorem tailTrace_3222212 : CollatzResearch.WordTrace tailWord_3222212 prefixEnd_3222212 551514508895084104810441 := by
  unfold tailWord_3222212
  simp only [CollatzResearch.WordTrace]
  refine ⟨58761863301241854421146445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78349151068322472561528593 58761863301241854421146445)
  ·
    refine ⟨22035698737965695407929917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58761863301241854421146445 22035698737965695407929917)
    ·
      refine ⟨8263387026737135777973719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22035698737965695407929917 8263387026737135777973719)
      ·
        refine ⟨12395080540105703666960579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263387026737135777973719 12395080540105703666960579)
        ·
          refine ⟨18592620810158555500440869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395080540105703666960579 18592620810158555500440869)
          ·
            refine ⟨3486116401904729156332663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18592620810158555500440869 3486116401904729156332663)
            ·
              refine ⟨5229174602857093734498995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486116401904729156332663 5229174602857093734498995)
              ·
                refine ⟨7843761904285640601748493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229174602857093734498995 7843761904285640601748493)
                ·
                  refine ⟨2941410714107115225655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7843761904285640601748493 2941410714107115225655685)
                  ·
                    refine ⟨551514508895084104810441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941410714107115225655685 551514508895084104810441)
                    ·
                      rfl

theorem cell23_3222212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3222212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222212 prefixEnd_3222212 := by exact prefixLift 3222212
  have htrace : WordTrace (prefixWord ++ tailWord_3222212) baseStart_3222212 baseEnd_3222212 := by
    simpa [prefixWord, tailWord_3222212, baseEnd_3222212] using wordTrace_append hprefix tailTrace_3222212
  have hstable : (prefixWord ++ tailWord_3222212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222212).length < 2 ^ (prefixWord ++ tailWord_3222212).sum := by decide
  have hdescent : baseEnd_3222212 < baseStart_3222212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222252 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_3222252 : Nat := 118140960795 + 3222252 * 2 ^ 59
def prefixEnd_3222252 : Nat := 4983230072969 + 3 ^ 40 * 3222252 * 2
def baseEnd_3222252 : Nat := 1654564065911432157931139

theorem tailTrace_3222252 : CollatzResearch.WordTrace tailWord_3222252 prefixEnd_3222252 1654564065911432157931139 := by
  unfold tailWord_3222252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58762592761169397836874505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78350123681559197115832673 58762592761169397836874505)
  ·
    refine ⟨44071944570877048377655879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58762592761169397836874505 44071944570877048377655879)
    ·
      refine ⟨66107916856315572566483819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44071944570877048377655879 66107916856315572566483819)
      ·
        refine ⟨99161875284473358849725729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66107916856315572566483819 99161875284473358849725729)
        ·
          refine ⟨74371406463355019137294297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99161875284473358849725729 74371406463355019137294297)
          ·
            refine ⟨55778554847516264352970723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74371406463355019137294297 55778554847516264352970723)
            ·
              refine ⟨83667832271274396529456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55778554847516264352970723 83667832271274396529456085)
              ·
                refine ⟨1960964818857993668659127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83667832271274396529456085 1960964818857993668659127)
                ·
                  refine ⟨2941447228286990502988691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960964818857993668659127 2941447228286990502988691)
                  ·
                    refine ⟨4412170842430485754483037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941447228286990502988691 4412170842430485754483037)
                    ·
                      refine ⟨1654564065911432157931139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412170842430485754483037 1654564065911432157931139)
                      ·
                        rfl

theorem cell23_3222252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_3222252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222252 prefixEnd_3222252 := by exact prefixLift 3222252
  have htrace : WordTrace (prefixWord ++ tailWord_3222252) baseStart_3222252 baseEnd_3222252 := by
    simpa [prefixWord, tailWord_3222252, baseEnd_3222252] using wordTrace_append hprefix tailTrace_3222252
  have hstable : (prefixWord ++ tailWord_3222252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222252).length < 2 ^ (prefixWord ++ tailWord_3222252).sum := by decide
  have hdescent : baseEnd_3222252 < baseStart_3222252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222262 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3222262 : Nat := 118140960795 + 3222262 * 2 ^ 59
def prefixEnd_3222262 : Nat := 4983230072969 + 3 ^ 40 * 3222262 * 2
def baseEnd_3222262 : Nat := 1654569200717977118806093

theorem tailTrace_3222262 : CollatzResearch.WordTrace tailWord_3222262 prefixEnd_3222262 1654569200717977118806093 := by
  unfold tailWord_3222262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345346890768910461350815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78350366834868378254408693 7345346890768910461350815)
  ·
    refine ⟨11018020336153365692026223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7345346890768910461350815 11018020336153365692026223)
    ·
      refine ⟨16527030504230048538039335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11018020336153365692026223 16527030504230048538039335)
      ·
        refine ⟨24790545756345072807059003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16527030504230048538039335 24790545756345072807059003)
        ·
          refine ⟨37185818634517609210588505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24790545756345072807059003 37185818634517609210588505)
          ·
            refine ⟨27889363975888206907941379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37185818634517609210588505 27889363975888206907941379)
            ·
              refine ⟨41834045963832310361912069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27889363975888206907941379 41834045963832310361912069)
              ·
                refine ⟨7843883618218558192858513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41834045963832310361912069 7843883618218558192858513)
                ·
                  refine ⟨5882912713663918644643885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843883618218558192858513 5882912713663918644643885)
                  ·
                    refine ⟨2206092267623969491741457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5882912713663918644643885 2206092267623969491741457)
                    ·
                      refine ⟨1654569200717977118806093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206092267623969491741457 1654569200717977118806093)
                      ·
                        rfl

theorem cell23_3222262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3222262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222262 prefixEnd_3222262 := by exact prefixLift 3222262
  have htrace : WordTrace (prefixWord ++ tailWord_3222262) baseStart_3222262 baseEnd_3222262 := by
    simpa [prefixWord, tailWord_3222262, baseEnd_3222262] using wordTrace_append hprefix tailTrace_3222262
  have hstable : (prefixWord ++ tailWord_3222262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222262).length < 2 ^ (prefixWord ++ tailWord_3222262).sum := by decide
  have hdescent : baseEnd_3222262 < baseStart_3222262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222312 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3222312 : Nat := 118140960795 + 3222312 * 2 ^ 59
def prefixEnd_3222312 : Nat := 4983230072969 + 3 ^ 40 * 3222312 * 2
def baseEnd_3222312 : Nat := 1654594874750701923180863

theorem tailTrace_3222312 : CollatzResearch.WordTrace tailWord_3222312 prefixEnd_3222312 1654594874750701923180863 := by
  unfold tailWord_3222312
  simp only [CollatzResearch.WordTrace]
  refine ⟨58763686951060712960466595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78351582601414283947288793 58763686951060712960466595)
  ·
    refine ⟨88145530426591069440699893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58763686951060712960466595 88145530426591069440699893)
    ·
      refine ⟨8263643477492912760065615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88145530426591069440699893 8263643477492912760065615)
      ·
        refine ⟨12395465216239369140098423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263643477492912760065615 12395465216239369140098423)
        ·
          refine ⟨18593197824359053710147635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395465216239369140098423 18593197824359053710147635)
          ·
            refine ⟨27889796736538580565221453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18593197824359053710147635 27889796736538580565221453)
            ·
              refine ⟨10458673776201967711958045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27889796736538580565221453 10458673776201967711958045)
              ·
                refine ⟨3922002666075737891984267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10458673776201967711958045 3922002666075737891984267)
                ·
                  refine ⟨5883003999113606837976401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922002666075737891984267 5883003999113606837976401)
                  ·
                    refine ⟨4412252999335205128482301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883003999113606837976401 4412252999335205128482301)
                    ·
                      refine ⟨1654594874750701923180863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412252999335205128482301 1654594874750701923180863)
                      ·
                        rfl

theorem cell23_3222312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3222312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222312 prefixEnd_3222312 := by exact prefixLift 3222312
  have htrace : WordTrace (prefixWord ++ tailWord_3222312) baseStart_3222312 baseEnd_3222312 := by
    simpa [prefixWord, tailWord_3222312, baseEnd_3222312] using wordTrace_append hprefix tailTrace_3222312
  have hstable : (prefixWord ++ tailWord_3222312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222312).length < 2 ^ (prefixWord ++ tailWord_3222312).sum := by decide
  have hdescent : baseEnd_3222312 < baseStart_3222312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222349 : List Nat := [1, 6, 1, 2, 2, 2, 2, 7]
def baseStart_3222349 : Nat := 118140960795 + 3222349 * 2 ^ 59
def prefixEnd_3222349 : Nat := 4983230072969 + 3 ^ 40 * 3222349 * 2
def baseEnd_3222349 : Nat := 61281995316108084385859

theorem tailTrace_3222349 : CollatzResearch.WordTrace tailWord_3222349 prefixEnd_3222349 61281995316108084385859 := by
  unfold tailWord_3222349
  simp only [CollatzResearch.WordTrace]
  refine ⟨117528723402987381240030101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78352482268658254160020067 117528723402987381240030101)
  ·
    refine ⟨5509158909515033495626411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117528723402987381240030101 5509158909515033495626411)
    ·
      refine ⟨8263738364272550243439617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509158909515033495626411 8263738364272550243439617)
      ·
        refine ⟨6197803773204412682579713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8263738364272550243439617 6197803773204412682579713)
        ·
          refine ⟨4648352829903309511934785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6197803773204412682579713 4648352829903309511934785)
          ·
            refine ⟨3486264622427482133951089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648352829903309511934785 3486264622427482133951089)
            ·
              refine ⟨2614698466820611600463317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486264622427482133951089 2614698466820611600463317)
              ·
                refine ⟨61281995316108084385859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2614698466820611600463317 61281995316108084385859)
                ·
                  rfl

theorem cell23_3222349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 7].length) (baseStart_3222349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222349 prefixEnd_3222349 := by exact prefixLift 3222349
  have htrace : WordTrace (prefixWord ++ tailWord_3222349) baseStart_3222349 baseEnd_3222349 := by
    simpa [prefixWord, tailWord_3222349, baseEnd_3222349] using wordTrace_append hprefix tailTrace_3222349
  have hstable : (prefixWord ++ tailWord_3222349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222349).length < 2 ^ (prefixWord ++ tailWord_3222349).sum := by decide
  have hdescent : baseEnd_3222349 < baseStart_3222349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222352 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2]
def baseStart_3222352 : Nat := 118140960795 + 3222352 * 2 ^ 59
def prefixEnd_3222352 : Nat := 4983230072969 + 3 ^ 40 * 3222352 * 2
def baseEnd_3222352 : Nat := 1654615413976881766680679

theorem tailTrace_3222352 : CollatzResearch.WordTrace tailWord_3222352 prefixEnd_3222352 1654615413976881766680679 := by
  unfold tailWord_3222352
  simp only [CollatzResearch.WordTrace]
  refine ⟨58764416410988256376194655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78352555214651008501592873 58764416410988256376194655)
  ·
    refine ⟨88146624616482384564291983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58764416410988256376194655 88146624616482384564291983)
    ·
      refine ⟨132219936924723576846437975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88146624616482384564291983 132219936924723576846437975)
      ·
        refine ⟨198329905387085365269656963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132219936924723576846437975 198329905387085365269656963)
        ·
          refine ⟨297494858080628047904485445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198329905387085365269656963 297494858080628047904485445)
          ·
            refine ⟨55780285890117758982091021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297494858080628047904485445 55780285890117758982091021)
            ·
              refine ⟨20917607208794159618284133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55780285890117758982091021 20917607208794159618284133)
              ·
                refine ⟨3922051351648904928428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20917607208794159618284133 3922051351648904928428275)
                ·
                  refine ⟨5883077027473357392642413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922051351648904928428275 5883077027473357392642413)
                  ·
                    refine ⟨2206153885302509022240905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5883077027473357392642413 2206153885302509022240905)
                    ·
                      refine ⟨1654615413976881766680679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206153885302509022240905 1654615413976881766680679)
                      ·
                        rfl

theorem cell23_3222352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2].length) (baseStart_3222352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222352 prefixEnd_3222352 := by exact prefixLift 3222352
  have htrace : WordTrace (prefixWord ++ tailWord_3222352) baseStart_3222352 baseEnd_3222352 := by
    simpa [prefixWord, tailWord_3222352, baseEnd_3222352] using wordTrace_append hprefix tailTrace_3222352
  have hstable : (prefixWord ++ tailWord_3222352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222352).length < 2 ^ (prefixWord ++ tailWord_3222352).sum := by decide
  have hdescent : baseEnd_3222352 < baseStart_3222352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222435 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 2, 5]
def baseStart_3222435 : Nat := 118140960795 + 3222435 * 2 ^ 59
def prefixEnd_3222435 : Nat := 4983230072969 + 3 ^ 40 * 3222435 * 2
def baseEnd_3222435 : Nat := 551552677623734980647599

theorem tailTrace_3222435 : CollatzResearch.WordTrace tailWord_3222435 prefixEnd_3222435 551552677623734980647599 := by
  unfold tailWord_3222435
  simp only [CollatzResearch.WordTrace]
  refine ⟨117531860080675817927660759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78354573387117211951773839 117531860080675817927660759)
  ·
    refine ⟨176297790121013726891491139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117531860080675817927660759 176297790121013726891491139)
    ·
      refine ⟨264446685181520590337236709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176297790121013726891491139 264446685181520590337236709)
      ·
        refine ⟨49583753471535110688231883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264446685181520590337236709 49583753471535110688231883)
        ·
          refine ⟨74375630207302666032347825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49583753471535110688231883 74375630207302666032347825)
          ·
            refine ⟨55781722655476999524260869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74375630207302666032347825 55781722655476999524260869)
            ·
              refine ⟨10459072997901937410798913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55781722655476999524260869 10459072997901937410798913)
              ·
                refine ⟨7844304748426453058099185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10459072997901937410798913 7844304748426453058099185)
                ·
                  refine ⟨5883228561319839793574389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7844304748426453058099185 5883228561319839793574389)
                  ·
                    refine ⟨551552677623734980647599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883228561319839793574389 551552677623734980647599)
                    ·
                      rfl

theorem cell23_3222435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].length) (baseStart_3222435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222435 prefixEnd_3222435 := by exact prefixLift 3222435
  have htrace : WordTrace (prefixWord ++ tailWord_3222435) baseStart_3222435 baseEnd_3222435 := by
    simpa [prefixWord, tailWord_3222435, baseEnd_3222435] using wordTrace_append hprefix tailTrace_3222435
  have hstable : (prefixWord ++ tailWord_3222435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222435).length < 2 ^ (prefixWord ++ tailWord_3222435).sum := by decide
  have hdescent : baseEnd_3222435 < baseStart_3222435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222439 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 5]
def baseStart_3222439 : Nat := 118140960795 + 3222439 * 2 ^ 59
def prefixEnd_3222439 : Nat := 4983230072969 + 3 ^ 40 * 3222439 * 2
def baseEnd_3222439 : Nat := 183851120754869214032531

theorem tailTrace_3222439 : CollatzResearch.WordTrace tailWord_3222439 prefixEnd_3222439 183851120754869214032531 := by
  unfold tailWord_3222439
  simp only [CollatzResearch.WordTrace]
  refine ⟨117532005972661326610806371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78354670648440884407204247 117532005972661326610806371)
  ·
    refine ⟨176298008958991989916209557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117532005972661326610806371 176298008958991989916209557)
    ·
      refine ⟨8263969169952749527322323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176298008958991989916209557 8263969169952749527322323)
      ·
        refine ⟨12395953754929124290983485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263969169952749527322323 12395953754929124290983485)
        ·
          refine ⟨4648482658098421609118807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12395953754929124290983485 4648482658098421609118807)
          ·
            refine ⟨6972723987147632413678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648482658098421609118807 6972723987147632413678211)
            ·
              refine ⟨10459085980721448620517317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972723987147632413678211 10459085980721448620517317)
              ·
                refine ⟨1961078621385271616346997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10459085980721448620517317 1961078621385271616346997)
                ·
                  refine ⟨183851120754869214032531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1961078621385271616346997 183851120754869214032531)
                  ·
                    rfl

theorem cell23_3222439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 5].length) (baseStart_3222439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222439 prefixEnd_3222439 := by exact prefixLift 3222439
  have htrace : WordTrace (prefixWord ++ tailWord_3222439) baseStart_3222439 baseEnd_3222439 := by
    simpa [prefixWord, tailWord_3222439, baseEnd_3222439] using wordTrace_append hprefix tailTrace_3222439
  have hstable : (prefixWord ++ tailWord_3222439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222439).length < 2 ^ (prefixWord ++ tailWord_3222439).sum := by decide
  have hdescent : baseEnd_3222439 < baseStart_3222439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
