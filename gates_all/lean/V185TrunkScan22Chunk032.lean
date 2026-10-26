import V185TrunkScan22Chunk031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_287560 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_287560 : Nat := 118140960795 + 287560 * 2 ^ 59
def prefixEnd_287560 : Nat := 4983230072969 + 3 ^ 40 * 287560 * 2
def baseEnd_287560 : Nat := 98437664671333435918361

theorem tailTrace_287560 : CollatzResearch.WordTrace tailWord_287560 prefixEnd_287560 98437664671333435918361 := by
  unfold tailWord_287560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244087419113353091578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6992116558817804122104089 5244087419113353091578067)
  ·
    refine ⟨7866131128670029637367101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5244087419113353091578067 7866131128670029637367101)
    ·
      refine ⟨2949799173251261114012663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7866131128670029637367101 2949799173251261114012663)
      ·
        refine ⟨4424698759876891671018995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949799173251261114012663 4424698759876891671018995)
        ·
          refine ⟨6637048139815337506528493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424698759876891671018995 6637048139815337506528493)
          ·
            refine ⟨2488893052430751564948185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6637048139815337506528493 2488893052430751564948185)
            ·
              refine ⟨1866669789323063673711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488893052430751564948185 1866669789323063673711139)
              ·
                refine ⟨2800004683984595510566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866669789323063673711139 2800004683984595510566709)
                ·
                  refine ⟨262500439123555829115629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800004683984595510566709 262500439123555829115629)
                  ·
                    refine ⟨98437664671333435918361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262500439123555829115629 98437664671333435918361)
                    ·
                      rfl

theorem cell22_287560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_287560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287560 prefixEnd_287560 := by exact prefixLift 287560
  have htrace : WordTrace (prefixWord ++ tailWord_287560) baseStart_287560 baseEnd_287560 := by
    simpa [prefixWord, tailWord_287560, baseEnd_287560] using wordTrace_append hprefix tailTrace_287560
  have hstable : (prefixWord ++ tailWord_287560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287560).length < 2 ^ (prefixWord ++ tailWord_287560).sum := by decide
  have hdescent : baseEnd_287560 < baseStart_287560 := by decide
  rcases family_descends (prefixWord ++ tailWord_287560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287605 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_287605 : Nat := 118140960795 + 287605 * 2 ^ 59
def prefixEnd_287605 : Nat := 4983230072969 + 3 ^ 40 * 287605 * 2
def baseEnd_287605 : Nat := 98453069090968318543223

theorem tailTrace_287605 : CollatzResearch.WordTrace tailWord_287605 prefixEnd_287605 98453069090968318543223 := by
  unfold tailWord_287605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489816123063678868544269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993210748709119245696179 10489816123063678868544269)
  ·
    refine ⟨3933681046148879575704101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10489816123063678868544269 3933681046148879575704101)
    ·
      refine ⟨737565196152914920444519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3933681046148879575704101 737565196152914920444519)
      ·
        refine ⟨1106347794229372380666779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737565196152914920444519 1106347794229372380666779)
        ·
          refine ⟨1659521691344058571000169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106347794229372380666779 1659521691344058571000169)
          ·
            refine ⟨1244641268508043928250127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659521691344058571000169 1244641268508043928250127)
            ·
              refine ⟨1866961902762065892375191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244641268508043928250127 1866961902762065892375191)
              ·
                refine ⟨2800442854143098838562787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866961902762065892375191 2800442854143098838562787)
                ·
                  refine ⟨4200664281214648257844181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800442854143098838562787 4200664281214648257844181)
                  ·
                    refine ⟨98453069090968318543223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4200664281214648257844181 98453069090968318543223)
                    ·
                      rfl

theorem cell22_287605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_287605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287605 prefixEnd_287605 := by exact prefixLift 287605
  have htrace : WordTrace (prefixWord ++ tailWord_287605) baseStart_287605 baseEnd_287605 := by
    simpa [prefixWord, tailWord_287605, baseEnd_287605] using wordTrace_append hprefix tailTrace_287605
  have hstable : (prefixWord ++ tailWord_287605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287605).length < 2 ^ (prefixWord ++ tailWord_287605).sum := by decide
  have hdescent : baseEnd_287605 < baseStart_287605 := by decide
  rcases family_descends (prefixWord ++ tailWord_287605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287637 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_287637 : Nat := 118140960795 + 287637 * 2 ^ 59
def prefixEnd_287637 : Nat := 4983230072969 + 3 ^ 40 * 287637 * 2
def baseEnd_287637 : Nat := 98464023344930901743125

theorem tailTrace_287637 : CollatzResearch.WordTrace tailWord_287637 prefixEnd_287637 98464023344930901743125 := by
  unfold tailWord_287637
  simp only [CollatzResearch.WordTrace]
  refine ⟨10490983258947748333709165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993988839298498889139443 10490983258947748333709165)
  ·
    refine ⟨3934118722105405625140937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10490983258947748333709165 3934118722105405625140937)
    ·
      refine ⟨2950589041579054218855703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3934118722105405625140937 2950589041579054218855703)
      ·
        refine ⟨4425883562368581328283555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950589041579054218855703 4425883562368581328283555)
        ·
          refine ⟨6638825343552871992425333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425883562368581328283555 6638825343552871992425333)
          ·
            refine ⟨622389875958081749289875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6638825343552871992425333 622389875958081749289875)
            ·
              refine ⟨933584813937122623934813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622389875958081749289875 933584813937122623934813)
              ·
                refine ⟨350094305226420983975555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933584813937122623934813 350094305226420983975555)
                ·
                  refine ⟨525141457839631475963333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350094305226420983975555 525141457839631475963333)
                  ·
                    refine ⟨98464023344930901743125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525141457839631475963333 98464023344930901743125)
                    ·
                      rfl

theorem cell22_287637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_287637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287637 prefixEnd_287637 := by exact prefixLift 287637
  have htrace : WordTrace (prefixWord ++ tailWord_287637) baseStart_287637 baseEnd_287637 := by
    simpa [prefixWord, tailWord_287637, baseEnd_287637] using wordTrace_append hprefix tailTrace_287637
  have hstable : (prefixWord ++ tailWord_287637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287637).length < 2 ^ (prefixWord ++ tailWord_287637).sum := by decide
  have hdescent : baseEnd_287637 < baseStart_287637 := by decide
  rcases family_descends (prefixWord ++ tailWord_287637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287652 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_287652 : Nat := 118140960795 + 287652 * 2 ^ 59
def prefixEnd_287652 : Nat := 4983230072969 + 3 ^ 40 * 287652 * 2
def baseEnd_287652 : Nat := 32823052717158620872693

theorem tailTrace_287652 : CollatzResearch.WordTrace tailWord_287652 prefixEnd_287652 32823052717158620872693 := by
  unfold tailWord_287652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245765176946702947752605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6994353569262270597003473 5245765176946702947752605)
  ·
    refine ⟨1967161941355013605407227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5245765176946702947752605 1967161941355013605407227)
    ·
      refine ⟨2950742912032520408110841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1967161941355013605407227 2950742912032520408110841)
      ·
        refine ⟨2213057184024390306083131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2950742912032520408110841 2213057184024390306083131)
        ·
          refine ⟨3319585776036585459124697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213057184024390306083131 3319585776036585459124697)
          ·
            refine ⟨2489689332027439094343523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319585776036585459124697 2489689332027439094343523)
            ·
              refine ⟨3734533998041158641515285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489689332027439094343523 3734533998041158641515285)
              ·
                refine ⟨175056281158179311321029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3734533998041158641515285 175056281158179311321029)
                ·
                  refine ⟨32823052717158620872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175056281158179311321029 32823052717158620872693)
                  ·
                    rfl

theorem cell22_287652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_287652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287652 prefixEnd_287652 := by exact prefixLift 287652
  have htrace : WordTrace (prefixWord ++ tailWord_287652) baseStart_287652 baseEnd_287652 := by
    simpa [prefixWord, tailWord_287652, baseEnd_287652] using wordTrace_append hprefix tailTrace_287652
  have hstable : (prefixWord ++ tailWord_287652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287652).length < 2 ^ (prefixWord ++ tailWord_287652).sum := by decide
  have hdescent : baseEnd_287652 < baseStart_287652 := by decide
  rcases family_descends (prefixWord ++ tailWord_287652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287680 : List Nat := [2, 1, 1, 2, 3, 4, 1, 8]
def baseStart_287680 : Nat := 118140960795 + 287680 * 2 ^ 59
def prefixEnd_287680 : Nat := 4983230072969 + 3 ^ 40 * 287680 * 2
def baseEnd_287680 : Nat := 10942082569299235879777

theorem tailTrace_287680 : CollatzResearch.WordTrace tailWord_287680 prefixEnd_287680 10942082569299235879777 := by
  unfold tailWord_287680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246275798895983338762247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6995034398527977785016329 5246275798895983338762247)
  ·
    refine ⟨7869413698343975008143371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5246275798895983338762247 7869413698343975008143371)
    ·
      refine ⟨11804120547515962512215057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7869413698343975008143371 11804120547515962512215057)
      ·
        refine ⟨8853090410636971884161293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11804120547515962512215057 8853090410636971884161293)
        ·
          refine ⟨3319908903988864456560485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8853090410636971884161293 3319908903988864456560485)
          ·
            refine ⟨622482919497912085605091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3319908903988864456560485 622482919497912085605091)
            ·
              refine ⟨933724379246868128407637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622482919497912085605091 933724379246868128407637)
              ·
                refine ⟨10942082569299235879777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 933724379246868128407637 10942082569299235879777)
                ·
                  rfl

theorem cell22_287680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_287680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287680 prefixEnd_287680 := by exact prefixLift 287680
  have htrace : WordTrace (prefixWord ++ tailWord_287680) baseStart_287680 baseEnd_287680 := by
    simpa [prefixWord, tailWord_287680, baseEnd_287680] using wordTrace_append hprefix tailTrace_287680
  have hstable : (prefixWord ++ tailWord_287680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287680).length < 2 ^ (prefixWord ++ tailWord_287680).sum := by decide
  have hdescent : baseEnd_287680 < baseStart_287680 := by decide
  rcases family_descends (prefixWord ++ tailWord_287680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287714 : List Nat := [3, 3, 3, 1, 1, 2, 2, 7]
def baseStart_287714 : Nat := 118140960795 + 287714 * 2 ^ 59
def prefixEnd_287714 : Nat := 4983230072969 + 3 ^ 40 * 287714 * 2
def baseEnd_287714 : Nat := 10943375779836485285321

theorem tailTrace_287714 : CollatzResearch.WordTrace tailWord_287714 prefixEnd_287714 10943375779836485285321 := by
  unfold tailWord_287714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623447919917197621065549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6995861119779193656174797 2623447919917197621065549)
  ·
    refine ⟨983792969968949107899581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2623447919917197621065549 983792969968949107899581)
    ·
      refine ⟨368922363738355915462343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 983792969968949107899581 368922363738355915462343)
      ·
        refine ⟨553383545607533873193515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368922363738355915462343 553383545607533873193515)
        ·
          refine ⟨830075318411300809790273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553383545607533873193515 830075318411300809790273)
          ·
            refine ⟨622556488808475607342705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830075318411300809790273 622556488808475607342705)
            ·
              refine ⟨466917366606356705507029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622556488808475607342705 466917366606356705507029)
              ·
                refine ⟨10943375779836485285321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 466917366606356705507029 10943375779836485285321)
                ·
                  rfl

theorem cell22_287714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_287714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287714 prefixEnd_287714 := by exact prefixLift 287714
  have htrace : WordTrace (prefixWord ++ tailWord_287714) baseStart_287714 baseEnd_287714 := by
    simpa [prefixWord, tailWord_287714, baseEnd_287714] using wordTrace_append hprefix tailTrace_287714
  have hstable : (prefixWord ++ tailWord_287714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287714).length < 2 ^ (prefixWord ++ tailWord_287714).sum := by decide
  have hdescent : baseEnd_287714 < baseStart_287714 := by decide
  rcases family_descends (prefixWord ++ tailWord_287714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287802 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_287802 : Nat := 118140960795 + 287802 * 2 ^ 59
def prefixEnd_287802 : Nat := 4983230072969 + 3 ^ 40 * 287802 * 2
def baseEnd_287802 : Nat := 98520506216925471367619

theorem tailTrace_287802 : CollatzResearch.WordTrace tailWord_287802 prefixEnd_287802 98520506216925471367619 := by
  unfold tailWord_287802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624250325837495378366415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6998000868899987675643773 2624250325837495378366415)
  ·
    refine ⟨3936375488756243067549623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624250325837495378366415 3936375488756243067549623)
    ·
      refine ⟨5904563233134364601324435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936375488756243067549623 5904563233134364601324435)
      ·
        refine ⟨8856844849701546901986653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904563233134364601324435 8856844849701546901986653)
        ·
          refine ⟨3321316818638080088244995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8856844849701546901986653 3321316818638080088244995)
          ·
            refine ⟨4981975227957120132367493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321316818638080088244995 4981975227957120132367493)
            ·
              refine ⟨934120355241960024818905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4981975227957120132367493 934120355241960024818905)
              ·
                refine ⟨700590266431470018614179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934120355241960024818905 700590266431470018614179)
                ·
                  refine ⟨1050885399647205027921269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700590266431470018614179 1050885399647205027921269)
                  ·
                    refine ⟨98520506216925471367619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050885399647205027921269 98520506216925471367619)
                    ·
                      rfl

theorem cell22_287802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_287802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287802 prefixEnd_287802 := by exact prefixLift 287802
  have htrace : WordTrace (prefixWord ++ tailWord_287802) baseStart_287802 baseEnd_287802 := by
    simpa [prefixWord, tailWord_287802, baseEnd_287802] using wordTrace_append hprefix tailTrace_287802
  have hstable : (prefixWord ++ tailWord_287802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287802).length < 2 ^ (prefixWord ++ tailWord_287802).sum := by decide
  have hdescent : baseEnd_287802 < baseStart_287802 := by decide
  rcases family_descends (prefixWord ++ tailWord_287802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287804 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_287804 : Nat := 118140960795 + 287804 * 2 ^ 59
def prefixEnd_287804 : Nat := 4983230072969 + 3 ^ 40 * 287804 * 2
def baseEnd_287804 : Nat := 32840396952599377605871

theorem tailTrace_287804 : CollatzResearch.WordTrace tailWord_287804 prefixEnd_287804 32840396952599377605871 := by
  unfold tailWord_287804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248537124671367927519233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6998049499561823903358977 5248537124671367927519233)
  ·
    refine ⟨3936402843503525945639425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5248537124671367927519233 3936402843503525945639425)
    ·
      refine ⟨2952302132627644459229569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3936402843503525945639425 2952302132627644459229569)
      ·
        refine ⟨2214226599470733344422177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2952302132627644459229569 2214226599470733344422177)
        ·
          refine ⟨1660669949603050008316633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214226599470733344422177 1660669949603050008316633)
          ·
            refine ⟨1245502462202287506237475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660669949603050008316633 1245502462202287506237475)
            ·
              refine ⟨1868253693303431259356213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245502462202287506237475 1868253693303431259356213)
              ·
                refine ⟨175148783747196680564645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1868253693303431259356213 175148783747196680564645)
                ·
                  refine ⟨32840396952599377605871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175148783747196680564645 32840396952599377605871)
                  ·
                    rfl

theorem cell22_287804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_287804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287804 prefixEnd_287804 := by exact prefixLift 287804
  have htrace : WordTrace (prefixWord ++ tailWord_287804) baseStart_287804 baseEnd_287804 := by
    simpa [prefixWord, tailWord_287804, baseEnd_287804] using wordTrace_append hprefix tailTrace_287804
  have hstable : (prefixWord ++ tailWord_287804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287804).length < 2 ^ (prefixWord ++ tailWord_287804).sum := by decide
  have hdescent : baseEnd_287804 < baseStart_287804 := by decide
  rcases family_descends (prefixWord ++ tailWord_287804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287806 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_287806 : Nat := 118140960795 + 287806 * 2 ^ 59
def prefixEnd_287806 : Nat := 4983230072969 + 3 ^ 40 * 287806 * 2
def baseEnd_287806 : Nat := 98521875498670794267607

theorem tailTrace_287806 : CollatzResearch.WordTrace tailWord_287806 prefixEnd_287806 98521875498670794267607 := by
  unfold tailWord_287806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312143399416936274576409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6998098130223660131074181 1312143399416936274576409)
  ·
    refine ⟨984107549562702205932307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1312143399416936274576409 984107549562702205932307)
    ·
      refine ⟨1476161324344053308898461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984107549562702205932307 1476161324344053308898461)
      ·
        refine ⟨553560496629019990836923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1476161324344053308898461 553560496629019990836923)
        ·
          refine ⟨830340744943529986255385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553560496629019990836923 830340744943529986255385)
          ·
            refine ⟨622755558707647489691539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830340744943529986255385 622755558707647489691539)
            ·
              refine ⟨934133338061471234537309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622755558707647489691539 934133338061471234537309)
              ·
                refine ⟨350300001773051712951491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934133338061471234537309 350300001773051712951491)
                ·
                  refine ⟨525450002659577569427237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350300001773051712951491 525450002659577569427237)
                  ·
                    refine ⟨98521875498670794267607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525450002659577569427237 98521875498670794267607)
                    ·
                      rfl

theorem cell22_287806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_287806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287806 prefixEnd_287806 := by exact prefixLift 287806
  have htrace : WordTrace (prefixWord ++ tailWord_287806) baseStart_287806 baseEnd_287806 := by
    simpa [prefixWord, tailWord_287806, baseEnd_287806] using wordTrace_append hprefix tailTrace_287806
  have hstable : (prefixWord ++ tailWord_287806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287806).length < 2 ^ (prefixWord ++ tailWord_287806).sum := by decide
  have hdescent : baseEnd_287806 < baseStart_287806 := by decide
  rcases family_descends (prefixWord ++ tailWord_287806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287821 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 4]
def baseStart_287821 : Nat := 118140960795 + 287821 * 2 ^ 59
def prefixEnd_287821 : Nat := 4983230072969 + 3 ^ 40 * 287821 * 2
def baseEnd_287821 : Nat := 32842336768405251714187

theorem tailTrace_287821 : CollatzResearch.WordTrace tailWord_287821 prefixEnd_287821 32842336768405251714187 := by
  unfold tailWord_287821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497694290281147758407317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6998462860187431838938211 10497694290281147758407317)
  ·
    refine ⟨492079419856928801175343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10497694290281147758407317 492079419856928801175343)
    ·
      refine ⟨738119129785393201763015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492079419856928801175343 738119129785393201763015)
      ·
        refine ⟨1107178694678089802644523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738119129785393201763015 1107178694678089802644523)
        ·
          refine ⟨1660768042017134703966785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107178694678089802644523 1660768042017134703966785)
          ·
            refine ⟨1245576031512851027975089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660768042017134703966785 1245576031512851027975089)
            ·
              refine ⟨934182023634638270981317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245576031512851027975089 934182023634638270981317)
              ·
                refine ⟨175159129431494675808997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 934182023634638270981317 175159129431494675808997)
                ·
                  refine ⟨32842336768405251714187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175159129431494675808997 32842336768405251714187)
                  ·
                    rfl

theorem cell22_287821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_287821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287821 prefixEnd_287821 := by exact prefixLift 287821
  have htrace : WordTrace (prefixWord ++ tailWord_287821) baseStart_287821 baseEnd_287821 := by
    simpa [prefixWord, tailWord_287821, baseEnd_287821] using wordTrace_append hprefix tailTrace_287821
  have hstable : (prefixWord ++ tailWord_287821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287821).length < 2 ^ (prefixWord ++ tailWord_287821).sum := by decide
  have hdescent : baseEnd_287821 < baseStart_287821 := by decide
  rcases family_descends (prefixWord ++ tailWord_287821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287849 : List Nat := [1, 2, 1, 1, 1, 8, 2, 6]
def baseStart_287849 : Nat := 118140960795 + 287849 * 2 ^ 59
def prefixEnd_287849 : Nat := 4983230072969 + 3 ^ 40 * 287849 * 2
def baseEnd_287849 : Nat := 10948510586381446160275

theorem tailTrace_287849 : CollatzResearch.WordTrace tailWord_287849 prefixEnd_287849 10948510586381446160275 := by
  unfold tailWord_287849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498715534179708540426601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6999143689453139026951067 10498715534179708540426601)
  ·
    refine ⟨7874036650634781405319951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10498715534179708540426601 7874036650634781405319951)
    ·
      refine ⟨11811054975952172107979927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874036650634781405319951 11811054975952172107979927)
      ·
        refine ⟨17716582463928258161969891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11811054975952172107979927 17716582463928258161969891)
        ·
          refine ⟨26574873695892387242954837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17716582463928258161969891 26574873695892387242954837)
          ·
            refine ⟨311424301123738913003377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 26574873695892387242954837 311424301123738913003377)
            ·
              refine ⟨233568225842804184752533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311424301123738913003377 233568225842804184752533)
              ·
                refine ⟨10948510586381446160275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233568225842804184752533 10948510586381446160275)
                ·
                  rfl

theorem cell22_287849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 6].length) (baseStart_287849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287849 prefixEnd_287849 := by exact prefixLift 287849
  have htrace : WordTrace (prefixWord ++ tailWord_287849) baseStart_287849 baseEnd_287849 := by
    simpa [prefixWord, tailWord_287849, baseEnd_287849] using wordTrace_append hprefix tailTrace_287849
  have hstable : (prefixWord ++ tailWord_287849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287849).length < 2 ^ (prefixWord ++ tailWord_287849).sum := by decide
  have hdescent : baseEnd_287849 < baseStart_287849 := by decide
  rcases family_descends (prefixWord ++ tailWord_287849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287881 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_287881 : Nat := 118140960795 + 287881 * 2 ^ 59
def prefixEnd_287881 : Nat := 4983230072969 + 3 ^ 40 * 287881 * 2
def baseEnd_287881 : Nat := 98547549531395598642377

theorem tailTrace_287881 : CollatzResearch.WordTrace tailWord_287881 prefixEnd_287881 98547549531395598642377 := by
  unfold tailWord_287881
  simp only [CollatzResearch.WordTrace]
  refine ⟨10499882670063778005591497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6999921780042518670394331 10499882670063778005591497)
  ·
    refine ⟨7874912002547833504193623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10499882670063778005591497 7874912002547833504193623)
    ·
      refine ⟨11812368003821750256290435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874912002547833504193623 11812368003821750256290435)
      ·
        refine ⟨17718552005732625384435653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812368003821750256290435 17718552005732625384435653)
        ·
          refine ⟨3322228501074867259581685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17718552005732625384435653 3322228501074867259581685)
          ·
            refine ⟨311458921975768805585783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3322228501074867259581685 311458921975768805585783)
            ·
              refine ⟨467188382963653208378675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311458921975768805585783 467188382963653208378675)
              ·
                refine ⟨700782574445479812568013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467188382963653208378675 700782574445479812568013)
                ·
                  refine ⟨262793465417054929713005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700782574445479812568013 262793465417054929713005)
                  ·
                    refine ⟨98547549531395598642377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262793465417054929713005 98547549531395598642377)
                    ·
                      rfl

theorem cell22_287881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_287881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287881 prefixEnd_287881 := by exact prefixLift 287881
  have htrace : WordTrace (prefixWord ++ tailWord_287881) baseStart_287881 baseEnd_287881 := by
    simpa [prefixWord, tailWord_287881, baseEnd_287881] using wordTrace_append hprefix tailTrace_287881
  have hstable : (prefixWord ++ tailWord_287881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287881).length < 2 ^ (prefixWord ++ tailWord_287881).sum := by decide
  have hdescent : baseEnd_287881 < baseStart_287881 := by decide
  rcases family_descends (prefixWord ++ tailWord_287881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287967 : List Nat := [1, 1, 2, 3, 2, 1, 2, 10]
def baseStart_287967 : Nat := 118140960795 + 287967 * 2 ^ 59
def prefixEnd_287967 : Nat := 4983230072969 + 3 ^ 40 * 287967 * 2
def baseEnd_287967 : Nat := 10952998787657782332457

theorem tailTrace_287967 : CollatzResearch.WordTrace tailWord_287967 prefixEnd_287967 10952998787657782332457 := by
  unfold tailWord_287967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503019347752214693222155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002012898501476462148103 10503019347752214693222155)
  ·
    refine ⟨15754529021628322039833233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10503019347752214693222155 15754529021628322039833233)
    ·
      refine ⟨11815896766221241529874925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15754529021628322039833233 11815896766221241529874925)
      ·
        refine ⟨4430961287332965573703097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11815896766221241529874925 4430961287332965573703097)
        ·
          refine ⟨3323220965499724180277323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4430961287332965573703097 3323220965499724180277323)
          ·
            refine ⟨4984831448249586270415985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323220965499724180277323 4984831448249586270415985)
            ·
              refine ⟨3738623586187189702811989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4984831448249586270415985 3738623586187189702811989)
              ·
                refine ⟨10952998787657782332457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3738623586187189702811989 10952998787657782332457)
                ·
                  rfl

theorem cell22_287967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 10].length) (baseStart_287967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287967 prefixEnd_287967 := by exact prefixLift 287967
  have htrace : WordTrace (prefixWord ++ tailWord_287967) baseStart_287967 baseEnd_287967 := by
    simpa [prefixWord, tailWord_287967, baseEnd_287967] using wordTrace_append hprefix tailTrace_287967
  have hstable : (prefixWord ++ tailWord_287967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287967).length < 2 ^ (prefixWord ++ tailWord_287967).sum := by decide
  have hdescent : baseEnd_287967 < baseStart_287967 := by decide
  rcases family_descends (prefixWord ++ tailWord_287967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287969 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_287969 : Nat := 118140960795 + 287969 * 2 ^ 59
def prefixEnd_287969 : Nat := 4983230072969 + 3 ^ 40 * 287969 * 2
def baseEnd_287969 : Nat := 98577673729792702442107

theorem tailTrace_287969 : CollatzResearch.WordTrace tailWord_287969 prefixEnd_287969 98577673729792702442107 := by
  unfold tailWord_287969
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503092293744969034794961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002061529163312689863307 10503092293744969034794961)
  ·
    refine ⟨7877319220308726776096221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10503092293744969034794961 7877319220308726776096221)
    ·
      refine ⟨2953994707615772541036083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7877319220308726776096221 2953994707615772541036083)
      ·
        refine ⟨4430992061423658811554125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953994707615772541036083 4430992061423658811554125)
        ·
          refine ⟨1661622023033872054332797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4430992061423658811554125 1661622023033872054332797)
          ·
            refine ⟨623108258637702020374799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1661622023033872054332797 623108258637702020374799)
            ·
              refine ⟨934662387956553030562199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623108258637702020374799 934662387956553030562199)
              ·
                refine ⟨1401993581934829545843299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934662387956553030562199 1401993581934829545843299)
                ·
                  refine ⟨2102990372902244318764949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401993581934829545843299 2102990372902244318764949)
                  ·
                    refine ⟨98577673729792702442107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2102990372902244318764949 98577673729792702442107)
                    ·
                      rfl

theorem cell22_287969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_287969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287969 prefixEnd_287969 := by exact prefixLift 287969
  have htrace : WordTrace (prefixWord ++ tailWord_287969) baseStart_287969 baseEnd_287969 := by
    simpa [prefixWord, tailWord_287969, baseEnd_287969] using wordTrace_append hprefix tailTrace_287969
  have hstable : (prefixWord ++ tailWord_287969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287969).length < 2 ^ (prefixWord ++ tailWord_287969).sum := by decide
  have hdescent : baseEnd_287969 < baseStart_287969 := by decide
  rcases family_descends (prefixWord ++ tailWord_287969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287973 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 4]
def baseStart_287973 : Nat := 118140960795 + 287973 * 2 ^ 59
def prefixEnd_287973 : Nat := 4983230072969 + 3 ^ 40 * 287973 * 2
def baseEnd_287973 : Nat := 32859681003846008447365

theorem tailTrace_287973 : CollatzResearch.WordTrace tailWord_287973 prefixEnd_287973 32859681003846008447365 := by
  unfold tailWord_287973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503238185730477717940573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002158790486985145293715 10503238185730477717940573)
  ·
    refine ⟨3938714319648929144227715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10503238185730477717940573 3938714319648929144227715)
    ·
      refine ⟨5908071479473393716341573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3938714319648929144227715 5908071479473393716341573)
      ·
        refine ⟨1107763402401261321814045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5908071479473393716341573 1107763402401261321814045)
        ·
          refine ⟨415411275900472995680267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1107763402401261321814045 415411275900472995680267)
          ·
            refine ⟨623116913850709493520401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415411275900472995680267 623116913850709493520401)
            ·
              refine ⟨467337685388032120140301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623116913850709493520401 467337685388032120140301)
              ·
                refine ⟨175251632020512045052613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467337685388032120140301 175251632020512045052613)
                ·
                  refine ⟨32859681003846008447365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175251632020512045052613 32859681003846008447365)
                  ·
                    rfl

theorem cell22_287973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_287973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287973 prefixEnd_287973 := by exact prefixLift 287973
  have htrace : WordTrace (prefixWord ++ tailWord_287973) baseStart_287973 baseEnd_287973 := by
    simpa [prefixWord, tailWord_287973, baseEnd_287973] using wordTrace_append hprefix tailTrace_287973
  have hstable : (prefixWord ++ tailWord_287973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287973).length < 2 ^ (prefixWord ++ tailWord_287973).sum := by decide
  have hdescent : baseEnd_287973 < baseStart_287973 := by decide
  rcases family_descends (prefixWord ++ tailWord_287973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287975 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 1, 4]
def baseStart_287975 : Nat := 118140960795 + 287975 * 2 ^ 59
def prefixEnd_287975 : Nat := 4983230072969 + 3 ^ 40 * 287975 * 2
def baseEnd_287975 : Nat := 98579727652410686792089

theorem tailTrace_287975 : CollatzResearch.WordTrace tailWord_287975 prefixEnd_287975 98579727652410686792089 := by
  unfold tailWord_287975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503311131723232059513379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002207421148821373008919 10503311131723232059513379)
  ·
    refine ⟨15754966697584848089270069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10503311131723232059513379 15754966697584848089270069)
    ·
      refine ⟨1477028127898579508369069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15754966697584848089270069 1477028127898579508369069)
      ·
        refine ⟨553885547961967315638401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1477028127898579508369069 553885547961967315638401)
        ·
          refine ⟨415414160971475486728801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553885547961967315638401 415414160971475486728801)
          ·
            refine ⟨311560620728606615046601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415414160971475486728801 311560620728606615046601)
            ·
              refine ⟨233670465546454961284951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311560620728606615046601 233670465546454961284951)
              ·
                refine ⟨350505698319682441927427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233670465546454961284951 350505698319682441927427)
                ·
                  refine ⟨525758547479523662891141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350505698319682441927427 525758547479523662891141)
                  ·
                    refine ⟨98579727652410686792089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525758547479523662891141 98579727652410686792089)
                    ·
                      rfl

theorem cell22_287975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_287975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287975 prefixEnd_287975 := by exact prefixLift 287975
  have htrace : WordTrace (prefixWord ++ tailWord_287975) baseStart_287975 baseEnd_287975 := by
    simpa [prefixWord, tailWord_287975, baseEnd_287975] using wordTrace_append hprefix tailTrace_287975
  have hstable : (prefixWord ++ tailWord_287975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287975).length < 2 ^ (prefixWord ++ tailWord_287975).sum := by decide
  have hdescent : baseEnd_287975 < baseStart_287975 := by decide
  rcases family_descends (prefixWord ++ tailWord_287975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288018 : List Nat := [3, 2, 4, 2, 1, 1, 1, 8]
def baseStart_288018 : Nat := 118140960795 + 288018 * 2 ^ 59
def prefixEnd_288018 : Nat := 4983230072969 + 3 ^ 40 * 288018 * 2
def baseEnd_288018 : Nat := 10954938603463656440773

theorem tailTrace_288018 : CollatzResearch.WordTrace tailWord_288018 prefixEnd_288018 10954938603463656440773 := by
  unfold tailWord_288018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626219867641862600832177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7003252980378300268885805 2626219867641862600832177)
  ·
    refine ⟨1969664900731396950624133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2626219867641862600832177 1969664900731396950624133)
    ·
      refine ⟨369312168887136928242025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1969664900731396950624133 369312168887136928242025)
      ·
        refine ⟨276984126665352696181519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369312168887136928242025 276984126665352696181519)
        ·
          refine ⟨415476189998029044272279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276984126665352696181519 415476189998029044272279)
          ·
            refine ⟨623214284997043566408419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415476189998029044272279 623214284997043566408419)
            ·
              refine ⟨934821427495565349612629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623214284997043566408419 934821427495565349612629)
              ·
                refine ⟨10954938603463656440773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 934821427495565349612629 10954938603463656440773)
                ·
                  rfl

theorem cell22_288018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_288018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288018 prefixEnd_288018 := by exact prefixLift 288018
  have htrace : WordTrace (prefixWord ++ tailWord_288018) baseStart_288018 baseEnd_288018 := by
    simpa [prefixWord, tailWord_288018, baseEnd_288018] using wordTrace_append hprefix tailTrace_288018
  have hstable : (prefixWord ++ tailWord_288018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288018).length < 2 ^ (prefixWord ++ tailWord_288018).sum := by decide
  have hdescent : baseEnd_288018 < baseStart_288018 := by decide
  rcases family_descends (prefixWord ++ tailWord_288018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288063 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 5]
def baseStart_288063 : Nat := 118140960795 + 288063 * 2 ^ 59
def prefixEnd_288063 : Nat := 4983230072969 + 3 ^ 40 * 288063 * 2
def baseEnd_288063 : Nat := 32869950616935930197273

theorem tailTrace_288063 : CollatzResearch.WordTrace tailWord_288063 prefixEnd_288063 32869950616935930197273 := by
  unfold tailWord_288063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506520755404423088716843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7004347170269615392477895 10506520755404423088716843)
  ·
    refine ⟨15759781133106634633075265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10506520755404423088716843 15759781133106634633075265)
    ·
      refine ⟨11819835849829975974806449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15759781133106634633075265 11819835849829975974806449)
      ·
        refine ⟨8864876887372481981104837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11819835849829975974806449 8864876887372481981104837)
        ·
          refine ⟨1662164416382340371457157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8864876887372481981104837 1662164416382340371457157)
          ·
            refine ⟨311655828071688819648217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1662164416382340371457157 311655828071688819648217)
            ·
              refine ⟨233741871053766614736163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311655828071688819648217 233741871053766614736163)
              ·
                refine ⟨350612806580649922104245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233741871053766614736163 350612806580649922104245)
                ·
                  refine ⟨32869950616935930197273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 350612806580649922104245 32869950616935930197273)
                  ·
                    rfl

theorem cell22_288063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 5].length) (baseStart_288063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288063 prefixEnd_288063 := by exact prefixLift 288063
  have htrace : WordTrace (prefixWord ++ tailWord_288063) baseStart_288063 baseEnd_288063 := by
    simpa [prefixWord, tailWord_288063, baseEnd_288063] using wordTrace_append hprefix tailTrace_288063
  have hstable : (prefixWord ++ tailWord_288063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288063).length < 2 ^ (prefixWord ++ tailWord_288063).sum := by decide
  have hdescent : baseEnd_288063 < baseStart_288063 := by decide
  rcases family_descends (prefixWord ++ tailWord_288063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288074 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_288074 : Nat := 118140960795 + 288074 * 2 ^ 59
def prefixEnd_288074 : Nat := 4983230072969 + 3 ^ 40 * 288074 * 2
def baseEnd_288074 : Nat := 32871205791869142855595

theorem tailTrace_288074 : CollatzResearch.WordTrace tailWord_288074 prefixEnd_288074 32871205791869142855595 := by
  unfold tailWord_288074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626730489591142991841819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7004614638909714644911517 2626730489591142991841819)
  ·
    refine ⟨3940095734386714487762729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626730489591142991841819 3940095734386714487762729)
    ·
      refine ⟨2955071800790035865822047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940095734386714487762729 2955071800790035865822047)
      ·
        refine ⟨4432607701185053798733071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955071800790035865822047 4432607701185053798733071)
        ·
          refine ⟨6648911551777580698099607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432607701185053798733071 6648911551777580698099607)
          ·
            refine ⟨9973367327666371047149411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648911551777580698099607 9973367327666371047149411)
            ·
              refine ⟨14960050991499556570724117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9973367327666371047149411 14960050991499556570724117)
              ·
                refine ⟨701252390226541714252693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14960050991499556570724117 701252390226541714252693)
                ·
                  refine ⟨32871205791869142855595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 701252390226541714252693 32871205791869142855595)
                  ·
                    rfl

theorem cell22_288074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_288074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288074 prefixEnd_288074 := by exact prefixLift 288074
  have htrace : WordTrace (prefixWord ++ tailWord_288074) baseStart_288074 baseEnd_288074 := by
    simpa [prefixWord, tailWord_288074, baseEnd_288074] using wordTrace_append hprefix tailTrace_288074
  have hstable : (prefixWord ++ tailWord_288074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288074).length < 2 ^ (prefixWord ++ tailWord_288074).sum := by decide
  have hdescent : baseEnd_288074 < baseStart_288074 := by decide
  rcases family_descends (prefixWord ++ tailWord_288074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288076 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_288076 : Nat := 118140960795 + 288076 * 2 ^ 59
def prefixEnd_288076 : Nat := 4983230072969 + 3 ^ 40 * 288076 * 2
def baseEnd_288076 : Nat := 98614302016480090016779

theorem tailTrace_288076 : CollatzResearch.WordTrace tailWord_288076 prefixEnd_288076 98614302016480090016779 := by
  unfold tailWord_288076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253497452178663154470041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7004663269571550872626721 5253497452178663154470041)
  ·
    refine ⟨3940123089133997365852531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5253497452178663154470041 3940123089133997365852531)
    ·
      refine ⟨5910184633700996048778797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940123089133997365852531 5910184633700996048778797)
      ·
        refine ⟨2216319237637873518292049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5910184633700996048778797 2216319237637873518292049)
        ·
          refine ⟨1662239428228405138719037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216319237637873518292049 1662239428228405138719037)
          ·
            refine ⟨623339785585651927019639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662239428228405138719037 623339785585651927019639)
            ·
              refine ⟨935009678378477890529459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623339785585651927019639 935009678378477890529459)
              ·
                refine ⟨1402514517567716835794189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935009678378477890529459 1402514517567716835794189)
                ·
                  refine ⟨525942944087893813422821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1402514517567716835794189 525942944087893813422821)
                  ·
                    refine ⟨98614302016480090016779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525942944087893813422821 98614302016480090016779)
                    ·
                      rfl

theorem cell22_288076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_288076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288076 prefixEnd_288076 := by exact prefixLift 288076
  have htrace : WordTrace (prefixWord ++ tailWord_288076) baseStart_288076 baseEnd_288076 := by
    simpa [prefixWord, tailWord_288076, baseEnd_288076] using wordTrace_append hprefix tailTrace_288076
  have hstable : (prefixWord ++ tailWord_288076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288076).length < 2 ^ (prefixWord ++ tailWord_288076).sum := by decide
  have hdescent : baseEnd_288076 < baseStart_288076 := by decide
  rcases family_descends (prefixWord ++ tailWord_288076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288089 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_288089 : Nat := 118140960795 + 288089 * 2 ^ 59
def prefixEnd_288089 : Nat := 4983230072969 + 3 ^ 40 * 288089 * 2
def baseEnd_288089 : Nat := 98618752182152389441739

theorem tailTrace_288089 : CollatzResearch.WordTrace tailWord_288089 prefixEnd_288089 98618752182152389441739 := by
  unfold tailWord_288089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507469053310229529163321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7004979368873486352775547 10507469053310229529163321)
  ·
    refine ⟨7880601789982672146872491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10507469053310229529163321 7880601789982672146872491)
    ·
      refine ⟨11820902684974008220308737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7880601789982672146872491 11820902684974008220308737)
      ·
        refine ⟨8865677013730506165231553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11820902684974008220308737 8865677013730506165231553)
        ·
          refine ⟨6649257760297879623923665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8865677013730506165231553 6649257760297879623923665)
          ·
            refine ⟨4986943320223409717942749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6649257760297879623923665 4986943320223409717942749)
            ·
              refine ⟨1870103745083778644228531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4986943320223409717942749 1870103745083778644228531)
              ·
                refine ⟨2805155617625667966342797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870103745083778644228531 2805155617625667966342797)
                ·
                  refine ⟨1051933356609625487378549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2805155617625667966342797 1051933356609625487378549)
                  ·
                    refine ⟨98618752182152389441739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1051933356609625487378549 98618752182152389441739)
                    ·
                      rfl

theorem cell22_288089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_288089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288089 prefixEnd_288089 := by exact prefixLift 288089
  have htrace : WordTrace (prefixWord ++ tailWord_288089) baseStart_288089 baseEnd_288089 := by
    simpa [prefixWord, tailWord_288089, baseEnd_288089] using wordTrace_append hprefix tailTrace_288089
  have hstable : (prefixWord ++ tailWord_288089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288089).length < 2 ^ (prefixWord ++ tailWord_288089).sum := by decide
  have hdescent : baseEnd_288089 < baseStart_288089 := by decide
  rcases family_descends (prefixWord ++ tailWord_288089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288108 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_288108 : Nat := 118140960795 + 288108 * 2 ^ 59
def prefixEnd_288108 : Nat := 4983230072969 + 3 ^ 40 * 288108 * 2
def baseEnd_288108 : Nat := 32875085423480891072227

theorem tailTrace_288108 : CollatzResearch.WordTrace tailWord_288108 prefixEnd_288108 32875085423480891072227 := by
  unfold tailWord_288108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254081020120697887052489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7005441360160930516069985 5254081020120697887052489)
  ·
    refine ⟨3940560765090523415289367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254081020120697887052489 3940560765090523415289367)
    ·
      refine ⟨5910841147635785122934051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940560765090523415289367 5910841147635785122934051)
      ·
        refine ⟨8866261721453677684401077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910841147635785122934051 8866261721453677684401077)
        ·
          refine ⟨831212036386282282912601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8866261721453677684401077 831212036386282282912601)
          ·
            refine ⟨623409027289711712184451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831212036386282282912601 623409027289711712184451)
            ·
              refine ⟨935113540934567568276677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623409027289711712184451 935113540934567568276677)
              ·
                refine ⟨175333788925231419051877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 935113540934567568276677 175333788925231419051877)
                ·
                  refine ⟨32875085423480891072227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175333788925231419051877 32875085423480891072227)
                  ·
                    rfl

theorem cell22_288108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_288108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288108 prefixEnd_288108 := by exact prefixLift 288108
  have htrace : WordTrace (prefixWord ++ tailWord_288108) baseStart_288108 baseEnd_288108 := by
    simpa [prefixWord, tailWord_288108, baseEnd_288108] using wordTrace_append hprefix tailTrace_288108
  have hstable : (prefixWord ++ tailWord_288108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288108).length < 2 ^ (prefixWord ++ tailWord_288108).sum := by decide
  have hdescent : baseEnd_288108 < baseStart_288108 := by decide
  rcases family_descends (prefixWord ++ tailWord_288108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288151 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 7, 3]
def baseStart_288151 : Nat := 118140960795 + 288151 * 2 ^ 59
def prefixEnd_288151 : Nat := 4983230072969 + 3 ^ 40 * 288151 * 2
def baseEnd_288151 : Nat := 98639976049204894391549

theorem tailTrace_288151 : CollatzResearch.WordTrace tailWord_288151 prefixEnd_288151 98639976049204894391549 := by
  unfold tailWord_288151
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509730379085614117920307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7006486919390409411946871 10509730379085614117920307)
  ·
    refine ⟨15764595568628421176880461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10509730379085614117920307 15764595568628421176880461)
    ·
      refine ⟨5911723338235657941330173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15764595568628421176880461 5911723338235657941330173)
      ·
        refine ⟨2216896251838371727998815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5911723338235657941330173 2216896251838371727998815)
        ·
          refine ⟨3325344377757557591998223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216896251838371727998815 3325344377757557591998223)
          ·
            refine ⟨4988016566636336387997335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325344377757557591998223 4988016566636336387997335)
            ·
              refine ⟨7482024849954504581996003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988016566636336387997335 7482024849954504581996003)
              ·
                refine ⟨11223037274931756872994005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482024849954504581996003 11223037274931756872994005)
                ·
                  refine ⟨263039936131213051710797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11223037274931756872994005 263039936131213051710797)
                  ·
                    refine ⟨98639976049204894391549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263039936131213051710797 98639976049204894391549)
                    ·
                      rfl

theorem cell22_288151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_288151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288151 prefixEnd_288151 := by exact prefixLift 288151
  have htrace : WordTrace (prefixWord ++ tailWord_288151) baseStart_288151 baseEnd_288151 := by
    simpa [prefixWord, tailWord_288151, baseEnd_288151] using wordTrace_append hprefix tailTrace_288151
  have hstable : (prefixWord ++ tailWord_288151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288151).length < 2 ^ (prefixWord ++ tailWord_288151).sum := by decide
  have hdescent : baseEnd_288151 < baseStart_288151 := by decide
  rcases family_descends (prefixWord ++ tailWord_288151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288202 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_288202 : Nat := 118140960795 + 288202 * 2 ^ 59
def prefixEnd_288202 : Nat := 4983230072969 + 3 ^ 40 * 288202 * 2
def baseEnd_288202 : Nat := 98657434391457761366393

theorem tailTrace_288202 : CollatzResearch.WordTrace tailWord_288202 prefixEnd_288202 98657434391457761366393 := by
  unfold tailWord_288202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627897625475212457006715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7007727001267233218684573 2627897625475212457006715)
  ·
    refine ⟨3941846438212818685510073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627897625475212457006715 3941846438212818685510073)
    ·
      refine ⟨2956384828659614014132555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3941846438212818685510073 2956384828659614014132555)
      ·
        refine ⟨4434577242989421021198833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956384828659614014132555 4434577242989421021198833)
        ·
          refine ⟨3325932932242065765899125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434577242989421021198833 3325932932242065765899125)
          ·
            refine ⟨311806212397693665553043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3325932932242065765899125 311806212397693665553043)
            ·
              refine ⟨467709318596540498329565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311806212397693665553043 467709318596540498329565)
              ·
                refine ⟨175390994473702686873587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467709318596540498329565 175390994473702686873587)
                ·
                  refine ⟨263086491710554030310381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175390994473702686873587 263086491710554030310381)
                  ·
                    refine ⟨98657434391457761366393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263086491710554030310381 98657434391457761366393)
                    ·
                      rfl

theorem cell22_288202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_288202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288202 prefixEnd_288202 := by exact prefixLift 288202
  have htrace : WordTrace (prefixWord ++ tailWord_288202) baseStart_288202 baseEnd_288202 := by
    simpa [prefixWord, tailWord_288202, baseEnd_288202] using wordTrace_append hprefix tailTrace_288202
  have hstable : (prefixWord ++ tailWord_288202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288202).length < 2 ^ (prefixWord ++ tailWord_288202).sum := by decide
  have hdescent : baseEnd_288202 < baseStart_288202 := by decide
  rcases family_descends (prefixWord ++ tailWord_288202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288245 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_288245 : Nat := 118140960795 + 288245 * 2 ^ 59
def prefixEnd_288245 : Nat := 4983230072969 + 3 ^ 40 * 288245 * 2
def baseEnd_288245 : Nat := 98672154170219982541261

theorem tailTrace_288245 : CollatzResearch.WordTrace tailWord_288245 prefixEnd_288245 98672154170219982541261 := by
  unfold tailWord_288245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513158840745068171842189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7008772560496712114561459 10513158840745068171842189)
  ·
    refine ⟨3942434565279400564440821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10513158840745068171842189 3942434565279400564440821)
    ·
      refine ⟨369603240494943802916327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3942434565279400564440821 369603240494943802916327)
      ·
        refine ⟨554404860742415704374491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369603240494943802916327 554404860742415704374491)
        ·
          refine ⟨831607291113623556561737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554404860742415704374491 831607291113623556561737)
          ·
            refine ⟨623705468335217667421303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831607291113623556561737 623705468335217667421303)
            ·
              refine ⟨935558202502826501131955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623705468335217667421303 935558202502826501131955)
              ·
                refine ⟨1403337303754239751697933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935558202502826501131955 1403337303754239751697933)
                ·
                  refine ⟨526251488907839906886725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1403337303754239751697933 526251488907839906886725)
                  ·
                    refine ⟨98672154170219982541261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526251488907839906886725 98672154170219982541261)
                    ·
                      rfl

theorem cell22_288245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_288245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288245 prefixEnd_288245 := by exact prefixLift 288245
  have htrace : WordTrace (prefixWord ++ tailWord_288245) baseStart_288245 baseEnd_288245 := by
    simpa [prefixWord, tailWord_288245, baseEnd_288245] using wordTrace_append hprefix tailTrace_288245
  have hstable : (prefixWord ++ tailWord_288245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288245).length < 2 ^ (prefixWord ++ tailWord_288245).sum := by decide
  have hdescent : baseEnd_288245 < baseStart_288245 := by decide
  rcases family_descends (prefixWord ++ tailWord_288245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288275 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 2, 3]
def baseStart_288275 : Nat := 118140960795 + 288275 * 2 ^ 59
def prefixEnd_288275 : Nat := 4983230072969 + 3 ^ 40 * 288275 * 2
def baseEnd_288275 : Nat := 98682423783309904291169

theorem tailTrace_288275 : CollatzResearch.WordTrace tailWord_288275 prefixEnd_288275 98682423783309904291169 := by
  unfold tailWord_288275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514253030636383295434279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7009502020424255530289519 10514253030636383295434279)
  ·
    refine ⟨15771379545954574943151419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10514253030636383295434279 15771379545954574943151419)
    ·
      refine ⟨23657069318931862414727129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15771379545954574943151419 23657069318931862414727129)
      ·
        refine ⟨17742801989198896811045347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23657069318931862414727129 17742801989198896811045347)
        ·
          refine ⟨26614202983798345216568021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742801989198896811045347 26614202983798345216568021)
          ·
            refine ⟨623770382432773716013313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26614202983798345216568021 623770382432773716013313)
            ·
              refine ⟨467827786824580287009985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623770382432773716013313 467827786824580287009985)
              ·
                refine ⟨350870840118435215257489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467827786824580287009985 350870840118435215257489)
                ·
                  refine ⟨263153130088826411443117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350870840118435215257489 263153130088826411443117)
                  ·
                    refine ⟨98682423783309904291169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263153130088826411443117 98682423783309904291169)
                    ·
                      rfl

theorem cell22_288275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].length) (baseStart_288275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288275 prefixEnd_288275 := by exact prefixLift 288275
  have htrace : WordTrace (prefixWord ++ tailWord_288275) baseStart_288275 baseEnd_288275 := by
    simpa [prefixWord, tailWord_288275, baseEnd_288275] using wordTrace_append hprefix tailTrace_288275
  have hstable : (prefixWord ++ tailWord_288275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288275).length < 2 ^ (prefixWord ++ tailWord_288275).sum := by decide
  have hdescent : baseEnd_288275 < baseStart_288275 := by decide
  rcases family_descends (prefixWord ++ tailWord_288275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288277 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 4]
def baseStart_288277 : Nat := 118140960795 + 288277 * 2 ^ 59
def prefixEnd_288277 : Nat := 4983230072969 + 3 ^ 40 * 288277 * 2
def baseEnd_288277 : Nat := 32894369474727521913721

theorem tailTrace_288277 : CollatzResearch.WordTrace tailWord_288277 prefixEnd_288277 32894369474727521913721 := by
  unfold tailWord_288277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514325976629137637007085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7009550651086091758004723 10514325976629137637007085)
  ·
    refine ⟨3942872241235926613877657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10514325976629137637007085 3942872241235926613877657)
    ·
      refine ⟨2957154180926944960408243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3942872241235926613877657 2957154180926944960408243)
      ·
        refine ⟨4435731271390417440612365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957154180926944960408243 4435731271390417440612365)
        ·
          refine ⟨1663399226771406540229637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4435731271390417440612365 1663399226771406540229637)
          ·
            refine ⟨311887355019638726293057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1663399226771406540229637 311887355019638726293057)
            ·
              refine ⟨233915516264729044719793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311887355019638726293057 233915516264729044719793)
              ·
                refine ⟨175436637198546783539845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233915516264729044719793 175436637198546783539845)
                ·
                  refine ⟨32894369474727521913721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175436637198546783539845 32894369474727521913721)
                  ·
                    rfl

theorem cell22_288277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_288277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288277 prefixEnd_288277 := by exact prefixLift 288277
  have htrace : WordTrace (prefixWord ++ tailWord_288277) baseStart_288277 baseEnd_288277 := by
    simpa [prefixWord, tailWord_288277, baseEnd_288277] using wordTrace_append hprefix tailTrace_288277
  have hstable : (prefixWord ++ tailWord_288277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288277).length < 2 ^ (prefixWord ++ tailWord_288277).sum := by decide
  have hdescent : baseEnd_288277 < baseStart_288277 := by decide
  rcases family_descends (prefixWord ++ tailWord_288277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288288 : List Nat := [2, 1, 1, 6, 1, 1, 3, 7]
def baseStart_288288 : Nat := 118140960795 + 288288 * 2 ^ 59
def prefixEnd_288288 : Nat := 4983230072969 + 3 ^ 40 * 288288 * 2
def baseEnd_288288 : Nat := 10965208216553578190681

theorem tailTrace_288288 : CollatzResearch.WordTrace tailWord_288288 prefixEnd_288288 10965208216553578190681 := by
  unfold tailWord_288288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257363589794643257828759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7009818119726191010438345 5257363589794643257828759)
  ·
    refine ⟨7886045384691964886743139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5257363589794643257828759 7886045384691964886743139)
    ·
      refine ⟨11829068077037947330114709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886045384691964886743139 11829068077037947330114709)
      ·
        refine ⟨554487566111153781099127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11829068077037947330114709 554487566111153781099127)
        ·
          refine ⟨831731349166730671648691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554487566111153781099127 831731349166730671648691)
          ·
            refine ⟨1247597023750096007473037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831731349166730671648691 1247597023750096007473037)
            ·
              refine ⟨467848883906286002802389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247597023750096007473037 467848883906286002802389)
              ·
                refine ⟨10965208216553578190681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 467848883906286002802389 10965208216553578190681)
                ·
                  rfl

theorem cell22_288288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_288288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288288 prefixEnd_288288 := by exact prefixLift 288288
  have htrace : WordTrace (prefixWord ++ tailWord_288288) baseStart_288288 baseEnd_288288 := by
    simpa [prefixWord, tailWord_288288, baseEnd_288288] using wordTrace_append hprefix tailTrace_288288
  have hstable : (prefixWord ++ tailWord_288288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288288).length < 2 ^ (prefixWord ++ tailWord_288288).sum := by decide
  have hdescent : baseEnd_288288 < baseStart_288288 := by decide
  rcases family_descends (prefixWord ++ tailWord_288288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288326 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_288326 : Nat := 118140960795 + 288326 * 2 ^ 59
def prefixEnd_288326 : Nat := 4983230072969 + 3 ^ 40 * 288326 * 2
def baseEnd_288326 : Nat := 98699882125562771266013

theorem tailTrace_288326 : CollatzResearch.WordTrace tailWord_288326 prefixEnd_288326 98699882125562771266013 := by
  unfold tailWord_288326
  simp only [CollatzResearch.WordTrace]
  refine ⟨328628536045363093923151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7010742102301079337027221 328628536045363093923151)
  ·
    refine ⟨492942804068044640884727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328628536045363093923151 492942804068044640884727)
    ·
      refine ⟨739414206102066961327091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492942804068044640884727 739414206102066961327091)
      ·
        refine ⟨1109121309153100441990637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739414206102066961327091 1109121309153100441990637)
        ·
          refine ⟨415920490932412665746489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109121309153100441990637 415920490932412665746489)
          ·
            refine ⟨311940368199309499309867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415920490932412665746489 311940368199309499309867)
            ·
              refine ⟨467910552298964248964801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311940368199309499309867 467910552298964248964801)
              ·
                refine ⟨350932914224223186723601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467910552298964248964801 350932914224223186723601)
                ·
                  refine ⟨263199685668167390042701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350932914224223186723601 263199685668167390042701)
                  ·
                    refine ⟨98699882125562771266013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263199685668167390042701 98699882125562771266013)
                    ·
                      rfl

theorem cell22_288326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_288326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288326 prefixEnd_288326 := by exact prefixLift 288326
  have htrace : WordTrace (prefixWord ++ tailWord_288326) baseStart_288326 baseEnd_288326 := by
    simpa [prefixWord, tailWord_288326, baseEnd_288326] using wordTrace_append hprefix tailTrace_288326
  have hstable : (prefixWord ++ tailWord_288326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288326).length < 2 ^ (prefixWord ++ tailWord_288326).sum := by decide
  have hdescent : baseEnd_288326 < baseStart_288326 := by decide
  rcases family_descends (prefixWord ++ tailWord_288326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288414 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_288414 : Nat := 118140960795 + 288414 * 2 ^ 59
def prefixEnd_288414 : Nat := 4983230072969 + 3 ^ 40 * 288414 * 2
def baseEnd_288414 : Nat := 98730006323959875065743

theorem tailTrace_288414 : CollatzResearch.WordTrace tailWord_288414 prefixEnd_288414 98730006323959875065743 := by
  unfold tailWord_288414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314915347141601254343037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7012881851421873356496197 1314915347141601254343037)
  ·
    refine ⟨493093255178100470378639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1314915347141601254343037 493093255178100470378639)
    ·
      refine ⟨739639882767150705567959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493093255178100470378639 739639882767150705567959)
      ·
        refine ⟨1109459824150726058351939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739639882767150705567959 1109459824150726058351939)
        ·
          refine ⟨1664189736226089087527909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109459824150726058351939 1664189736226089087527909)
          ·
            refine ⟨312035575542391703911483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1664189736226089087527909 312035575542391703911483)
            ·
              refine ⟨468053363313587555867225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312035575542391703911483 468053363313587555867225)
              ·
                refine ⟨351040022485190666900419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468053363313587555867225 351040022485190666900419)
                ·
                  refine ⟨526560033727786000350629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351040022485190666900419 526560033727786000350629)
                  ·
                    refine ⟨98730006323959875065743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526560033727786000350629 98730006323959875065743)
                    ·
                      rfl

theorem cell22_288414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_288414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288414 prefixEnd_288414 := by exact prefixLift 288414
  have htrace : WordTrace (prefixWord ++ tailWord_288414) baseStart_288414 baseEnd_288414 := by
    simpa [prefixWord, tailWord_288414, baseEnd_288414] using wordTrace_append hprefix tailTrace_288414
  have hstable : (prefixWord ++ tailWord_288414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288414).length < 2 ^ (prefixWord ++ tailWord_288414).sum := by decide
  have hdescent : baseEnd_288414 < baseStart_288414 := by decide
  rcases family_descends (prefixWord ++ tailWord_288414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288455 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 3, 3]
def baseStart_288455 : Nat := 118140960795 + 288455 * 2 ^ 59
def prefixEnd_288455 : Nat := 4983230072969 + 3 ^ 40 * 288455 * 2
def baseEnd_288455 : Nat := 98744041461849434790617

theorem tailTrace_288455 : CollatzResearch.WordTrace tailWord_288455 prefixEnd_288455 98744041461849434790617 := by
  unfold tailWord_288455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520818169984274036986819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7013878779989516024657879 10520818169984274036986819)
  ·
    refine ⟨15781227254976411055480229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10520818169984274036986819 15781227254976411055480229)
    ·
      refine ⟨2958980110308077072902543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15781227254976411055480229 2958980110308077072902543)
      ·
        refine ⟨4438470165462115609353815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958980110308077072902543 4438470165462115609353815)
        ·
          refine ⟨6657705248193173414030723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4438470165462115609353815 6657705248193173414030723)
          ·
            refine ⟨9986557872289760121046085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6657705248193173414030723 9986557872289760121046085)
            ·
              refine ⟨1872479601054330022696141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9986557872289760121046085 1872479601054330022696141)
              ·
                refine ⟨702179850395373758511053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1872479601054330022696141 702179850395373758511053)
                ·
                  refine ⟨263317443898265159441645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702179850395373758511053 263317443898265159441645)
                  ·
                    refine ⟨98744041461849434790617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263317443898265159441645 98744041461849434790617)
                    ·
                      rfl

theorem cell22_288455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_288455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288455 prefixEnd_288455 := by exact prefixLift 288455
  have htrace : WordTrace (prefixWord ++ tailWord_288455) baseStart_288455 baseEnd_288455 := by
    simpa [prefixWord, tailWord_288455, baseEnd_288455] using wordTrace_append hprefix tailTrace_288455
  have hstable : (prefixWord ++ tailWord_288455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288455).length < 2 ^ (prefixWord ++ tailWord_288455).sum := by decide
  have hdescent : baseEnd_288455 < baseStart_288455 := by decide
  rcases family_descends (prefixWord ++ tailWord_288455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288476 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_288476 : Nat := 118140960795 + 288476 * 2 ^ 59
def prefixEnd_288476 : Nat := 4983230072969 + 3 ^ 40 * 288476 * 2
def baseEnd_288476 : Nat := 98751230191012380015553

theorem tailTrace_288476 : CollatzResearch.WordTrace tailWord_288476 prefixEnd_288476 98751230191012380015553 := by
  unfold tailWord_288476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260792051454097311750641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7014389401938796415667521 5260792051454097311750641)
  ·
    refine ⟨3945594038590572983812981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5260792051454097311750641 3945594038590572983812981)
    ·
      refine ⟨369899441117866217232467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3945594038590572983812981 369899441117866217232467)
      ·
        refine ⟨554849161676799325848701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369899441117866217232467 554849161676799325848701)
        ·
          refine ⟨208068435628799747193263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554849161676799325848701 208068435628799747193263)
          ·
            refine ⟨312102653443199620789895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208068435628799747193263 312102653443199620789895)
            ·
              refine ⟨468153980164799431184843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312102653443199620789895 468153980164799431184843)
              ·
                refine ⟨702230970247199146777265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468153980164799431184843 702230970247199146777265)
                ·
                  refine ⟨526673227685399360082949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702230970247199146777265 526673227685399360082949)
                  ·
                    refine ⟨98751230191012380015553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526673227685399360082949 98751230191012380015553)
                    ·
                      rfl

theorem cell22_288476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_288476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288476 prefixEnd_288476 := by exact prefixLift 288476
  have htrace : WordTrace (prefixWord ++ tailWord_288476) baseStart_288476 baseEnd_288476 := by
    simpa [prefixWord, tailWord_288476, baseEnd_288476] using wordTrace_append hprefix tailTrace_288476
  have hstable : (prefixWord ++ tailWord_288476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288476).length < 2 ^ (prefixWord ++ tailWord_288476).sum := by decide
  have hdescent : baseEnd_288476 < baseStart_288476 := by decide
  rcases family_descends (prefixWord ++ tailWord_288476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288502 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_288502 : Nat := 118140960795 + 288502 * 2 ^ 59
def prefixEnd_288502 : Nat := 4983230072969 + 3 ^ 40 * 288502 * 2
def baseEnd_288502 : Nat := 32920043507452326288491

theorem tailTrace_288502 : CollatzResearch.WordTrace tailWord_288502 prefixEnd_288502 32920043507452326288491 := by
  unfold tailWord_288502
  simp only [CollatzResearch.WordTrace]
  refine ⟨657658275050875066496735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7015021600542667375965173 657658275050875066496735)
  ·
    refine ⟨986487412576312599745103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657658275050875066496735 986487412576312599745103)
    ·
      refine ⟨1479731118864468899617655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986487412576312599745103 1479731118864468899617655)
      ·
        refine ⟨2219596678296703349426483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479731118864468899617655 2219596678296703349426483)
        ·
          refine ⟨3329395017445055024139725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219596678296703349426483 3329395017445055024139725)
          ·
            refine ⟨1248523131541895634052397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3329395017445055024139725 1248523131541895634052397)
            ·
              refine ⟨468196174328210862769649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1248523131541895634052397 468196174328210862769649)
              ·
                refine ⟨351147130746158147077237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468196174328210862769649 351147130746158147077237)
                ·
                  refine ⟨32920043507452326288491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351147130746158147077237 32920043507452326288491)
                  ·
                    rfl

theorem cell22_288502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_288502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288502 prefixEnd_288502 := by exact prefixLift 288502
  have htrace : WordTrace (prefixWord ++ tailWord_288502) baseStart_288502 baseEnd_288502 := by
    simpa [prefixWord, tailWord_288502, baseEnd_288502] using wordTrace_append hprefix tailTrace_288502
  have hstable : (prefixWord ++ tailWord_288502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288502).length < 2 ^ (prefixWord ++ tailWord_288502).sum := by decide
  have hdescent : baseEnd_288502 < baseStart_288502 := by decide
  rcases family_descends (prefixWord ++ tailWord_288502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288519 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 5]
def baseStart_288519 : Nat := 118140960795 + 288519 * 2 ^ 59
def prefixEnd_288519 : Nat := 4983230072969 + 3 ^ 40 * 288519 * 2
def baseEnd_288519 : Nat := 32921983323258200396807

theorem tailTrace_288519 : CollatzResearch.WordTrace tailWord_288519 prefixEnd_288519 32921983323258200396807 := by
  unfold tailWord_288519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523152441752412967316611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7015434961168275311544407 10523152441752412967316611)
  ·
    refine ⟨15784728662628619450974917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523152441752412967316611 15784728662628619450974917)
    ·
      refine ⟨2959636624242866147057797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15784728662628619450974917 2959636624242866147057797)
      ·
        refine ⟨554931867045537402573337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2959636624242866147057797 554931867045537402573337)
        ·
          refine ⟨416198900284153051930003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554931867045537402573337 416198900284153051930003)
          ·
            refine ⟨624298350426229577895005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416198900284153051930003 624298350426229577895005)
            ·
              refine ⟨234111881409836091710627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624298350426229577895005 234111881409836091710627)
              ·
                refine ⟨351167822114754137565941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234111881409836091710627 351167822114754137565941)
                ·
                  refine ⟨32921983323258200396807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351167822114754137565941 32921983323258200396807)
                  ·
                    rfl

theorem cell22_288519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 5].length) (baseStart_288519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288519 prefixEnd_288519 := by exact prefixLift 288519
  have htrace : WordTrace (prefixWord ++ tailWord_288519) baseStart_288519 baseEnd_288519 := by
    simpa [prefixWord, tailWord_288519, baseEnd_288519] using wordTrace_append hprefix tailTrace_288519
  have hstable : (prefixWord ++ tailWord_288519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288519).length < 2 ^ (prefixWord ++ tailWord_288519).sum := by decide
  have hdescent : baseEnd_288519 < baseStart_288519 := by decide
  rcases family_descends (prefixWord ++ tailWord_288519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288525 : List Nat := [1, 7, 2, 1, 2, 1, 2, 6]
def baseStart_288525 : Nat := 118140960795 + 288525 * 2 ^ 59
def prefixEnd_288525 : Nat := 4983230072969 + 3 ^ 40 * 288525 * 2
def baseEnd_288525 : Nat := 10974222654710287282267

theorem tailTrace_288525 : CollatzResearch.WordTrace tailWord_288525 prefixEnd_288525 10974222654710287282267 := by
  unfold tailWord_288525
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523371279730675992035029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7015580853153783994690019 10523371279730675992035029)
  ·
    refine ⟨246641514368687718563321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10523371279730675992035029 246641514368687718563321)
    ·
      refine ⟨184981135776515788922491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246641514368687718563321 184981135776515788922491)
      ·
        refine ⟨277471703664773683383737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184981135776515788922491 277471703664773683383737)
        ·
          refine ⟨208103777748580262537803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277471703664773683383737 208103777748580262537803)
          ·
            refine ⟨312155666622870393806705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208103777748580262537803 312155666622870393806705)
            ·
              refine ⟨234116749967152795355029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312155666622870393806705 234116749967152795355029)
              ·
                refine ⟨10974222654710287282267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234116749967152795355029 10974222654710287282267)
                ·
                  rfl

theorem cell22_288525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 6].length) (baseStart_288525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288525 prefixEnd_288525 := by exact prefixLift 288525
  have htrace : WordTrace (prefixWord ++ tailWord_288525) baseStart_288525 baseEnd_288525 := by
    simpa [prefixWord, tailWord_288525, baseEnd_288525] using wordTrace_append hprefix tailTrace_288525
  have hstable : (prefixWord ++ tailWord_288525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288525).length < 2 ^ (prefixWord ++ tailWord_288525).sum := by decide
  have hdescent : baseEnd_288525 < baseStart_288525 := by decide
  rcases family_descends (prefixWord ++ tailWord_288525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288547 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 4]
def baseStart_288547 : Nat := 118140960795 + 288547 * 2 ^ 59
def prefixEnd_288547 : Nat := 4983230072969 + 3 ^ 40 * 288547 * 2
def baseEnd_288547 : Nat := 32925178313997287163445

theorem tailTrace_288547 : CollatzResearch.WordTrace tailWord_288547 prefixEnd_288547 32925178313997287163445 := by
  unfold tailWord_288547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524173685650973749335895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7016115790433982499557263 10524173685650973749335895)
  ·
    refine ⟨15786260528476460624003843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10524173685650973749335895 15786260528476460624003843)
    ·
      refine ⟨23679390792714690936005765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15786260528476460624003843 23679390792714690936005765)
      ·
        refine ⟨4439885773634004550501081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23679390792714690936005765 4439885773634004550501081)
        ·
          refine ⟨3329914330225503412875811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4439885773634004550501081 3329914330225503412875811)
          ·
            refine ⟨4994871495338255119313717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329914330225503412875811 4994871495338255119313717)
            ·
              refine ⟨468269202687961417435661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4994871495338255119313717 468269202687961417435661)
              ·
                refine ⟨175600951007985531538373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468269202687961417435661 175600951007985531538373)
                ·
                  refine ⟨32925178313997287163445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175600951007985531538373 32925178313997287163445)
                  ·
                    rfl

theorem cell22_288547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 4].length) (baseStart_288547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288547 prefixEnd_288547 := by exact prefixLift 288547
  have htrace : WordTrace (prefixWord ++ tailWord_288547) baseStart_288547 baseEnd_288547 := by
    simpa [prefixWord, tailWord_288547, baseEnd_288547] using wordTrace_append hprefix tailTrace_288547
  have hstable : (prefixWord ++ tailWord_288547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288547).length < 2 ^ (prefixWord ++ tailWord_288547).sum := by decide
  have hdescent : baseEnd_288547 < baseStart_288547 := by decide
  rcases family_descends (prefixWord ++ tailWord_288547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288562 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_288562 : Nat := 118140960795 + 288562 * 2 ^ 59
def prefixEnd_288562 : Nat := 4983230072969 + 3 ^ 40 * 288562 * 2
def baseEnd_288562 : Nat := 98780669748536822365289

theorem tailTrace_288562 : CollatzResearch.WordTrace tailWord_288562 prefixEnd_288562 98780669748536822365289 := by
  unfold tailWord_288562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631180195149157827782985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7016480520397754207421293 2631180195149157827782985)
  ·
    refine ⟨1973385146361868370837239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2631180195149157827782985 1973385146361868370837239)
    ·
      refine ⟨2960077719542802556255859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973385146361868370837239 2960077719542802556255859)
      ·
        refine ⟨4440116579314203834383789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960077719542802556255859 4440116579314203834383789)
        ·
          refine ⟨1665043717242826437893921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4440116579314203834383789 1665043717242826437893921)
          ·
            refine ⟨1248782787932119828420441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665043717242826437893921 1248782787932119828420441)
            ·
              refine ⟨936587090949089871315331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248782787932119828420441 936587090949089871315331)
              ·
                refine ⟨1404880636423634806972997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936587090949089871315331 1404880636423634806972997)
                ·
                  refine ⟨263415119329431526307437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404880636423634806972997 263415119329431526307437)
                  ·
                    refine ⟨98780669748536822365289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263415119329431526307437 98780669748536822365289)
                    ·
                      rfl

theorem cell22_288562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_288562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288562 prefixEnd_288562 := by exact prefixLift 288562
  have htrace : WordTrace (prefixWord ++ tailWord_288562) baseStart_288562 baseEnd_288562 := by
    simpa [prefixWord, tailWord_288562, baseEnd_288562] using wordTrace_append hprefix tailTrace_288562
  have hstable : (prefixWord ++ tailWord_288562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288562).length < 2 ^ (prefixWord ++ tailWord_288562).sum := by decide
  have hdescent : baseEnd_288562 < baseStart_288562 := by decide
  rcases family_descends (prefixWord ++ tailWord_288562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288564 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_288564 : Nat := 118140960795 + 288564 * 2 ^ 59
def prefixEnd_288564 : Nat := 4983230072969 + 3 ^ 40 * 288564 * 2
def baseEnd_288564 : Nat := 32927118129803161271761

theorem tailTrace_288564 : CollatzResearch.WordTrace tailWord_288564 prefixEnd_288564 32927118129803161271761 := by
  unfold tailWord_288564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262396863294692826352373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7016529151059590435136497 5262396863294692826352373)
  ·
    refine ⟨493349705933877452470535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5262396863294692826352373 493349705933877452470535)
    ·
      refine ⟨740024558900816178705803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493349705933877452470535 740024558900816178705803)
      ·
        refine ⟨1110036838351224268058705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740024558900816178705803 1110036838351224268058705)
        ·
          refine ⟨832527628763418201044029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110036838351224268058705 832527628763418201044029)
          ·
            refine ⟨312197860786281825391511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 832527628763418201044029 312197860786281825391511)
            ·
              refine ⟨468296791179422738087267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312197860786281825391511 468296791179422738087267)
              ·
                refine ⟨702445186769134107130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468296791179422738087267 702445186769134107130901)
                ·
                  refine ⟨32927118129803161271761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 702445186769134107130901 32927118129803161271761)
                  ·
                    rfl

theorem cell22_288564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_288564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288564 prefixEnd_288564 := by exact prefixLift 288564
  have htrace : WordTrace (prefixWord ++ tailWord_288564) baseStart_288564 baseEnd_288564 := by
    simpa [prefixWord, tailWord_288564, baseEnd_288564] using wordTrace_append hprefix tailTrace_288564
  have hstable : (prefixWord ++ tailWord_288564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288564).length < 2 ^ (prefixWord ++ tailWord_288564).sum := by decide
  have hdescent : baseEnd_288564 < baseStart_288564 := by decide
  rcases family_descends (prefixWord ++ tailWord_288564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288579 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 2, 3]
def baseStart_288579 : Nat := 118140960795 + 288579 * 2 ^ 59
def prefixEnd_288579 : Nat := 4983230072969 + 3 ^ 40 * 288579 * 2
def baseEnd_288579 : Nat := 98786489195954444690237

theorem tailTrace_288579 : CollatzResearch.WordTrace tailWord_288579 prefixEnd_288579 98786489195954444690237 := by
  unfold tailWord_288579
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525340821535043214500791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7016893881023362143000527 10525340821535043214500791)
  ·
    refine ⟨15788011232302564821751187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525340821535043214500791 15788011232302564821751187)
    ·
      refine ⟨23682016848453847232626781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15788011232302564821751187 23682016848453847232626781)
      ·
        refine ⟨8880756318170192712235043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23682016848453847232626781 8880756318170192712235043)
        ·
          refine ⟨13321134477255289068352565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880756318170192712235043 13321134477255289068352565)
          ·
            refine ⟨1248856357242683350158053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13321134477255289068352565 1248856357242683350158053)
            ·
              refine ⟨234160566983003128154635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1248856357242683350158053 234160566983003128154635)
              ·
                refine ⟨351240850474504692231953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234160566983003128154635 351240850474504692231953)
                ·
                  refine ⟨263430637855878519173965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351240850474504692231953 263430637855878519173965)
                  ·
                    refine ⟨98786489195954444690237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263430637855878519173965 98786489195954444690237)
                    ·
                      rfl

theorem cell22_288579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 3].length) (baseStart_288579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288579 prefixEnd_288579 := by exact prefixLift 288579
  have htrace : WordTrace (prefixWord ++ tailWord_288579) baseStart_288579 baseEnd_288579 := by
    simpa [prefixWord, tailWord_288579, baseEnd_288579] using wordTrace_append hprefix tailTrace_288579
  have hstable : (prefixWord ++ tailWord_288579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288579).length < 2 ^ (prefixWord ++ tailWord_288579).sum := by decide
  have hdescent : baseEnd_288579 < baseStart_288579 := by decide
  rcases family_descends (prefixWord ++ tailWord_288579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288622 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_288622 : Nat := 118140960795 + 288622 * 2 ^ 59
def prefixEnd_288622 : Nat := 4983230072969 + 3 ^ 40 * 288622 * 2
def baseEnd_288622 : Nat := 98801208974716665865105

theorem tailTrace_288622 : CollatzResearch.WordTrace tailWord_288622 prefixEnd_288622 98801208974716665865105 := by
  unfold tailWord_288622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315863645047407694789515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7017939440252841038877413 1315863645047407694789515)
  ·
    refine ⟨1973795467571111542184273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315863645047407694789515 1973795467571111542184273)
    ·
      refine ⟨1480346600678333656638205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1973795467571111542184273 1480346600678333656638205)
      ·
        refine ⟨555129975254375121239327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1480346600678333656638205 555129975254375121239327)
        ·
          refine ⟨832694962881562681858991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555129975254375121239327 832694962881562681858991)
          ·
            refine ⟨1249042444322344022788487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832694962881562681858991 1249042444322344022788487)
            ·
              refine ⟨1873563666483516034182731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249042444322344022788487 1873563666483516034182731)
              ·
                refine ⟨2810345499725274051274097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873563666483516034182731 2810345499725274051274097)
                ·
                  refine ⟨2107759124793955538455573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810345499725274051274097 2107759124793955538455573)
                  ·
                    refine ⟨98801208974716665865105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2107759124793955538455573 98801208974716665865105)
                    ·
                      rfl

theorem cell22_288622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_288622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288622 prefixEnd_288622 := by exact prefixLift 288622
  have htrace : WordTrace (prefixWord ++ tailWord_288622) baseStart_288622 baseEnd_288622 := by
    simpa [prefixWord, tailWord_288622, baseEnd_288622] using wordTrace_append hprefix tailTrace_288622
  have hstable : (prefixWord ++ tailWord_288622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288622).length < 2 ^ (prefixWord ++ tailWord_288622).sum := by decide
  have hdescent : baseEnd_288622 < baseStart_288622 := by decide
  rcases family_descends (prefixWord ++ tailWord_288622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288641 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_288641 : Nat := 118140960795 + 288641 * 2 ^ 59
def prefixEnd_288641 : Nat := 4983230072969 + 3 ^ 40 * 288641 * 2
def baseEnd_288641 : Nat := 98807713063006949640047

theorem tailTrace_288641 : CollatzResearch.WordTrace tailWord_288641 prefixEnd_288641 98807713063006949640047 := by
  unfold tailWord_288641
  simp only [CollatzResearch.WordTrace]
  refine ⟨10527602147310427803257777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7018401431540285202171851 10527602147310427803257777)
  ·
    refine ⟨7895701610482820852443333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10527602147310427803257777 7895701610482820852443333)
    ·
      refine ⟨1480444051965528909833125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7895701610482820852443333 1480444051965528909833125)
      ·
        refine ⟨277583259743536670593711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1480444051965528909833125 277583259743536670593711)
        ·
          refine ⟨416374889615305005890567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277583259743536670593711 416374889615305005890567)
          ·
            refine ⟨624562334422957508835851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416374889615305005890567 624562334422957508835851)
            ·
              refine ⟨936843501634436263253777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624562334422957508835851 936843501634436263253777)
              ·
                refine ⟨702632626225827197440333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936843501634436263253777 702632626225827197440333)
                ·
                  refine ⟨263487234834685199040125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702632626225827197440333 263487234834685199040125)
                  ·
                    refine ⟨98807713063006949640047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263487234834685199040125 98807713063006949640047)
                    ·
                      rfl

theorem cell22_288641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_288641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288641 prefixEnd_288641 := by exact prefixLift 288641
  have htrace : WordTrace (prefixWord ++ tailWord_288641) baseStart_288641 baseEnd_288641 := by
    simpa [prefixWord, tailWord_288641, baseEnd_288641] using wordTrace_append hprefix tailTrace_288641
  have hstable : (prefixWord ++ tailWord_288641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288641).length < 2 ^ (prefixWord ++ tailWord_288641).sum := by decide
  have hdescent : baseEnd_288641 < baseStart_288641 := by decide
  rcases family_descends (prefixWord ++ tailWord_288641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288658 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_288658 : Nat := 118140960795 + 288658 * 2 ^ 59
def prefixEnd_288658 : Nat := 4983230072969 + 3 ^ 40 * 288658 * 2
def baseEnd_288658 : Nat := 98813532510424571964995

theorem tailTrace_288658 : CollatzResearch.WordTrace tailWord_288658 prefixEnd_288658 98813532510424571964995 := by
  unfold tailWord_288658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632055547062209926656657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7018814792165893137751085 2632055547062209926656657)
  ·
    refine ⟨1974041660296657444992493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2632055547062209926656657 1974041660296657444992493)
    ·
      refine ⟨740265622611246541872185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1974041660296657444992493 740265622611246541872185)
      ·
        refine ⟨555199216958434906404139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 740265622611246541872185 555199216958434906404139)
        ·
          refine ⟨832798825437652359606209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555199216958434906404139 832798825437652359606209)
          ·
            refine ⟨624599119078239269704657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832798825437652359606209 624599119078239269704657)
            ·
              refine ⟨468449339308679452278493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624599119078239269704657 468449339308679452278493)
              ·
                refine ⟨175668502240754794604435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468449339308679452278493 175668502240754794604435)
                ·
                  refine ⟨263502753361132191906653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175668502240754794604435 263502753361132191906653)
                  ·
                    refine ⟨98813532510424571964995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263502753361132191906653 98813532510424571964995)
                    ·
                      rfl

theorem cell22_288658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_288658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288658 prefixEnd_288658 := by exact prefixLift 288658
  have htrace : WordTrace (prefixWord ++ tailWord_288658) baseStart_288658 baseEnd_288658 := by
    simpa [prefixWord, tailWord_288658, baseEnd_288658] using wordTrace_append hprefix tailTrace_288658
  have hstable : (prefixWord ++ tailWord_288658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288658).length < 2 ^ (prefixWord ++ tailWord_288658).sum := by decide
  have hdescent : baseEnd_288658 < baseStart_288658 := by decide
  rcases family_descends (prefixWord ++ tailWord_288658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288671 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 5]
def baseStart_288671 : Nat := 118140960795 + 288671 * 2 ^ 59
def prefixEnd_288671 : Nat := 4983230072969 + 3 ^ 40 * 288671 * 2
def baseEnd_288671 : Nat := 32939327558698957129985

theorem tailTrace_288671 : CollatzResearch.WordTrace tailWord_288671 prefixEnd_288671 32939327558698957129985 := by
  unfold tailWord_288671
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528696337201742926849867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7019130891467828617899911 10528696337201742926849867)
  ·
    refine ⟨15793044505802614390274801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10528696337201742926849867 15793044505802614390274801)
    ·
      refine ⟨11844783379351960792706101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15793044505802614390274801 11844783379351960792706101)
      ·
        refine ⟨1110448441814246324316197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11844783379351960792706101 1110448441814246324316197)
        ·
          refine ⟨208209082840171185809287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1110448441814246324316197 208209082840171185809287)
          ·
            refine ⟨312313624260256778713931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208209082840171185809287 312313624260256778713931)
            ·
              refine ⟨468470436390385168070897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312313624260256778713931 468470436390385168070897)
              ·
                refine ⟨351352827292788876053173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468470436390385168070897 351352827292788876053173)
                ·
                  refine ⟨32939327558698957129985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351352827292788876053173 32939327558698957129985)
                  ·
                    rfl

theorem cell22_288671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 5].length) (baseStart_288671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288671 prefixEnd_288671 := by exact prefixLift 288671
  have htrace : WordTrace (prefixWord ++ tailWord_288671) baseStart_288671 baseEnd_288671 := by
    simpa [prefixWord, tailWord_288671, baseEnd_288671] using wordTrace_append hprefix tailTrace_288671
  have hstable : (prefixWord ++ tailWord_288671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288671).length < 2 ^ (prefixWord ++ tailWord_288671).sum := by decide
  have hdescent : baseEnd_288671 < baseStart_288671 := by decide
  rcases family_descends (prefixWord ++ tailWord_288671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288712 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_288712 : Nat := 118140960795 + 288712 * 2 ^ 59
def prefixEnd_288712 : Nat := 4983230072969 + 3 ^ 40 * 288712 * 2
def baseEnd_288712 : Nat := 98832017813986431114829

theorem tailTrace_288712 : CollatzResearch.WordTrace tailWord_288712 prefixEnd_288712 98832017813986431114829 := by
  unfold tailWord_288712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265095865026603464546195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7020127820035471286061593 5265095865026603464546195)
  ·
    refine ⟨7897643797539905196819293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5265095865026603464546195 7897643797539905196819293)
    ·
      refine ⟨2961616424077464448807235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7897643797539905196819293 2961616424077464448807235)
      ·
        refine ⟨4442424636116196673210853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961616424077464448807235 4442424636116196673210853)
        ·
          refine ⟨832954619271786876227035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4442424636116196673210853 832954619271786876227035)
          ·
            refine ⟨1249431928907680314340553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832954619271786876227035 1249431928907680314340553)
            ·
              refine ⟨937073946680760235755415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249431928907680314340553 937073946680760235755415)
              ·
                refine ⟨1405610920021140353633123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937073946680760235755415 1405610920021140353633123)
                ·
                  refine ⟨2108416380031710530449685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405610920021140353633123 2108416380031710530449685)
                  ·
                    refine ⟨98832017813986431114829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2108416380031710530449685 98832017813986431114829)
                    ·
                      rfl

theorem cell22_288712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_288712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288712 prefixEnd_288712 := by exact prefixLift 288712
  have htrace : WordTrace (prefixWord ++ tailWord_288712) baseStart_288712 baseEnd_288712 := by
    simpa [prefixWord, tailWord_288712, baseEnd_288712] using wordTrace_append hprefix tailTrace_288712
  have hstable : (prefixWord ++ tailWord_288712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288712).length < 2 ^ (prefixWord ++ tailWord_288712).sum := by decide
  have hdescent : baseEnd_288712 < baseStart_288712 := by decide
  rcases family_descends (prefixWord ++ tailWord_288712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288716 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_288716 : Nat := 118140960795 + 288716 * 2 ^ 59
def prefixEnd_288716 : Nat := 4983230072969 + 3 ^ 40 * 288716 * 2
def baseEnd_288716 : Nat := 32944462365243918004939

theorem tailTrace_288716 : CollatzResearch.WordTrace tailWord_288716 prefixEnd_288716 32944462365243918004939 := by
  unfold tailWord_288716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265168811019357806119001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7020225081359143741492001 5265168811019357806119001)
  ·
    refine ⟨3948876608264518354589251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5265168811019357806119001 3948876608264518354589251)
    ·
      refine ⟨5923314912396777531883877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948876608264518354589251 5923314912396777531883877)
      ·
        refine ⟨1110621546074395787228227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5923314912396777531883877 1110621546074395787228227)
        ·
          refine ⟨1665932319111593680842341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110621546074395787228227 1665932319111593680842341)
          ·
            refine ⟨312362309833423815157939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1665932319111593680842341 312362309833423815157939)
            ·
              refine ⟨468543464750135722736909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312362309833423815157939 468543464750135722736909)
              ·
                refine ⟨175703799281300896026341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468543464750135722736909 175703799281300896026341)
                ·
                  refine ⟨32944462365243918004939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175703799281300896026341 32944462365243918004939)
                  ·
                    rfl

theorem cell22_288716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_288716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288716 prefixEnd_288716 := by exact prefixLift 288716
  have htrace : WordTrace (prefixWord ++ tailWord_288716) baseStart_288716 baseEnd_288716 := by
    simpa [prefixWord, tailWord_288716, baseEnd_288716] using wordTrace_append hprefix tailTrace_288716
  have hstable : (prefixWord ++ tailWord_288716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288716).length < 2 ^ (prefixWord ++ tailWord_288716).sum := by decide
  have hdescent : baseEnd_288716 < baseStart_288716 := by decide
  rcases family_descends (prefixWord ++ tailWord_288716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288729 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_288729 : Nat := 118140960795 + 288729 * 2 ^ 59
def prefixEnd_288729 : Nat := 4983230072969 + 3 ^ 40 * 288729 * 2
def baseEnd_288729 : Nat := 98837837261404053439777

theorem tailTrace_288729 : CollatzResearch.WordTrace tailWord_288729 prefixEnd_288729 98837837261404053439777 := by
  unfold tailWord_288729
  simp only [CollatzResearch.WordTrace]
  refine ⟨10530811770991618832461241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7020541180661079221640827 10530811770991618832461241)
  ·
    refine ⟨7898108828243714124345931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10530811770991618832461241 7898108828243714124345931)
    ·
      refine ⟨11847163242365571186518897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7898108828243714124345931 11847163242365571186518897)
      ·
        refine ⟨8885372431774178389889173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11847163242365571186518897 8885372431774178389889173)
        ·
          refine ⟨416501832739414612026055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8885372431774178389889173 416501832739414612026055)
          ·
            refine ⟨624752749109121918039083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416501832739414612026055 624752749109121918039083)
            ·
              refine ⟨937129123663682877058625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624752749109121918039083 937129123663682877058625)
              ·
                refine ⟨702846842747762157793969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937129123663682877058625 702846842747762157793969)
                ·
                  refine ⟨527135132060821618345477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702846842747762157793969 527135132060821618345477)
                  ·
                    refine ⟨98837837261404053439777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527135132060821618345477 98837837261404053439777)
                    ·
                      rfl

theorem cell22_288729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_288729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288729 prefixEnd_288729 := by exact prefixLift 288729
  have htrace : WordTrace (prefixWord ++ tailWord_288729) baseStart_288729 baseEnd_288729 := by
    simpa [prefixWord, tailWord_288729, baseEnd_288729] using wordTrace_append hprefix tailTrace_288729
  have hstable : (prefixWord ++ tailWord_288729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288729).length < 2 ^ (prefixWord ++ tailWord_288729).sum := by decide
  have hdescent : baseEnd_288729 < baseStart_288729 := by decide
  rcases family_descends (prefixWord ++ tailWord_288729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288733 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 4]
def baseStart_288733 : Nat := 118140960795 + 288733 * 2 ^ 59
def prefixEnd_288733 : Nat := 4983230072969 + 3 ^ 40 * 288733 * 2
def baseEnd_288733 : Nat := 32946402181049792113255

theorem tailTrace_288733 : CollatzResearch.WordTrace tailWord_288733 prefixEnd_288733 32946402181049792113255 := by
  unfold tailWord_288733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10530957662977127515606853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7020638441984751677071235 10530957662977127515606853)
  ·
    refine ⟨1974554561808211409176285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10530957662977127515606853 1974554561808211409176285)
    ·
      refine ⟨740457960678079278441107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1974554561808211409176285 740457960678079278441107)
      ·
        refine ⟨1110686941017118917661661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740457960678079278441107 1110686941017118917661661)
        ·
          refine ⟨416507602881419594123123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1110686941017118917661661 416507602881419594123123)
          ·
            refine ⟨624761404322129391184685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416507602881419594123123 624761404322129391184685)
            ·
              refine ⟨234285526620798521694257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624761404322129391184685 234285526620798521694257)
              ·
                refine ⟨175714144965598891270693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234285526620798521694257 175714144965598891270693)
                ·
                  refine ⟨32946402181049792113255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175714144965598891270693 32946402181049792113255)
                  ·
                    rfl

theorem cell22_288733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_288733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288733 prefixEnd_288733 := by exact prefixLift 288733
  have htrace : WordTrace (prefixWord ++ tailWord_288733) baseStart_288733 baseEnd_288733 := by
    simpa [prefixWord, tailWord_288733, baseEnd_288733] using wordTrace_append hprefix tailTrace_288733
  have hstable : (prefixWord ++ tailWord_288733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288733).length < 2 ^ (prefixWord ++ tailWord_288733).sum := by decide
  have hdescent : baseEnd_288733 < baseStart_288733 := by decide
  rcases family_descends (prefixWord ++ tailWord_288733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288776 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_288776 : Nat := 118140960795 + 288776 * 2 ^ 59
def prefixEnd_288776 : Nat := 4983230072969 + 3 ^ 40 * 288776 * 2
def baseEnd_288776 : Nat := 98853926321911597514633

theorem tailTrace_288776 : CollatzResearch.WordTrace tailWord_288776 prefixEnd_288776 98853926321911597514633 := by
  unfold tailWord_288776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266263000910672929711091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7021684001214230572948121 5266263000910672929711091)
  ·
    refine ⟨7899394501366009394566637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5266263000910672929711091 7899394501366009394566637)
    ·
      refine ⟨2962272938012253522962489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7899394501366009394566637 2962272938012253522962489)
      ·
        refine ⟨2221704703509190142221867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962272938012253522962489 2221704703509190142221867)
        ·
          refine ⟨3332557055263785213332801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221704703509190142221867 3332557055263785213332801)
          ·
            refine ⟨2499417791447838909999601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3332557055263785213332801 2499417791447838909999601)
            ·
              refine ⟨1874563343585879182499701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499417791447838909999601 1874563343585879182499701)
              ·
                refine ⟨175740313461176173359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1874563343585879182499701 175740313461176173359347)
                ·
                  refine ⟨263610470191764260039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175740313461176173359347 263610470191764260039021)
                  ·
                    refine ⟨98853926321911597514633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263610470191764260039021 98853926321911597514633)
                    ·
                      rfl

theorem cell22_288776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_288776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288776 prefixEnd_288776 := by exact prefixLift 288776
  have htrace : WordTrace (prefixWord ++ tailWord_288776) baseStart_288776 baseEnd_288776 := by
    simpa [prefixWord, tailWord_288776, baseEnd_288776] using wordTrace_append hprefix tailTrace_288776
  have hstable : (prefixWord ++ tailWord_288776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288776).length < 2 ^ (prefixWord ++ tailWord_288776).sum := by decide
  have hdescent : baseEnd_288776 < baseStart_288776 := by decide
  rcases family_descends (prefixWord ++ tailWord_288776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288817 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 8]
def baseStart_288817 : Nat := 118140960795 + 288817 * 2 ^ 59
def prefixEnd_288817 : Nat := 4983230072969 + 3 ^ 40 * 288817 * 2
def baseEnd_288817 : Nat := 32955987153267052413169

theorem tailTrace_288817 : CollatzResearch.WordTrace tailWord_288817 prefixEnd_288817 32955987153267052413169 := by
  unfold tailWord_288817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534021394672809861664705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7022680929781873241109803 10534021394672809861664705)
  ·
    refine ⟨7900516046004607396248529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10534021394672809861664705 7900516046004607396248529)
    ·
      refine ⟨5925387034503455547186397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7900516046004607396248529 5925387034503455547186397)
      ·
        refine ⟨2222020137938795830194899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5925387034503455547186397 2222020137938795830194899)
        ·
          refine ⟨3333030206908193745292349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222020137938795830194899 3333030206908193745292349)
          ·
            refine ⟨1249886327590572654484631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3333030206908193745292349 1249886327590572654484631)
            ·
              refine ⟨1874829491385858981726947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249886327590572654484631 1874829491385858981726947)
              ·
                refine ⟨2812244237078788472590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874829491385858981726947 2812244237078788472590421)
                ·
                  refine ⟨32955987153267052413169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2812244237078788472590421 32955987153267052413169)
                  ·
                    rfl

theorem cell22_288817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_288817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288817 prefixEnd_288817 := by exact prefixLift 288817
  have htrace : WordTrace (prefixWord ++ tailWord_288817) baseStart_288817 baseEnd_288817 := by
    simpa [prefixWord, tailWord_288817, baseEnd_288817] using wordTrace_append hprefix tailTrace_288817
  have hstable : (prefixWord ++ tailWord_288817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288817).length < 2 ^ (prefixWord ++ tailWord_288817).sum := by decide
  have hdescent : baseEnd_288817 < baseStart_288817 := by decide
  rcases family_descends (prefixWord ++ tailWord_288817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288879 : List Nat := [1, 1, 2, 1, 3, 4, 4, 6]
def baseStart_288879 : Nat := 118140960795 + 288879 * 2 ^ 59
def prefixEnd_288879 : Nat := 4983230072969 + 3 ^ 40 * 288879 * 2
def baseEnd_288879 : Nat := 10987687258539295798813

theorem tailTrace_288879 : CollatzResearch.WordTrace tailWord_288879 prefixEnd_288879 10987687258539295798813 := by
  unfold tailWord_288879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536282720448194450421691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024188480298796300281127 10536282720448194450421691)
  ·
    refine ⟨15804424080672291675632537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536282720448194450421691 15804424080672291675632537)
    ·
      refine ⟨11853318060504218756724403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804424080672291675632537 11853318060504218756724403)
      ·
        refine ⟨17779977090756328135086605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853318060504218756724403 17779977090756328135086605)
        ·
          refine ⟨6667491409033623050657477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17779977090756328135086605 6667491409033623050657477)
          ·
            refine ⟨1250154639193804321998277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6667491409033623050657477 1250154639193804321998277)
            ·
              refine ⟨234403994848838310374677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1250154639193804321998277 234403994848838310374677)
              ·
                refine ⟨10987687258539295798813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234403994848838310374677 10987687258539295798813)
                ·
                  rfl

theorem cell22_288879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 6].length) (baseStart_288879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288879 prefixEnd_288879 := by exact prefixLift 288879
  have htrace : WordTrace (prefixWord ++ tailWord_288879) baseStart_288879 baseEnd_288879 := by
    simpa [prefixWord, tailWord_288879, baseEnd_288879] using wordTrace_append hprefix tailTrace_288879
  have hstable : (prefixWord ++ tailWord_288879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288879).length < 2 ^ (prefixWord ++ tailWord_288879).sum := by decide
  have hdescent : baseEnd_288879 < baseStart_288879 := by decide
  rcases family_descends (prefixWord ++ tailWord_288879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288958 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_288958 : Nat := 118140960795 + 288958 * 2 ^ 59
def prefixEnd_288958 : Nat := 4983230072969 + 3 ^ 40 * 288958 * 2
def baseEnd_288958 : Nat := 32972076213774596488025

theorem tailTrace_288958 : CollatzResearch.WordTrace tailWord_288958 prefixEnd_288958 32972076213774596488025 := by
  unfold tailWord_288958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317395510895248867818441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7026109391441327295031685 1317395510895248867818441)
  ·
    refine ⟨988046633171436650863831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1317395510895248867818441 988046633171436650863831)
    ·
      refine ⟨1482069949757154976295747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988046633171436650863831 1482069949757154976295747)
      ·
        refine ⟨2223104924635732464443621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482069949757154976295747 2223104924635732464443621)
        ·
          refine ⟨416832173369199837083179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2223104924635732464443621 416832173369199837083179)
          ·
            refine ⟨625248260053799755624769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416832173369199837083179 625248260053799755624769)
            ·
              refine ⟨468936195040349816718577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625248260053799755624769 468936195040349816718577)
              ·
                refine ⟨351702146280262362538933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468936195040349816718577 351702146280262362538933)
                ·
                  refine ⟨32972076213774596488025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351702146280262362538933 32972076213774596488025)
                  ·
                    rfl

theorem cell22_288958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_288958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_288958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_288958 prefixEnd_288958 := by exact prefixLift 288958
  have htrace : WordTrace (prefixWord ++ tailWord_288958) baseStart_288958 baseEnd_288958 := by
    simpa [prefixWord, tailWord_288958, baseEnd_288958] using wordTrace_append hprefix tailTrace_288958
  have hstable : (prefixWord ++ tailWord_288958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288958).length < 2 ^ (prefixWord ++ tailWord_288958).sum := by decide
  have hdescent : baseEnd_288958 < baseStart_288958 := by decide
  rcases family_descends (prefixWord ++ tailWord_288958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289018 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_289018 : Nat := 118140960795 + 289018 * 2 ^ 59
def prefixEnd_289018 : Nat := 4983230072969 + 3 ^ 40 * 289018 * 2
def baseEnd_289018 : Nat := 98936767867503632963891

theorem tailTrace_289018 : CollatzResearch.WordTrace tailWord_289018 prefixEnd_289018 98936767867503632963891 := by
  unfold tailWord_289018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635338116736155297432927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7027568311296414126487805 2635338116736155297432927)
  ·
    refine ⟨3953007175104232946149391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635338116736155297432927 3953007175104232946149391)
    ·
      refine ⟨5929510762656349419224087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953007175104232946149391 5929510762656349419224087)
      ·
        refine ⟨8894266143984524128836131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5929510762656349419224087 8894266143984524128836131)
        ·
          refine ⟨13341399215976786193254197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8894266143984524128836131 13341399215976786193254197)
          ·
            refine ⟨1250756176497823705617581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13341399215976786193254197 1250756176497823705617581)
            ·
              refine ⟨469033566186683889606593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250756176497823705617581 469033566186683889606593)
              ·
                refine ⟨351775174640012917204945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469033566186683889606593 351775174640012917204945)
                ·
                  refine ⟨263831380980009687903709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351775174640012917204945 263831380980009687903709)
                  ·
                    refine ⟨98936767867503632963891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263831380980009687903709 98936767867503632963891)
                    ·
                      rfl

theorem cell22_289018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_289018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289018 prefixEnd_289018 := by exact prefixLift 289018
  have htrace : WordTrace (prefixWord ++ tailWord_289018) baseStart_289018 baseEnd_289018 := by
    simpa [prefixWord, tailWord_289018, baseEnd_289018] using wordTrace_append hprefix tailTrace_289018
  have hstable : (prefixWord ++ tailWord_289018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289018).length < 2 ^ (prefixWord ++ tailWord_289018).sum := by decide
  have hdescent : baseEnd_289018 < baseStart_289018 := by decide
  rcases family_descends (prefixWord ++ tailWord_289018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289059 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 9]
def baseStart_289059 : Nat := 118140960795 + 289059 * 2 ^ 59
def prefixEnd_289059 : Nat := 4983230072969 + 3 ^ 40 * 289059 * 2
def baseEnd_289059 : Nat := 32983601001797730896255

theorem tailTrace_289059 : CollatzResearch.WordTrace tailWord_289059 prefixEnd_289059 32983601001797730896255 := by
  unfold tailWord_289059
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542847859796085191974231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7028565239864056794649487 10542847859796085191974231)
  ·
    refine ⟨15814271789694127787961347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542847859796085191974231 15814271789694127787961347)
    ·
      refine ⟨23721407684541191681942021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15814271789694127787961347 23721407684541191681942021)
      ·
        refine ⟨4447763940851473440364129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23721407684541191681942021 4447763940851473440364129)
        ·
          refine ⟨3335822955638605080273097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447763940851473440364129 3335822955638605080273097)
          ·
            refine ⟨2501867216728953810204823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3335822955638605080273097 2501867216728953810204823)
            ·
              refine ⟨3752800825093430715307235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501867216728953810204823 3752800825093430715307235)
              ·
                refine ⟨5629201237640146072960853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752800825093430715307235 5629201237640146072960853)
                ·
                  refine ⟨32983601001797730896255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5629201237640146072960853 32983601001797730896255)
                  ·
                    rfl

theorem cell22_289059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_289059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289059 prefixEnd_289059 := by exact prefixLift 289059
  have htrace : WordTrace (prefixWord ++ tailWord_289059) baseStart_289059 baseEnd_289059 := by
    simpa [prefixWord, tailWord_289059, baseEnd_289059] using wordTrace_append hprefix tailTrace_289059
  have hstable : (prefixWord ++ tailWord_289059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289059).length < 2 ^ (prefixWord ++ tailWord_289059).sum := by decide
  have hdescent : baseEnd_289059 < baseStart_289059 := by decide
  rcases family_descends (prefixWord ++ tailWord_289059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289153 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_289153 : Nat := 118140960795 + 289153 * 2 ^ 59
def prefixEnd_289153 : Nat := 4983230072969 + 3 ^ 40 * 289153 * 2
def baseEnd_289153 : Nat := 98982981126408280838477

theorem tailTrace_289153 : CollatzResearch.WordTrace tailWord_289153 prefixEnd_289153 98982981126408280838477 := by
  unfold tailWord_289153
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546276321455539245896113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7030850880970359497264075 10546276321455539245896113)
  ·
    refine ⟨7909707241091654434422085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10546276321455539245896113 7909707241091654434422085)
    ·
      refine ⟨1483070107704685206454141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7909707241091654434422085 1483070107704685206454141)
      ·
        refine ⟨556151290389256952420303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1483070107704685206454141 556151290389256952420303)
        ·
          refine ⟨834226935583885428630455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556151290389256952420303 834226935583885428630455)
          ·
            refine ⟨1251340403375828142945683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834226935583885428630455 1251340403375828142945683)
            ·
              refine ⟨1877010605063742214418525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251340403375828142945683 1877010605063742214418525)
              ·
                refine ⟨703878976898903330406947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877010605063742214418525 703878976898903330406947)
                ·
                  refine ⟨1055818465348354995610421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703878976898903330406947 1055818465348354995610421)
                  ·
                    refine ⟨98982981126408280838477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1055818465348354995610421 98982981126408280838477)
                    ·
                      rfl

theorem cell22_289153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_289153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289153 prefixEnd_289153 := by exact prefixLift 289153
  have htrace : WordTrace (prefixWord ++ tailWord_289153) baseStart_289153 baseEnd_289153 := by
    simpa [prefixWord, tailWord_289153, baseEnd_289153] using wordTrace_append hprefix tailTrace_289153
  have hstable : (prefixWord ++ tailWord_289153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289153).length < 2 ^ (prefixWord ++ tailWord_289153).sum := by decide
  have hdescent : baseEnd_289153 < baseStart_289153 := by decide
  rcases family_descends (prefixWord ++ tailWord_289153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289172 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_289172 : Nat := 118140960795 + 289172 * 2 ^ 59
def prefixEnd_289172 : Nat := 4983230072969 + 3 ^ 40 * 289172 * 2
def baseEnd_289172 : Nat := 32996495071566188204473

theorem tailTrace_289172 : CollatzResearch.WordTrace tailWord_289172 prefixEnd_289172 32996495071566188204473 := by
  unfold tailWord_289172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273484654193352745418885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7031312872257803660558513 5273484654193352745418885)
  ·
    refine ⟨988778372661253639766041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5273484654193352745418885 988778372661253639766041)
    ·
      refine ⟨741583779495940229824531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988778372661253639766041 741583779495940229824531)
      ·
        refine ⟨1112375669243910344736797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741583779495940229824531 1112375669243910344736797)
        ·
          refine ⟨417140875966466379276299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1112375669243910344736797 417140875966466379276299)
          ·
            refine ⟨625711313949699568914449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417140875966466379276299 625711313949699568914449)
            ·
              refine ⟨469283485462274676685837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625711313949699568914449 469283485462274676685837)
              ·
                refine ⟨175981307048353003757189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469283485462274676685837 175981307048353003757189)
                ·
                  refine ⟨32996495071566188204473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175981307048353003757189 32996495071566188204473)
                  ·
                    rfl

theorem cell22_289172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_289172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289172 prefixEnd_289172 := by exact prefixLift 289172
  have htrace : WordTrace (prefixWord ++ tailWord_289172) baseStart_289172 baseEnd_289172 := by
    simpa [prefixWord, tailWord_289172, baseEnd_289172] using wordTrace_append hprefix tailTrace_289172
  have hstable : (prefixWord ++ tailWord_289172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289172).length < 2 ^ (prefixWord ++ tailWord_289172).sum := by decide
  have hdescent : baseEnd_289172 < baseStart_289172 := by decide
  rcases family_descends (prefixWord ++ tailWord_289172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289204 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_289204 : Nat := 118140960795 + 289204 * 2 ^ 59
def prefixEnd_289204 : Nat := 4983230072969 + 3 ^ 40 * 289204 * 2
def baseEnd_289204 : Nat := 99000439468661147813321

theorem tailTrace_289204 : CollatzResearch.WordTrace tailWord_289204 prefixEnd_289204 99000439468661147813321 := by
  unfold tailWord_289204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274068222135387478001333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7032090962847183304001777 5274068222135387478001333)
  ·
    refine ⟨494443895825192576062625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5274068222135387478001333 494443895825192576062625)
    ·
      refine ⟨370832921868894432046969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494443895825192576062625 370832921868894432046969)
      ·
        refine ⟨278124691401670824035227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370832921868894432046969 278124691401670824035227)
        ·
          refine ⟨417187037102506236052841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278124691401670824035227 417187037102506236052841)
          ·
            refine ⟨312890277826879677039631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417187037102506236052841 312890277826879677039631)
            ·
              refine ⟨469335416740319515559447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312890277826879677039631 469335416740319515559447)
              ·
                refine ⟨704003125110479273339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469335416740319515559447 704003125110479273339171)
                ·
                  refine ⟨1056004687665718910008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704003125110479273339171 1056004687665718910008757)
                  ·
                    refine ⟨99000439468661147813321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1056004687665718910008757 99000439468661147813321)
                    ·
                      rfl

theorem cell22_289204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_289204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289204 prefixEnd_289204 := by exact prefixLift 289204
  have htrace : WordTrace (prefixWord ++ tailWord_289204) baseStart_289204 baseEnd_289204 := by
    simpa [prefixWord, tailWord_289204, baseEnd_289204] using wordTrace_append hprefix tailTrace_289204
  have hstable : (prefixWord ++ tailWord_289204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289204).length < 2 ^ (prefixWord ++ tailWord_289204).sum := by decide
  have hdescent : baseEnd_289204 < baseStart_289204 := by decide
  rcases family_descends (prefixWord ++ tailWord_289204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289217 : List Nat := [1, 2, 7, 1, 1, 1, 1, 8]
def baseStart_289217 : Nat := 118140960795 + 289217 * 2 ^ 59
def prefixEnd_289217 : Nat := 4983230072969 + 3 ^ 40 * 289217 * 2
def baseEnd_289217 : Nat := 11000543292703716359809

theorem tailTrace_289217 : CollatzResearch.WordTrace tailWord_289217 prefixEnd_289217 11000543292703716359809 := by
  unfold tailWord_289217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548610593223678176225905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7032407062149118784150603 10548610593223678176225905)
  ·
    refine ⟨7911457944917758632169429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10548610593223678176225905 7911457944917758632169429)
    ·
      refine ⟨185424795584009967941471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7911457944917758632169429 185424795584009967941471)
      ·
        refine ⟨278137193376014951912207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185424795584009967941471 278137193376014951912207)
        ·
          refine ⟨417205790064022427868311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278137193376014951912207 417205790064022427868311)
          ·
            refine ⟨625808685096033641802467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417205790064022427868311 625808685096033641802467)
            ·
              refine ⟨938713027644050462703701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625808685096033641802467 938713027644050462703701)
              ·
                refine ⟨11000543292703716359809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 938713027644050462703701 11000543292703716359809)
                ·
                  rfl

theorem cell22_289217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 8].length) (baseStart_289217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289217 prefixEnd_289217 := by exact prefixLift 289217
  have htrace : WordTrace (prefixWord ++ tailWord_289217) baseStart_289217 baseEnd_289217 := by
    simpa [prefixWord, tailWord_289217, baseEnd_289217] using wordTrace_append hprefix tailTrace_289217
  have hstable : (prefixWord ++ tailWord_289217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289217).length < 2 ^ (prefixWord ++ tailWord_289217).sum := by decide
  have hdescent : baseEnd_289217 < baseStart_289217 := by decide
  rcases family_descends (prefixWord ++ tailWord_289217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289262 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_289262 : Nat := 118140960795 + 289262 * 2 ^ 59
def prefixEnd_289262 : Nat := 4983230072969 + 3 ^ 40 * 289262 * 2
def baseEnd_289262 : Nat := 33006764684656109954381

theorem tailTrace_289262 : CollatzResearch.WordTrace tailWord_289262 prefixEnd_289262 33006764684656109954381 := by
  unfold tailWord_289262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318781484757581357701755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7033501252040433907742693 1318781484757581357701755)
  ·
    refine ⟨1978172227136372036552633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318781484757581357701755 1978172227136372036552633)
    ·
      refine ⟨1483629170352279027414475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1978172227136372036552633 1483629170352279027414475)
      ·
        refine ⟨2225443755528418541121713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483629170352279027414475 2225443755528418541121713)
        ·
          refine ⟨1669082816646313905841285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225443755528418541121713 1669082816646313905841285)
          ·
            refine ⟨312953028121183857345241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1669082816646313905841285 312953028121183857345241)
            ·
              refine ⟨234714771090887893008931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312953028121183857345241 234714771090887893008931)
              ·
                refine ⟨352072156636331839513397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234714771090887893008931 352072156636331839513397)
                ·
                  refine ⟨33006764684656109954381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352072156636331839513397 33006764684656109954381)
                  ·
                    rfl

theorem cell22_289262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_289262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289262 prefixEnd_289262 := by exact prefixLift 289262
  have htrace : WordTrace (prefixWord ++ tailWord_289262) baseStart_289262 baseEnd_289262 := by
    simpa [prefixWord, tailWord_289262, baseEnd_289262] using wordTrace_append hprefix tailTrace_289262
  have hstable : (prefixWord ++ tailWord_289262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289262).length < 2 ^ (prefixWord ++ tailWord_289262).sum := by decide
  have hdescent : baseEnd_289262 < baseStart_289262 := by decide
  rcases family_descends (prefixWord ++ tailWord_289262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289290 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_289290 : Nat := 118140960795 + 289290 * 2 ^ 59
def prefixEnd_289290 : Nat := 4983230072969 + 3 ^ 40 * 289290 * 2
def baseEnd_289290 : Nat := 33009959675395196721019

theorem tailTrace_289290 : CollatzResearch.WordTrace tailWord_289290 prefixEnd_289290 33009959675395196721019 := by
  unfold tailWord_289290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637818280489802910908331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7034182081306141095755549 2637818280489802910908331)
  ·
    refine ⟨3956727420734704366362497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2637818280489802910908331 3956727420734704366362497)
    ·
      refine ⟨2967545565551028274771873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3956727420734704366362497 2967545565551028274771873)
      ·
        refine ⟨2225659174163271206078905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2967545565551028274771873 2225659174163271206078905)
        ·
          refine ⟨1669244380622453404559179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225659174163271206078905 1669244380622453404559179)
          ·
            refine ⟨2503866570933680106838769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669244380622453404559179 2503866570933680106838769)
            ·
              refine ⟨1877899928200260080129077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503866570933680106838769 1877899928200260080129077)
              ·
                refine ⟨176053118268774382512101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1877899928200260080129077 176053118268774382512101)
                ·
                  refine ⟨33009959675395196721019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176053118268774382512101 33009959675395196721019)
                  ·
                    rfl

theorem cell22_289290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_289290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289290 prefixEnd_289290 := by exact prefixLift 289290
  have htrace : WordTrace (prefixWord ++ tailWord_289290) baseStart_289290 baseEnd_289290 := by
    simpa [prefixWord, tailWord_289290, baseEnd_289290] using wordTrace_append hprefix tailTrace_289290
  have hstable : (prefixWord ++ tailWord_289290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289290).length < 2 ^ (prefixWord ++ tailWord_289290).sum := by decide
  have hdescent : baseEnd_289290 < baseStart_289290 := by decide
  rcases family_descends (prefixWord ++ tailWord_289290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289292 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_289292 : Nat := 118140960795 + 289292 * 2 ^ 59
def prefixEnd_289292 : Nat := 4983230072969 + 3 ^ 40 * 289292 * 2
def baseEnd_289292 : Nat := 99030563667058251613051

theorem tailTrace_289292 : CollatzResearch.WordTrace tailWord_289292 prefixEnd_289292 99030563667058251613051 := by
  unfold tailWord_289292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275673033975982992603065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7034230711967977323470753 5275673033975982992603065)
  ·
    refine ⟨3956754775481987244452299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5275673033975982992603065 3956754775481987244452299)
    ·
      refine ⟨5935132163222980866678449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956754775481987244452299 5935132163222980866678449)
      ·
        refine ⟨4451349122417235650008837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5935132163222980866678449 4451349122417235650008837)
        ·
          refine ⟨834627960453231684376657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4451349122417235650008837 834627960453231684376657)
          ·
            refine ⟨625970970339923763282493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834627960453231684376657 625970970339923763282493)
            ·
              refine ⟨234739113877471411230935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625970970339923763282493 234739113877471411230935)
              ·
                refine ⟨352108670816207116846403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234739113877471411230935 352108670816207116846403)
                ·
                  refine ⟨528163006224310675269605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352108670816207116846403 528163006224310675269605)
                  ·
                    refine ⟨99030563667058251613051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528163006224310675269605 99030563667058251613051)
                    ·
                      rfl

theorem cell22_289292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_289292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289292 prefixEnd_289292 := by exact prefixLift 289292
  have htrace : WordTrace (prefixWord ++ tailWord_289292) baseStart_289292 baseEnd_289292 := by
    simpa [prefixWord, tailWord_289292, baseEnd_289292] using wordTrace_append hprefix tailTrace_289292
  have hstable : (prefixWord ++ tailWord_289292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289292).length < 2 ^ (prefixWord ++ tailWord_289292).sum := by decide
  have hdescent : baseEnd_289292 < baseStart_289292 := by decide
  rcases family_descends (prefixWord ++ tailWord_289292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289322 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_289322 : Nat := 118140960795 + 289322 * 2 ^ 59
def prefixEnd_289322 : Nat := 4983230072969 + 3 ^ 40 * 289322 * 2
def baseEnd_289322 : Nat := 99040833280148173362959

theorem tailTrace_289322 : CollatzResearch.WordTrace tailWord_289322 prefixEnd_289322 99040833280148173362959 := by
  unfold tailWord_289322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638110064460820277199555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7034960171895520739198813 2638110064460820277199555)
  ·
    refine ⟨3957165096691230415799333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2638110064460820277199555 3957165096691230415799333)
    ·
      refine ⟨741968455629605702962375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3957165096691230415799333 741968455629605702962375)
      ·
        refine ⟨1112952683444408554443563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741968455629605702962375 1112952683444408554443563)
        ·
          refine ⟨1669429025166612831665345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112952683444408554443563 1669429025166612831665345)
          ·
            refine ⟨1252071768874959623749009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669429025166612831665345 1252071768874959623749009)
            ·
              refine ⟨939053826656219717811757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252071768874959623749009 939053826656219717811757)
              ·
                refine ⟨352145184996082394179409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939053826656219717811757 352145184996082394179409)
                ·
                  refine ⟨264108888747061795634557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352145184996082394179409 264108888747061795634557)
                  ·
                    refine ⟨99040833280148173362959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264108888747061795634557 99040833280148173362959)
                    ·
                      rfl

theorem cell22_289322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_289322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289322 prefixEnd_289322 := by exact prefixLift 289322
  have htrace : WordTrace (prefixWord ++ tailWord_289322) baseStart_289322 baseEnd_289322 := by
    simpa [prefixWord, tailWord_289322, baseEnd_289322] using wordTrace_append hprefix tailTrace_289322
  have hstable : (prefixWord ++ tailWord_289322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289322).length < 2 ^ (prefixWord ++ tailWord_289322).sum := by decide
  have hdescent : baseEnd_289322 < baseStart_289322 := by decide
  rcases family_descends (prefixWord ++ tailWord_289322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289367 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 1, 3]
def baseStart_289367 : Nat := 118140960795 + 289367 * 2 ^ 59
def prefixEnd_289367 : Nat := 4983230072969 + 3 ^ 40 * 289367 * 2
def baseEnd_289367 : Nat := 99056237699783055987821

theorem tailTrace_289367 : CollatzResearch.WordTrace tailWord_289367 prefixEnd_289367 99056237699783055987821 := by
  unfold tailWord_289367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554081542680253794186355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7036054361786835862790903 10554081542680253794186355)
  ·
    refine ⟨15831122314020380691279533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554081542680253794186355 15831122314020380691279533)
    ·
      refine ⟨5936670867757642759229825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15831122314020380691279533 5936670867757642759229825)
      ·
        refine ⟨4452503150818232069422369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5936670867757642759229825 4452503150818232069422369)
        ·
          refine ⟨3339377363113674052066777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4452503150818232069422369 3339377363113674052066777)
          ·
            refine ⟨2504533022335255539050083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3339377363113674052066777 2504533022335255539050083)
            ·
              refine ⟨3756799533502883308575125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504533022335255539050083 3756799533502883308575125)
              ·
                refine ⟨176099978132947655089459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3756799533502883308575125 176099978132947655089459)
                ·
                  refine ⟨264149967199421482634189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176099978132947655089459 264149967199421482634189)
                  ·
                    refine ⟨99056237699783055987821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264149967199421482634189 99056237699783055987821)
                    ·
                      rfl

theorem cell22_289367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_289367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289367 prefixEnd_289367 := by exact prefixLift 289367
  have htrace : WordTrace (prefixWord ++ tailWord_289367) baseStart_289367 baseEnd_289367 := by
    simpa [prefixWord, tailWord_289367, baseEnd_289367] using wordTrace_append hprefix tailTrace_289367
  have hstable : (prefixWord ++ tailWord_289367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289367).length < 2 ^ (prefixWord ++ tailWord_289367).sum := by decide
  have hdescent : baseEnd_289367 < baseStart_289367 := by decide
  rcases family_descends (prefixWord ++ tailWord_289367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_289423 : Nat := 118140960795 + 289423 * 2 ^ 59
def prefixEnd_289423 : Nat := 4983230072969 + 3 ^ 40 * 289423 * 2
def baseEnd_289423 : Nat := 99075407644217576587649

theorem tailTrace_289423 : CollatzResearch.WordTrace tailWord_289423 prefixEnd_289423 99075407644217576587649 := by
  unfold tailWord_289423
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556124030477375358224923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7037416020318250238816615 10556124030477375358224923)
  ·
    refine ⟨15834186045716063037337385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556124030477375358224923 15834186045716063037337385)
    ·
      refine ⟨11875639534287047278003039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15834186045716063037337385 11875639534287047278003039)
      ·
        refine ⟨17813459301430570917004559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875639534287047278003039 17813459301430570917004559)
        ·
          refine ⟨26720188952145856375506839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17813459301430570917004559 26720188952145856375506839)
          ·
            refine ⟨40080283428218784563260259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26720188952145856375506839 40080283428218784563260259)
            ·
              refine ⟨60120425142328176844890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40080283428218784563260259 60120425142328176844890389)
              ·
                refine ⟨2818144928546633289604237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60120425142328176844890389 2818144928546633289604237)
                ·
                  refine ⟨1056804348204987483601589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2818144928546633289604237 1056804348204987483601589)
                  ·
                    refine ⟨99075407644217576587649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1056804348204987483601589 99075407644217576587649)
                    ·
                      rfl

theorem cell22_289423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_289423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289423 prefixEnd_289423 := by exact prefixLift 289423
  have htrace : WordTrace (prefixWord ++ tailWord_289423) baseStart_289423 baseEnd_289423 := by
    simpa [prefixWord, tailWord_289423, baseEnd_289423] using wordTrace_append hprefix tailTrace_289423
  have hstable : (prefixWord ++ tailWord_289423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289423).length < 2 ^ (prefixWord ++ tailWord_289423).sum := by decide
  have hdescent : baseEnd_289423 < baseStart_289423 := by decide
  rcases family_descends (prefixWord ++ tailWord_289423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289455 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_289455 : Nat := 118140960795 + 289455 * 2 ^ 59
def prefixEnd_289455 : Nat := 4983230072969 + 3 ^ 40 * 289455 * 2
def baseEnd_289455 : Nat := 99086361898180159787551

theorem tailTrace_289455 : CollatzResearch.WordTrace tailWord_289455 prefixEnd_289455 99086361898180159787551 := by
  unfold tailWord_289455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557291166361444823389819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7038194110907629882259879 10557291166361444823389819)
  ·
    refine ⟨15835936749542167235084729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10557291166361444823389819 15835936749542167235084729)
    ·
      refine ⟨11876952562156625426313547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15835936749542167235084729 11876952562156625426313547)
      ·
        refine ⟨17815428843234938139470321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11876952562156625426313547 17815428843234938139470321)
        ·
          refine ⟨13361571632426203604602741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17815428843234938139470321 13361571632426203604602741)
          ·
            refine ⟨1252647340539956587931507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13361571632426203604602741 1252647340539956587931507)
            ·
              refine ⟨1878971010809934881897261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252647340539956587931507 1878971010809934881897261)
              ·
                refine ⟨704614129053725580711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878971010809934881897261 704614129053725580711473)
                ·
                  refine ⟨528460596790294185533605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704614129053725580711473 528460596790294185533605)
                  ·
                    refine ⟨99086361898180159787551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528460596790294185533605 99086361898180159787551)
                    ·
                      rfl

theorem cell22_289455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_289455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289455 prefixEnd_289455 := by exact prefixLift 289455
  have htrace : WordTrace (prefixWord ++ tailWord_289455) baseStart_289455 baseEnd_289455 := by
    simpa [prefixWord, tailWord_289455, baseEnd_289455] using wordTrace_append hprefix tailTrace_289455
  have hstable : (prefixWord ++ tailWord_289455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289455).length < 2 ^ (prefixWord ++ tailWord_289455).sum := by decide
  have hdescent : baseEnd_289455 < baseStart_289455 := by decide
  rcases family_descends (prefixWord ++ tailWord_289455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289476 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_289476 : Nat := 118140960795 + 289476 * 2 ^ 59
def prefixEnd_289476 : Nat := 4983230072969 + 3 ^ 40 * 289476 * 2
def baseEnd_289476 : Nat := 33031183542447701670829

theorem tailTrace_289476 : CollatzResearch.WordTrace tailWord_289476 prefixEnd_289476 33031183542447701670829 := by
  unfold tailWord_289476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279028549642682704952141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7038704732856910273269521 5279028549642682704952141)
  ·
    refine ⟨1979635706116006014357053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5279028549642682704952141 1979635706116006014357053)
    ·
      refine ⟨742363389793502255383895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1979635706116006014357053 742363389793502255383895)
      ·
        refine ⟨1113545084690253383075843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742363389793502255383895 1113545084690253383075843)
        ·
          refine ⟨1670317627035380074613765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113545084690253383075843 1670317627035380074613765)
          ·
            refine ⟨313184555069133763990081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1670317627035380074613765 313184555069133763990081)
            ·
              refine ⟨234888416301850322992561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313184555069133763990081 234888416301850322992561)
              ·
                refine ⟨176166312226387742244421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234888416301850322992561 176166312226387742244421)
                ·
                  refine ⟨33031183542447701670829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176166312226387742244421 33031183542447701670829)
                  ·
                    rfl

theorem cell22_289476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_289476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289476 prefixEnd_289476 := by exact prefixLift 289476
  have htrace : WordTrace (prefixWord ++ tailWord_289476) baseStart_289476 baseEnd_289476 := by
    simpa [prefixWord, tailWord_289476, baseEnd_289476] using wordTrace_append hprefix tailTrace_289476
  have hstable : (prefixWord ++ tailWord_289476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289476).length < 2 ^ (prefixWord ++ tailWord_289476).sum := by decide
  have hdescent : baseEnd_289476 < baseStart_289476 := by decide
  rcases family_descends (prefixWord ++ tailWord_289476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289519 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 1, 3]
def baseStart_289519 : Nat := 118140960795 + 289519 * 2 ^ 59
def prefixEnd_289519 : Nat := 4983230072969 + 3 ^ 40 * 289519 * 2
def baseEnd_289519 : Nat := 99108270406105326187355

theorem tailTrace_289519 : CollatzResearch.WordTrace tailWord_289519 prefixEnd_289519 99108270406105326187355 := by
  unfold tailWord_289519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559625438129583753719611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7039750292086389169146407 10559625438129583753719611)
  ·
    refine ⟨15839438157194375630579417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10559625438129583753719611 15839438157194375630579417)
    ·
      refine ⟨11879578617895781722934563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15839438157194375630579417 11879578617895781722934563)
      ·
        refine ⟨17819367926843672584401845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879578617895781722934563 17819367926843672584401845)
        ·
          refine ⟨1670565743141594304787673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17819367926843672584401845 1670565743141594304787673)
          ·
            refine ⟨1252924307356195728590755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1670565743141594304787673 1252924307356195728590755)
            ·
              refine ⟨1879386461034293592886133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252924307356195728590755 1879386461034293592886133)
              ·
                refine ⟨176192480721965024333075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1879386461034293592886133 176192480721965024333075)
                ·
                  refine ⟨264288721082947536499613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176192480721965024333075 264288721082947536499613)
                  ·
                    refine ⟨99108270406105326187355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264288721082947536499613 99108270406105326187355)
                    ·
                      rfl

theorem cell22_289519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_289519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289519 prefixEnd_289519 := by exact prefixLift 289519
  have htrace : WordTrace (prefixWord ++ tailWord_289519) baseStart_289519 baseEnd_289519 := by
    simpa [prefixWord, tailWord_289519, baseEnd_289519] using wordTrace_append hprefix tailTrace_289519
  have hstable : (prefixWord ++ tailWord_289519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289519).length < 2 ^ (prefixWord ++ tailWord_289519).sum := by decide
  have hdescent : baseEnd_289519 < baseStart_289519 := by decide
  rcases family_descends (prefixWord ++ tailWord_289519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289525 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_289525 : Nat := 118140960795 + 289525 * 2 ^ 59
def prefixEnd_289525 : Nat := 4983230072969 + 3 ^ 40 * 289525 * 2
def baseEnd_289525 : Nat := 99110324328723310537337

theorem tailTrace_289525 : CollatzResearch.WordTrace tailWord_289525 prefixEnd_289525 99110324328723310537337 := by
  unfold tailWord_289525
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559844276107846778438029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7039896184071897852292019 10559844276107846778438029)
  ·
    refine ⟨3959941603540442541914261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10559844276107846778438029 3959941603540442541914261)
    ·
      refine ⟨185622262665958244152231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3959941603540442541914261 185622262665958244152231)
      ·
        refine ⟨278433393998937366228347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185622262665958244152231 278433393998937366228347)
        ·
          refine ⟨417650090998406049342521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278433393998937366228347 417650090998406049342521)
          ·
            refine ⟨313237568248804537006891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417650090998406049342521 313237568248804537006891)
            ·
              refine ⟨469856352373206805510337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313237568248804537006891 469856352373206805510337)
              ·
                refine ⟨352392264279905104132753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469856352373206805510337 352392264279905104132753)
                ·
                  refine ⟨264294198209928828099565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352392264279905104132753 264294198209928828099565)
                  ·
                    refine ⟨99110324328723310537337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264294198209928828099565 99110324328723310537337)
                    ·
                      rfl

theorem cell22_289525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_289525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289525 prefixEnd_289525 := by exact prefixLift 289525
  have htrace : WordTrace (prefixWord ++ tailWord_289525) baseStart_289525 baseEnd_289525 := by
    simpa [prefixWord, tailWord_289525, baseEnd_289525] using wordTrace_append hprefix tailTrace_289525
  have hstable : (prefixWord ++ tailWord_289525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289525).length < 2 ^ (prefixWord ++ tailWord_289525).sum := by decide
  have hdescent : baseEnd_289525 < baseStart_289525 := by decide
  rcases family_descends (prefixWord ++ tailWord_289525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289530 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_289530 : Nat := 118140960795 + 289530 * 2 ^ 59
def prefixEnd_289530 : Nat := 4983230072969 + 3 ^ 40 * 289530 * 2
def baseEnd_289530 : Nat := 99112035930904964162321

theorem tailTrace_289530 : CollatzResearch.WordTrace tailWord_289530 prefixEnd_289530 99112035930904964162321 := by
  unfold tailWord_289530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640006660272433158092511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7040017760726488421580029 2640006660272433158092511)
  ·
    refine ⟨3960009990408649737138767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640006660272433158092511 3960009990408649737138767)
    ·
      refine ⟨5940014985612974605708151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960009990408649737138767 5940014985612974605708151)
      ·
        refine ⟨8910022478419461908562227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940014985612974605708151 8910022478419461908562227)
        ·
          refine ⟨13365033717629192862843341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8910022478419461908562227 13365033717629192862843341)
          ·
            refine ⟨5011887644110947323566253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13365033717629192862843341 5011887644110947323566253)
            ·
              refine ⟨1879457866541605246337345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5011887644110947323566253 1879457866541605246337345)
              ·
                refine ⟨1409593399906203934753009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879457866541605246337345 1409593399906203934753009)
                ·
                  refine ⟨1057195049929652951064757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409593399906203934753009 1057195049929652951064757)
                  ·
                    refine ⟨99112035930904964162321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1057195049929652951064757 99112035930904964162321)
                    ·
                      rfl

theorem cell22_289530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_289530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289530 prefixEnd_289530 := by exact prefixLift 289530
  have htrace : WordTrace (prefixWord ++ tailWord_289530) baseStart_289530 baseEnd_289530 := by
    simpa [prefixWord, tailWord_289530, baseEnd_289530] using wordTrace_append hprefix tailTrace_289530
  have hstable : (prefixWord ++ tailWord_289530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289530).length < 2 ^ (prefixWord ++ tailWord_289530).sum := by decide
  have hdescent : baseEnd_289530 < baseStart_289530 := by decide
  rcases family_descends (prefixWord ++ tailWord_289530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289532 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_289532 : Nat := 118140960795 + 289532 * 2 ^ 59
def prefixEnd_289532 : Nat := 4983230072969 + 3 ^ 40 * 289532 * 2
def baseEnd_289532 : Nat := 33037573523925875204105

theorem tailTrace_289532 : CollatzResearch.WordTrace tailWord_289532 prefixEnd_289532 33037573523925875204105 := by
  unfold tailWord_289532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280049793541243486971425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7040066391388324649295233 5280049793541243486971425)
  ·
    refine ⟨3960037345155932615228569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280049793541243486971425 3960037345155932615228569)
    ·
      refine ⟨2970028008866949461421427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960037345155932615228569 2970028008866949461421427)
      ·
        refine ⟨4455042013300424192132141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970028008866949461421427 4455042013300424192132141)
        ·
          refine ⟨1670640754987659072049553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4455042013300424192132141 1670640754987659072049553)
          ·
            refine ⟨1252980566240744304037165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1670640754987659072049553 1252980566240744304037165)
            ·
              refine ⟨469867712340279114013937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1252980566240744304037165 469867712340279114013937)
              ·
                refine ⟨352400784255209335510453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469867712340279114013937 352400784255209335510453)
                ·
                  refine ⟨33037573523925875204105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352400784255209335510453 33037573523925875204105)
                  ·
                    rfl

theorem cell22_289532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_289532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289532 prefixEnd_289532 := by exact prefixLift 289532
  have htrace : WordTrace (prefixWord ++ tailWord_289532) baseStart_289532 baseEnd_289532 := by
    simpa [prefixWord, tailWord_289532, baseEnd_289532] using wordTrace_append hprefix tailTrace_289532
  have hstable : (prefixWord ++ tailWord_289532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289532).length < 2 ^ (prefixWord ++ tailWord_289532).sum := by decide
  have hdescent : baseEnd_289532 < baseStart_289532 := by decide
  rcases family_descends (prefixWord ++ tailWord_289532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289545 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_289545 : Nat := 118140960795 + 289545 * 2 ^ 59
def prefixEnd_289545 : Nat := 4983230072969 + 3 ^ 40 * 289545 * 2
def baseEnd_289545 : Nat := 99117170737449925037275

theorem tailTrace_289545 : CollatzResearch.WordTrace tailWord_289545 prefixEnd_289545 99117170737449925037275 := by
  unfold tailWord_289545
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560573736035390194166089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7040382490690260129444059 10560573736035390194166089)
  ·
    refine ⟨7920430302026542645624567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10560573736035390194166089 7920430302026542645624567)
    ·
      refine ⟨11880645453039813968436851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7920430302026542645624567 11880645453039813968436851)
      ·
        refine ⟨17820968179559720952655277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11880645453039813968436851 17820968179559720952655277)
        ·
          refine ⟨6682863067334895357245729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17820968179559720952655277 6682863067334895357245729)
          ·
            refine ⟨5012147300501171517934297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682863067334895357245729 5012147300501171517934297)
            ·
              refine ⟨3759110475375878638450723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012147300501171517934297 3759110475375878638450723)
              ·
                refine ⟨5638665713063817957676085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759110475375878638450723 5638665713063817957676085)
                ·
                  refine ⟨528624910599732933532133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5638665713063817957676085 528624910599732933532133)
                  ·
                    refine ⟨99117170737449925037275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528624910599732933532133 99117170737449925037275)
                    ·
                      rfl

theorem cell22_289545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_289545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289545 prefixEnd_289545 := by exact prefixLift 289545
  have htrace : WordTrace (prefixWord ++ tailWord_289545) baseStart_289545 baseEnd_289545 := by
    simpa [prefixWord, tailWord_289545, baseEnd_289545] using wordTrace_append hprefix tailTrace_289545
  have hstable : (prefixWord ++ tailWord_289545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289545).length < 2 ^ (prefixWord ++ tailWord_289545).sum := by decide
  have hdescent : baseEnd_289545 < baseStart_289545 := by decide
  rcases family_descends (prefixWord ++ tailWord_289545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289592 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_289592 : Nat := 118140960795 + 289592 * 2 ^ 59
def prefixEnd_289592 : Nat := 4983230072969 + 3 ^ 40 * 289592 * 2
def baseEnd_289592 : Nat := 99133259797957469112131

theorem tailTrace_289592 : CollatzResearch.WordTrace tailWord_289592 prefixEnd_289592 99133259797957469112131 := by
  unfold tailWord_289592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281143983432558610563515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7041525311243411480751353 5281143983432558610563515)
  ·
    refine ⟨7921715975148837915845273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281143983432558610563515 7921715975148837915845273)
    ·
      refine ⟨5941286981361628436883955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7921715975148837915845273 5941286981361628436883955)
      ·
        refine ⟨8911930472042442655325933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941286981361628436883955 8911930472042442655325933)
        ·
          refine ⟨3341973927015915995747225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8911930472042442655325933 3341973927015915995747225)
          ·
            refine ⟨2506480445261936996810419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3341973927015915995747225 2506480445261936996810419)
            ·
              refine ⟨3759720667892905495215629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506480445261936996810419 3759720667892905495215629)
              ·
                refine ⟨1409895250459839560705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3759720667892905495215629 1409895250459839560705861)
                ·
                  refine ⟨264355359461219917632349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409895250459839560705861 264355359461219917632349)
                  ·
                    refine ⟨99133259797957469112131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264355359461219917632349 99133259797957469112131)
                    ·
                      rfl

theorem cell22_289592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_289592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289592 prefixEnd_289592 := by exact prefixLift 289592
  have htrace : WordTrace (prefixWord ++ tailWord_289592) baseStart_289592 baseEnd_289592 := by
    simpa [prefixWord, tailWord_289592, baseEnd_289592] using wordTrace_append hprefix tailTrace_289592
  have hstable : (prefixWord ++ tailWord_289592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289592).length < 2 ^ (prefixWord ++ tailWord_289592).sum := by decide
  have hdescent : baseEnd_289592 < baseStart_289592 := by decide
  rcases family_descends (prefixWord ++ tailWord_289592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289594 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_289594 : Nat := 118140960795 + 289594 * 2 ^ 59
def prefixEnd_289594 : Nat := 4983230072969 + 3 ^ 40 * 289594 * 2
def baseEnd_289594 : Nat := 33044648146276710187375

theorem tailTrace_289594 : CollatzResearch.WordTrace tailWord_289594 prefixEnd_289594 33044648146276710187375 := by
  unfold tailWord_289594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640590228214467890674959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7041573941905247708466557 2640590228214467890674959)
  ·
    refine ⟨3960885342321701836012439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640590228214467890674959 3960885342321701836012439)
    ·
      refine ⟨5941328013482552754018659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960885342321701836012439 5941328013482552754018659)
      ·
        refine ⟨8911992020223829131027989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941328013482552754018659 8911992020223829131027989)
        ·
          refine ⟨417749625947991990516937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8911992020223829131027989 417749625947991990516937)
          ·
            refine ⟨313312219460993992887703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417749625947991990516937 313312219460993992887703)
            ·
              refine ⟨469968329191490989331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313312219460993992887703 469968329191490989331555)
              ·
                refine ⟨704952493787236483997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469968329191490989331555 704952493787236483997333)
                ·
                  refine ⟨33044648146276710187375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 704952493787236483997333 33044648146276710187375)
                  ·
                    rfl

theorem cell22_289594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_289594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289594 prefixEnd_289594 := by exact prefixLift 289594
  have htrace : WordTrace (prefixWord ++ tailWord_289594) baseStart_289594 baseEnd_289594 := by
    simpa [prefixWord, tailWord_289594, baseEnd_289594] using wordTrace_append hprefix tailTrace_289594
  have hstable : (prefixWord ++ tailWord_289594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289594).length < 2 ^ (prefixWord ++ tailWord_289594).sum := by decide
  have hdescent : baseEnd_289594 < baseStart_289594 := by decide
  rcases family_descends (prefixWord ++ tailWord_289594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289609 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_289609 : Nat := 118140960795 + 289609 * 2 ^ 59
def prefixEnd_289609 : Nat := 4983230072969 + 3 ^ 40 * 289609 * 2
def baseEnd_289609 : Nat := 99139079245375091437079

theorem tailTrace_289609 : CollatzResearch.WordTrace tailWord_289609 prefixEnd_289609 99139079245375091437079 := by
  unfold tailWord_289609
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562908007803529124495881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7041938671869019416330587 10562908007803529124495881)
  ·
    refine ⟨7922181005852646843371911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10562908007803529124495881 7922181005852646843371911)
    ·
      refine ⟨11883271508778970265057867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922181005852646843371911 11883271508778970265057867)
      ·
        refine ⟨17824907263168455397586801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883271508778970265057867 17824907263168455397586801)
        ·
          refine ⟨13368680447376341548190101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17824907263168455397586801 13368680447376341548190101)
          ·
            refine ⟨626656895970766010071411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13368680447376341548190101 626656895970766010071411)
            ·
              refine ⟨939985343956149015107117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626656895970766010071411 939985343956149015107117)
              ·
                refine ⟨352494503983555880665169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939985343956149015107117 352494503983555880665169)
                ·
                  refine ⟨264370877987666910498877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352494503983555880665169 264370877987666910498877)
                  ·
                    refine ⟨99139079245375091437079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264370877987666910498877 99139079245375091437079)
                    ·
                      rfl

theorem cell22_289609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_289609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289609 prefixEnd_289609 := by exact prefixLift 289609
  have htrace : WordTrace (prefixWord ++ tailWord_289609) baseStart_289609 baseEnd_289609 := by
    simpa [prefixWord, tailWord_289609, baseEnd_289609] using wordTrace_append hprefix tailTrace_289609
  have hstable : (prefixWord ++ tailWord_289609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289609).length < 2 ^ (prefixWord ++ tailWord_289609).sum := by decide
  have hdescent : baseEnd_289609 < baseStart_289609 := by decide
  rcases family_descends (prefixWord ++ tailWord_289609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289613 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_289613 : Nat := 118140960795 + 289613 * 2 ^ 59
def prefixEnd_289613 : Nat := 4983230072969 + 3 ^ 40 * 289613 * 2
def baseEnd_289613 : Nat := 99140448527120414337067

theorem tailTrace_289613 : CollatzResearch.WordTrace tailWord_289613 prefixEnd_289613 99140448527120414337067 := by
  unfold tailWord_289613
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563053899789037807641493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7042035933192691871760995 10563053899789037807641493)
  ·
    refine ⟨495143151552611147233195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10563053899789037807641493 495143151552611147233195)
    ·
      refine ⟨742714727328916720849793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495143151552611147233195 742714727328916720849793)
      ·
        refine ⟨557036045496687540637345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742714727328916720849793 557036045496687540637345)
        ·
          refine ⟨417777034122515655478009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557036045496687540637345 417777034122515655478009)
          ·
            refine ⟨313332775591886741608507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417777034122515655478009 313332775591886741608507)
            ·
              refine ⟨469999163387830112412761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313332775591886741608507 469999163387830112412761)
              ·
                refine ⟨352499372540872584309571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469999163387830112412761 352499372540872584309571)
                ·
                  refine ⟨528749058811308876464357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352499372540872584309571 528749058811308876464357)
                  ·
                    refine ⟨99140448527120414337067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528749058811308876464357 99140448527120414337067)
                    ·
                      rfl

theorem cell22_289613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_289613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289613 prefixEnd_289613 := by exact prefixLift 289613
  have htrace : WordTrace (prefixWord ++ tailWord_289613) baseStart_289613 baseEnd_289613 := by
    simpa [prefixWord, tailWord_289613, baseEnd_289613] using wordTrace_append hprefix tailTrace_289613
  have hstable : (prefixWord ++ tailWord_289613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289613).length < 2 ^ (prefixWord ++ tailWord_289613).sum := by decide
  have hdescent : baseEnd_289613 < baseStart_289613 := by decide
  rcases family_descends (prefixWord ++ tailWord_289613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289667 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 5]
def baseStart_289667 : Nat := 118140960795 + 289667 * 2 ^ 59
def prefixEnd_289667 : Nat := 4983230072969 + 3 ^ 40 * 289667 * 2
def baseEnd_289667 : Nat := 33052977943560757828967

theorem tailTrace_289667 : CollatzResearch.WordTrace tailWord_289667 prefixEnd_289667 33052977943560757828967 := by
  unfold tailWord_289667
  simp only [CollatzResearch.WordTrace]
  refine ⟨10565023441593405030107255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7043348961062270020071503 10565023441593405030107255)
  ·
    refine ⟨15847535162390107545160883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10565023441593405030107255 15847535162390107545160883)
    ·
      refine ⟨23771302743585161317741325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15847535162390107545160883 23771302743585161317741325)
      ·
        refine ⟨8914238528844435494152997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23771302743585161317741325 8914238528844435494152997)
        ·
          refine ⟨1671419724158331655153687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8914238528844435494152997 1671419724158331655153687)
          ·
            refine ⟨2507129586237497482730531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671419724158331655153687 2507129586237497482730531)
            ·
              refine ⟨3760694379356246224095797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507129586237497482730531 3760694379356246224095797)
              ·
                refine ⟨352565098064648083508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3760694379356246224095797 352565098064648083508981)
                ·
                  refine ⟨33052977943560757828967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352565098064648083508981 33052977943560757828967)
                  ·
                    rfl

theorem cell22_289667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].length) (baseStart_289667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289667 prefixEnd_289667 := by exact prefixLift 289667
  have htrace : WordTrace (prefixWord ++ tailWord_289667) baseStart_289667 baseEnd_289667 := by
    simpa [prefixWord, tailWord_289667, baseEnd_289667] using wordTrace_append hprefix tailTrace_289667
  have hstable : (prefixWord ++ tailWord_289667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289667).length < 2 ^ (prefixWord ++ tailWord_289667).sum := by decide
  have hdescent : baseEnd_289667 < baseStart_289667 := by decide
  rcases family_descends (prefixWord ++ tailWord_289667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289716 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_289716 : Nat := 118140960795 + 289716 * 2 ^ 59
def prefixEnd_289716 : Nat := 4983230072969 + 3 ^ 40 * 289716 * 2
def baseEnd_289716 : Nat := 99175707532062479011751

theorem tailTrace_289716 : CollatzResearch.WordTrace tailWord_289716 prefixEnd_289716 99175707532062479011751 := by
  unfold tailWord_289716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283405309207943199320501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7044540412277257599094001 5283405309207943199320501)
  ·
    refine ⟨495319247738244674936297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5283405309207943199320501 495319247738244674936297)
    ·
      refine ⟨371489435803683506202223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 495319247738244674936297 371489435803683506202223)
      ·
        refine ⟨557234153705525259303335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371489435803683506202223 557234153705525259303335)
        ·
          refine ⟨835851230558287888955003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557234153705525259303335 835851230558287888955003)
          ·
            refine ⟨1253776845837431833432505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835851230558287888955003 1253776845837431833432505)
            ·
              refine ⟨940332634378073875074379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253776845837431833432505 940332634378073875074379)
              ·
                refine ⟨1410498951567110812611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940332634378073875074379 1410498951567110812611569)
                ·
                  refine ⟨1057874213675333109458677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410498951567110812611569 1057874213675333109458677)
                  ·
                    refine ⟨99175707532062479011751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1057874213675333109458677 99175707532062479011751)
                    ·
                      rfl

theorem cell22_289716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_289716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289716 prefixEnd_289716 := by exact prefixLift 289716
  have htrace : WordTrace (prefixWord ++ tailWord_289716) baseStart_289716 baseEnd_289716 := by
    simpa [prefixWord, tailWord_289716, baseEnd_289716] using wordTrace_append hprefix tailTrace_289716
  have hstable : (prefixWord ++ tailWord_289716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289716).length < 2 ^ (prefixWord ++ tailWord_289716).sum := by decide
  have hdescent : baseEnd_289716 < baseStart_289716 := by decide
  rcases family_descends (prefixWord ++ tailWord_289716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289727 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_289727 : Nat := 118140960795 + 289727 * 2 ^ 59
def prefixEnd_289727 : Nat := 4983230072969 + 3 ^ 40 * 289727 * 2
def baseEnd_289727 : Nat := 99179473056862116986717

theorem tailTrace_289727 : CollatzResearch.WordTrace tailWord_289727 prefixEnd_289727 99179473056862116986717 := by
  unfold tailWord_289727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567211821376035277291435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7044807880917356851527623 10567211821376035277291435)
  ·
    refine ⟨15850817732064052915937153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10567211821376035277291435 15850817732064052915937153)
    ·
      refine ⟨11888113299048039686952865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15850817732064052915937153 11888113299048039686952865)
      ·
        refine ⟨8916084974286029765214649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11888113299048039686952865 8916084974286029765214649)
        ·
          refine ⟨6687063730714522323910987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8916084974286029765214649 6687063730714522323910987)
          ·
            refine ⟨10030595596071783485866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687063730714522323910987 10030595596071783485866481)
            ·
              refine ⟨7522946697053837614399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10030595596071783485866481 7522946697053837614399861)
              ·
                refine ⟨705276252848797276349987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7522946697053837614399861 705276252848797276349987)
                ·
                  refine ⟨1057914379273195914524981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705276252848797276349987 1057914379273195914524981)
                  ·
                    refine ⟨99179473056862116986717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1057914379273195914524981 99179473056862116986717)
                    ·
                      rfl

theorem cell22_289727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_289727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289727 prefixEnd_289727 := by exact prefixLift 289727
  have htrace : WordTrace (prefixWord ++ tailWord_289727) baseStart_289727 baseEnd_289727 := by
    simpa [prefixWord, tailWord_289727, baseEnd_289727] using wordTrace_append hprefix tailTrace_289727
  have hstable : (prefixWord ++ tailWord_289727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289727).length < 2 ^ (prefixWord ++ tailWord_289727).sum := by decide
  have hdescent : baseEnd_289727 < baseStart_289727 := by decide
  rcases family_descends (prefixWord ++ tailWord_289727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289789 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_289789 : Nat := 118140960795 + 289789 * 2 ^ 59
def prefixEnd_289789 : Nat := 4983230072969 + 3 ^ 40 * 289789 * 2
def baseEnd_289789 : Nat := 99200696923914621936527

theorem tailTrace_289789 : CollatzResearch.WordTrace tailWord_289789 prefixEnd_289789 99200696923914621936527 := by
  unfold tailWord_289789
  simp only [CollatzResearch.WordTrace]
  refine ⟨10569473147151419866048421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7046315431434279910698947 10569473147151419866048421)
  ·
    refine ⟨1981776215090891224884079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10569473147151419866048421 1981776215090891224884079)
    ·
      refine ⟨2972664322636336837326119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981776215090891224884079 2972664322636336837326119)
      ·
        refine ⟨4458996483954505255989179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972664322636336837326119 4458996483954505255989179)
        ·
          refine ⟨6688494725931757883983769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458996483954505255989179 6688494725931757883983769)
          ·
            refine ⟨5016371044448818412987827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688494725931757883983769 5016371044448818412987827)
            ·
              refine ⟨7524556566673227619481741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5016371044448818412987827 7524556566673227619481741)
              ·
                refine ⟨2821708712502460357305653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7524556566673227619481741 2821708712502460357305653)
                ·
                  refine ⟨264535191797105658497405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2821708712502460357305653 264535191797105658497405)
                  ·
                    refine ⟨99200696923914621936527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264535191797105658497405 99200696923914621936527)
                    ·
                      rfl

theorem cell22_289789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_289789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289789 prefixEnd_289789 := by exact prefixLift 289789
  have htrace : WordTrace (prefixWord ++ tailWord_289789) baseStart_289789 baseEnd_289789 := by
    simpa [prefixWord, tailWord_289789, baseEnd_289789] using wordTrace_append hprefix tailTrace_289789
  have hstable : (prefixWord ++ tailWord_289789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289789).length < 2 ^ (prefixWord ++ tailWord_289789).sum := by decide
  have hdescent : baseEnd_289789 < baseStart_289789 := by decide
  rcases family_descends (prefixWord ++ tailWord_289789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289823 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 1, 3]
def baseStart_289823 : Nat := 118140960795 + 289823 * 2 ^ 59
def prefixEnd_289823 : Nat := 4983230072969 + 3 ^ 40 * 289823 * 2
def baseEnd_289823 : Nat := 99212335818749866586423

theorem tailTrace_289823 : CollatzResearch.WordTrace tailWord_289823 prefixEnd_289823 99212335818749866586423 := by
  unfold tailWord_289823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570713229028243672786123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7047142152685495781857415 10570713229028243672786123)
  ·
    refine ⟨15856069843542365509179185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10570713229028243672786123 15856069843542365509179185)
    ·
      refine ⟨11892052382656774131884389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15856069843542365509179185 11892052382656774131884389)
      ·
        refine ⟨2229759821748145149728323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11892052382656774131884389 2229759821748145149728323)
        ·
          refine ⟨3344639732622217724592485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229759821748145149728323 3344639732622217724592485)
          ·
            refine ⟨627119949866665823361091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3344639732622217724592485 627119949866665823361091)
            ·
              refine ⟨940679924799998735041637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627119949866665823361091 940679924799998735041637)
              ·
                refine ⟨176377485899999762820307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 940679924799998735041637 176377485899999762820307)
                ·
                  refine ⟨264566228849999644230461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176377485899999762820307 264566228849999644230461)
                  ·
                    refine ⟨99212335818749866586423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264566228849999644230461 99212335818749866586423)
                    ·
                      rfl

theorem cell22_289823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_289823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289823 prefixEnd_289823 := by exact prefixLift 289823
  have htrace : WordTrace (prefixWord ++ tailWord_289823) baseStart_289823 baseEnd_289823 := by
    simpa [prefixWord, tailWord_289823, baseEnd_289823] using wordTrace_append hprefix tailTrace_289823
  have hstable : (prefixWord ++ tailWord_289823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289823).length < 2 ^ (prefixWord ++ tailWord_289823).sum := by decide
  have hdescent : baseEnd_289823 < baseStart_289823 := by decide
  rcases family_descends (prefixWord ++ tailWord_289823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289928 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_289928 : Nat := 118140960795 + 289928 * 2 ^ 59
def prefixEnd_289928 : Nat := 4983230072969 + 3 ^ 40 * 289928 * 2
def baseEnd_289928 : Nat := 99248279464564592711101

theorem tailTrace_289928 : CollatzResearch.WordTrace tailWord_289928 prefixEnd_289928 99248279464564592711101 := by
  unfold tailWord_289928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287271446823923302679219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7049695262431897736905625 5287271446823923302679219)
  ·
    refine ⟨7930907170235884954018829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287271446823923302679219 7930907170235884954018829)
    ·
      refine ⟨2974090188838456857757061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7930907170235884954018829 2974090188838456857757061)
      ·
        refine ⟨557641910407210660829449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2974090188838456857757061 557641910407210660829449)
        ·
          refine ⟨418231432805407995622087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557641910407210660829449 418231432805407995622087)
          ·
            refine ⟨627347149208111993433131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418231432805407995622087 627347149208111993433131)
            ·
              refine ⟨941020723812167990149697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627347149208111993433131 941020723812167990149697)
              ·
                refine ⟨705765542859125992612273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941020723812167990149697 705765542859125992612273)
                ·
                  refine ⟨529324157144344494459205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705765542859125992612273 529324157144344494459205)
                  ·
                    refine ⟨99248279464564592711101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 529324157144344494459205 99248279464564592711101)
                    ·
                      rfl

theorem cell22_289928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_289928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289928 prefixEnd_289928 := by exact prefixLift 289928
  have htrace : WordTrace (prefixWord ++ tailWord_289928) baseStart_289928 baseEnd_289928 := by
    simpa [prefixWord, tailWord_289928, baseEnd_289928] using wordTrace_append hprefix tailTrace_289928
  have hstable : (prefixWord ++ tailWord_289928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289928).length < 2 ^ (prefixWord ++ tailWord_289928).sum := by decide
  have hdescent : baseEnd_289928 < baseStart_289928 := by decide
  rcases family_descends (prefixWord ++ tailWord_289928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289941 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_289941 : Nat := 118140960795 + 289941 * 2 ^ 59
def prefixEnd_289941 : Nat := 4983230072969 + 3 ^ 40 * 289941 * 2
def baseEnd_289941 : Nat := 99252729630236892136061

theorem tailTrace_289941 : CollatzResearch.WordTrace tailWord_289941 prefixEnd_289941 99252729630236892136061 := by
  unfold tailWord_289941
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575017042600749825581677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7050011361733833217054451 10575017042600749825581677)
  ·
    refine ⟨3965631390975281184593129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10575017042600749825581677 3965631390975281184593129)
    ·
      refine ⟨2974223543231460888444847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3965631390975281184593129 2974223543231460888444847)
      ·
        refine ⟨4461335314847191332667271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974223543231460888444847 4461335314847191332667271)
        ·
          refine ⟨6692002972270786999000907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461335314847191332667271 6692002972270786999000907)
          ·
            refine ⟨10038004458406180498501361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692002972270786999000907 10038004458406180498501361)
            ·
              refine ⟨7528503343804635373876021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10038004458406180498501361 7528503343804635373876021)
              ·
                refine ⟨705797188481684566300877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7528503343804635373876021 705797188481684566300877)
                ·
                  refine ⟨264673945680631712362829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705797188481684566300877 264673945680631712362829)
                  ·
                    refine ⟨99252729630236892136061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264673945680631712362829 99252729630236892136061)
                    ·
                      rfl

theorem cell22_289941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_289941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_289941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_289941 prefixEnd_289941 := by exact prefixLift 289941
  have htrace : WordTrace (prefixWord ++ tailWord_289941) baseStart_289941 baseEnd_289941 := by
    simpa [prefixWord, tailWord_289941, baseEnd_289941] using wordTrace_append hprefix tailTrace_289941
  have hstable : (prefixWord ++ tailWord_289941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289941).length < 2 ^ (prefixWord ++ tailWord_289941).sum := by decide
  have hdescent : baseEnd_289941 < baseStart_289941 := by decide
  rcases family_descends (prefixWord ++ tailWord_289941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290016 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_290016 : Nat := 118140960795 + 290016 * 2 ^ 59
def prefixEnd_290016 : Nat := 4983230072969 + 3 ^ 40 * 290016 * 2
def baseEnd_290016 : Nat := 33092801220987232170277

theorem tailTrace_290016 : CollatzResearch.WordTrace tailWord_290016 prefixEnd_290016 33092801220987232170277 := by
  unfold tailWord_290016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288876258664518817280951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7051835011552691756374601 5288876258664518817280951)
  ·
    refine ⟨7933314387996778225921427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288876258664518817280951 7933314387996778225921427)
    ·
      refine ⟨11899971581995167338882141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7933314387996778225921427 11899971581995167338882141)
      ·
        refine ⟨4462489343248187752080803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11899971581995167338882141 4462489343248187752080803)
        ·
          refine ⟨6693734014872281628121205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462489343248187752080803 6693734014872281628121205)
          ·
            refine ⟨627537563894276402636363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6693734014872281628121205 627537563894276402636363)
            ·
              refine ⟨941306345841414603954545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627537563894276402636363 941306345841414603954545)
              ·
                refine ⟨705979759381060952965909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941306345841414603954545 705979759381060952965909)
                ·
                  refine ⟨33092801220987232170277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 705979759381060952965909 33092801220987232170277)
                  ·
                    rfl

theorem cell22_290016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_290016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290016 prefixEnd_290016 := by exact prefixLift 290016
  have htrace : WordTrace (prefixWord ++ tailWord_290016) baseStart_290016 baseEnd_290016 := by
    simpa [prefixWord, tailWord_290016, baseEnd_290016] using wordTrace_append hprefix tailTrace_290016
  have hstable : (prefixWord ++ tailWord_290016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290016).length < 2 ^ (prefixWord ++ tailWord_290016).sum := by decide
  have hdescent : baseEnd_290016 < baseStart_290016 := by decide
  rcases family_descends (prefixWord ++ tailWord_290016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290035 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 1, 4]
def baseStart_290035 : Nat := 118140960795 + 290035 * 2 ^ 59
def prefixEnd_290035 : Nat := 4983230072969 + 3 ^ 40 * 290035 * 2
def baseEnd_290035 : Nat := 99284907751251980285773

theorem tailTrace_290035 : CollatzResearch.WordTrace tailWord_290035 prefixEnd_290035 99284907751251980285773 := by
  unfold tailWord_290035
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578445504260203879503559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7052297002840135919669039 10578445504260203879503559)
  ·
    refine ⟨15867668256390305819255339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10578445504260203879503559 15867668256390305819255339)
    ·
      refine ⟨23801502384585458728883009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15867668256390305819255339 23801502384585458728883009)
      ·
        refine ⟨17851126788439094046662257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23801502384585458728883009 17851126788439094046662257)
        ·
          refine ⟨13388345091329320534996693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17851126788439094046662257 13388345091329320534996693)
          ·
            refine ⟨313789338078030950038985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13388345091329320534996693 313789338078030950038985)
            ·
              refine ⟨235342003558523212529239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313789338078030950038985 235342003558523212529239)
              ·
                refine ⟨353013005337784818793859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235342003558523212529239 353013005337784818793859)
                ·
                  refine ⟨529519508006677228190789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353013005337784818793859 529519508006677228190789)
                  ·
                    refine ⟨99284907751251980285773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 529519508006677228190789 99284907751251980285773)
                    ·
                      rfl

theorem cell22_290035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 4].length) (baseStart_290035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290035 prefixEnd_290035 := by exact prefixLift 290035
  have htrace : WordTrace (prefixWord ++ tailWord_290035) baseStart_290035 baseEnd_290035 := by
    simpa [prefixWord, tailWord_290035, baseEnd_290035] using wordTrace_append hprefix tailTrace_290035
  have hstable : (prefixWord ++ tailWord_290035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290035).length < 2 ^ (prefixWord ++ tailWord_290035).sum := by decide
  have hdescent : baseEnd_290035 < baseStart_290035 := by decide
  rcases family_descends (prefixWord ++ tailWord_290035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290050 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_290050 : Nat := 118140960795 + 290050 * 2 ^ 59
def prefixEnd_290050 : Nat := 4983230072969 + 3 ^ 40 * 290050 * 2
def baseEnd_290050 : Nat := 33096680852598980386909

theorem tailTrace_290050 : CollatzResearch.WordTrace tailWord_290050 prefixEnd_290050 33096680852598980386909 := by
  unfold tailWord_290050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644748149801465360324901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7052661732803907627533069 2644748149801465360324901)
  ·
    refine ⟨495890278087774755060919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2644748149801465360324901 495890278087774755060919)
    ·
      refine ⟨743835417131662132591379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495890278087774755060919 743835417131662132591379)
      ·
        refine ⟨1115753125697493198887069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743835417131662132591379 1115753125697493198887069)
        ·
          refine ⟨418407422136559949582651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1115753125697493198887069 418407422136559949582651)
          ·
            refine ⟨627611133204839924373977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418407422136559949582651 627611133204839924373977)
            ·
              refine ⟨470708349903629943280483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627611133204839924373977 470708349903629943280483)
              ·
                refine ⟨706062524855444914920725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470708349903629943280483 706062524855444914920725)
                ·
                  refine ⟨33096680852598980386909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 706062524855444914920725 33096680852598980386909)
                  ·
                    rfl

theorem cell22_290050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_290050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290050 prefixEnd_290050 := by exact prefixLift 290050
  have htrace : WordTrace (prefixWord ++ tailWord_290050) baseStart_290050 baseEnd_290050 := by
    simpa [prefixWord, tailWord_290050, baseEnd_290050] using wordTrace_append hprefix tailTrace_290050
  have hstable : (prefixWord ++ tailWord_290050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290050).length < 2 ^ (prefixWord ++ tailWord_290050).sum := by decide
  have hdescent : baseEnd_290050 < baseStart_290050 := by decide
  rcases family_descends (prefixWord ++ tailWord_290050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290065 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_290065 : Nat := 118140960795 + 290065 * 2 ^ 59
def prefixEnd_290065 : Nat := 4983230072969 + 3 ^ 40 * 290065 * 2
def baseEnd_290065 : Nat := 99295177364341902035681

theorem tailTrace_290065 : CollatzResearch.WordTrace tailWord_290065 prefixEnd_290065 99295177364341902035681 := by
  unfold tailWord_290065
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579539694151519003095649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7053026462767679335397099 10579539694151519003095649)
  ·
    refine ⟨7934654770613639252321737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10579539694151519003095649 7934654770613639252321737)
    ·
      refine ⟨5950991077960229439241303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7934654770613639252321737 5950991077960229439241303)
      ·
        refine ⟨8926486616940344158861955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950991077960229439241303 8926486616940344158861955)
        ·
          refine ⟨13389729925410516238292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926486616940344158861955 13389729925410516238292933)
          ·
            refine ⟨2510574361014471794679925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13389729925410516238292933 2510574361014471794679925)
            ·
              refine ⟨235366346345106730751243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2510574361014471794679925 235366346345106730751243)
              ·
                refine ⟨353049519517660096126865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235366346345106730751243 353049519517660096126865)
                ·
                  refine ⟨264787139638245072095149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353049519517660096126865 264787139638245072095149)
                  ·
                    refine ⟨99295177364341902035681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264787139638245072095149 99295177364341902035681)
                    ·
                      rfl

theorem cell22_290065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_290065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290065 prefixEnd_290065 := by exact prefixLift 290065
  have htrace : WordTrace (prefixWord ++ tailWord_290065) baseStart_290065 baseEnd_290065 := by
    simpa [prefixWord, tailWord_290065, baseEnd_290065] using wordTrace_append hprefix tailTrace_290065
  have hstable : (prefixWord ++ tailWord_290065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290065).length < 2 ^ (prefixWord ++ tailWord_290065).sum := by decide
  have hdescent : baseEnd_290065 < baseStart_290065 := by decide
  rcases family_descends (prefixWord ++ tailWord_290065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290106 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_290106 : Nat := 118140960795 + 290106 * 2 ^ 59
def prefixEnd_290106 : Nat := 4983230072969 + 3 ^ 40 * 290106 * 2
def baseEnd_290106 : Nat := 33103070834077153920185

theorem tailTrace_290106 : CollatzResearch.WordTrace tailWord_290106 prefixEnd_290106 33103070834077153920185 := by
  unfold tailWord_290106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645258771750745751334543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7054023391335322003558781 2645258771750745751334543)
  ·
    refine ⟨3967888157626118627001815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645258771750745751334543 3967888157626118627001815)
    ·
      refine ⟨5951832236439177940502723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967888157626118627001815 5951832236439177940502723)
      ·
        refine ⟨8927748354658766910754085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951832236439177940502723 8927748354658766910754085)
        ·
          refine ⟨1673952816498518795766391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8927748354658766910754085 1673952816498518795766391)
          ·
            refine ⟨2510929224747778193649587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673952816498518795766391 2510929224747778193649587)
            ·
              refine ⟨3766393837121667290474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510929224747778193649587 3766393837121667290474381)
              ·
                refine ⟨1412397688920625233927893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766393837121667290474381 1412397688920625233927893)
                ·
                  refine ⟨33103070834077153920185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1412397688920625233927893 33103070834077153920185)
                  ·
                    rfl

theorem cell22_290106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_290106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290106 prefixEnd_290106 := by exact prefixLift 290106
  have htrace : WordTrace (prefixWord ++ tailWord_290106) baseStart_290106 baseEnd_290106 := by
    simpa [prefixWord, tailWord_290106, baseEnd_290106] using wordTrace_append hprefix tailTrace_290106
  have hstable : (prefixWord ++ tailWord_290106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290106).length < 2 ^ (prefixWord ++ tailWord_290106).sum := by decide
  have hdescent : baseEnd_290106 < baseStart_290106 := by decide
  rcases family_descends (prefixWord ++ tailWord_290106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290121 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_290121 : Nat := 118140960795 + 290121 * 2 ^ 59
def prefixEnd_290121 : Nat := 4983230072969 + 3 ^ 40 * 290121 * 2
def baseEnd_290121 : Nat := 99314347308776422635509

theorem tailTrace_290121 : CollatzResearch.WordTrace tailWord_290121 prefixEnd_290121 99314347308776422635509 := by
  unfold tailWord_290121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10581582181948640567134217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7054388121299093711422811 10581582181948640567134217)
  ·
    refine ⟨7936186636461480425350663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10581582181948640567134217 7936186636461480425350663)
    ·
      refine ⟨11904279954692220638025995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7936186636461480425350663 11904279954692220638025995)
      ·
        refine ⟨17856419932038330957038993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11904279954692220638025995 17856419932038330957038993)
        ·
          refine ⟨13392314949028748217779245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17856419932038330957038993 13392314949028748217779245)
          ·
            refine ⟨5022118105885780581667217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13392314949028748217779245 5022118105885780581667217)
            ·
              refine ⟨3766588579414335436250413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022118105885780581667217 3766588579414335436250413)
              ·
                refine ⟨1412470717280375788593905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766588579414335436250413 1412470717280375788593905)
                ·
                  refine ⟨1059353037960281841445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412470717280375788593905 1059353037960281841445429)
                  ·
                    refine ⟨99314347308776422635509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1059353037960281841445429 99314347308776422635509)
                    ·
                      rfl

theorem cell22_290121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_290121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290121 prefixEnd_290121 := by exact prefixLift 290121
  have htrace : WordTrace (prefixWord ++ tailWord_290121) baseStart_290121 baseEnd_290121 := by
    simpa [prefixWord, tailWord_290121, baseEnd_290121] using wordTrace_append hprefix tailTrace_290121
  have hstable : (prefixWord ++ tailWord_290121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290121).length < 2 ^ (prefixWord ++ tailWord_290121).sum := by decide
  have hdescent : baseEnd_290121 < baseStart_290121 := by decide
  rcases family_descends (prefixWord ++ tailWord_290121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290183 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_290183 : Nat := 118140960795 + 290183 * 2 ^ 59
def prefixEnd_290183 : Nat := 4983230072969 + 3 ^ 40 * 290183 * 2
def baseEnd_290183 : Nat := 99335571175828927585319

theorem tailTrace_290183 : CollatzResearch.WordTrace tailWord_290183 prefixEnd_290183 99335571175828927585319 := by
  unfold tailWord_290183
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583843507724025155891203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7055895671816016770594135 10583843507724025155891203)
  ·
    refine ⟨15875765261586037733836805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583843507724025155891203 15875765261586037733836805)
    ·
      refine ⟨2976705986547382075094401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15875765261586037733836805 2976705986547382075094401)
      ·
        refine ⟨2232529489910536556320801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976705986547382075094401 2232529489910536556320801)
        ·
          refine ⟨1674397117432902417240601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232529489910536556320801 1674397117432902417240601)
          ·
            refine ⟨1255797838074676812930451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674397117432902417240601 1255797838074676812930451)
            ·
              refine ⟨1883696757112015219395677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255797838074676812930451 1883696757112015219395677)
              ·
                refine ⟨706386283917005707273379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1883696757112015219395677 706386283917005707273379)
                ·
                  refine ⟨1059579425875508560910069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706386283917005707273379 1059579425875508560910069)
                  ·
                    refine ⟨99335571175828927585319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1059579425875508560910069 99335571175828927585319)
                    ·
                      rfl

theorem cell22_290183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_290183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290183 prefixEnd_290183 := by exact prefixLift 290183
  have htrace : WordTrace (prefixWord ++ tailWord_290183) baseStart_290183 baseEnd_290183 := by
    simpa [prefixWord, tailWord_290183, baseEnd_290183] using wordTrace_append hprefix tailTrace_290183
  have hstable : (prefixWord ++ tailWord_290183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290183).length < 2 ^ (prefixWord ++ tailWord_290183).sum := by decide
  have hdescent : baseEnd_290183 < baseStart_290183 := by decide
  rcases family_descends (prefixWord ++ tailWord_290183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290335 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 4, 3]
def baseStart_290335 : Nat := 118140960795 + 290335 * 2 ^ 59
def prefixEnd_290335 : Nat := 4983230072969 + 3 ^ 40 * 290335 * 2
def baseEnd_290335 : Nat := 99387603882151197784853

theorem tailTrace_290335 : CollatzResearch.WordTrace tailWord_290335 prefixEnd_290335 99387603882151197784853 := by
  unfold tailWord_290335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589387403173355115424459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7059591602115570076949639 10589387403173355115424459)
  ·
    refine ⟨15884081104760032673136689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10589387403173355115424459 15884081104760032673136689)
    ·
      refine ⟨11913060828570024504852517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15884081104760032673136689 11913060828570024504852517)
      ·
        refine ⟨2233698905356879594659847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11913060828570024504852517 2233698905356879594659847)
        ·
          refine ⟨3350548358035319391989771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233698905356879594659847 3350548358035319391989771)
          ·
            refine ⟨5025822537052979087984657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350548358035319391989771 5025822537052979087984657)
            ·
              refine ⟨3769366902789734315988493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5025822537052979087984657 3769366902789734315988493)
              ·
                refine ⟨1413512588546150368495685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3769366902789734315988493 1413512588546150368495685)
                ·
                  refine ⟨265033610352403194092941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413512588546150368495685 265033610352403194092941)
                  ·
                    refine ⟨99387603882151197784853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265033610352403194092941 99387603882151197784853)
                    ·
                      rfl

theorem cell22_290335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_290335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290335 prefixEnd_290335 := by exact prefixLift 290335
  have htrace : WordTrace (prefixWord ++ tailWord_290335) baseStart_290335 baseEnd_290335 := by
    simpa [prefixWord, tailWord_290335, baseEnd_290335] using wordTrace_append hprefix tailTrace_290335
  have hstable : (prefixWord ++ tailWord_290335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290335).length < 2 ^ (prefixWord ++ tailWord_290335).sum := by decide
  have hdescent : baseEnd_290335 < baseStart_290335 := by decide
  rcases family_descends (prefixWord ++ tailWord_290335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290337 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 4]
def baseStart_290337 : Nat := 118140960795 + 290337 * 2 ^ 59
def prefixEnd_290337 : Nat := 4983230072969 + 3 ^ 40 * 290337 * 2
def baseEnd_290337 : Nat := 33129429507674619744949

theorem tailTrace_290337 : CollatzResearch.WordTrace tailWord_290337 prefixEnd_290337 33129429507674619744949 := by
  unfold tailWord_290337
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589460349166109456997265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7059640232777406304664843 10589460349166109456997265)
  ·
    refine ⟨7942095261874582092747949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10589460349166109456997265 7942095261874582092747949)
    ·
      refine ⟨2978285723202968284780481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7942095261874582092747949 2978285723202968284780481)
      ·
        refine ⟨2233714292402226213585361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978285723202968284780481 2233714292402226213585361)
        ·
          refine ⟨1675285719301669660189021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233714292402226213585361 1675285719301669660189021)
          ·
            refine ⟨628232144738126122570883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1675285719301669660189021 628232144738126122570883)
            ·
              refine ⟨942348217107189183856325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628232144738126122570883 942348217107189183856325)
              ·
                refine ⟨176690290707597971973061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 942348217107189183856325 176690290707597971973061)
                ·
                  refine ⟨33129429507674619744949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176690290707597971973061 33129429507674619744949)
                  ·
                    rfl

theorem cell22_290337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_290337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290337 prefixEnd_290337 := by exact prefixLift 290337
  have htrace : WordTrace (prefixWord ++ tailWord_290337) baseStart_290337 baseEnd_290337 := by
    simpa [prefixWord, tailWord_290337, baseEnd_290337] using wordTrace_append hprefix tailTrace_290337
  have hstable : (prefixWord ++ tailWord_290337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290337).length < 2 ^ (prefixWord ++ tailWord_290337).sum := by decide
  have hdescent : baseEnd_290337 < baseStart_290337 := by decide
  rcases family_descends (prefixWord ++ tailWord_290337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290367 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 2, 4]
def baseStart_290367 : Nat := 118140960795 + 290367 * 2 ^ 59
def prefixEnd_290367 : Nat := 4983230072969 + 3 ^ 40 * 290367 * 2
def baseEnd_290367 : Nat := 99398558136113780984755

theorem tailTrace_290367 : CollatzResearch.WordTrace tailWord_290367 prefixEnd_290367 99398558136113780984755 := by
  unfold tailWord_290367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10590554539057424580589355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7060369692704949720392903 10590554539057424580589355)
  ·
    refine ⟨15885831808586136870884033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10590554539057424580589355 15885831808586136870884033)
    ·
      refine ⟨11914373856439602653163025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15885831808586136870884033 11914373856439602653163025)
      ·
        refine ⟨8935780392329701989872269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11914373856439602653163025 8935780392329701989872269)
        ·
          refine ⟨3350917647123638246202101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8935780392329701989872269 3350917647123638246202101)
          ·
            refine ⟨314148529417841085581447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3350917647123638246202101 314148529417841085581447)
            ·
              refine ⟨471222794126761628372171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314148529417841085581447 471222794126761628372171)
              ·
                refine ⟨706834191190142442558257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471222794126761628372171 706834191190142442558257)
                ·
                  refine ⟨530125643392606831918693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706834191190142442558257 530125643392606831918693)
                  ·
                    refine ⟨99398558136113780984755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530125643392606831918693 99398558136113780984755)
                    ·
                      rfl

theorem cell22_290367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_290367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290367 prefixEnd_290367 := by exact prefixLift 290367
  have htrace : WordTrace (prefixWord ++ tailWord_290367) baseStart_290367 baseEnd_290367 := by
    simpa [prefixWord, tailWord_290367, baseEnd_290367] using wordTrace_append hprefix tailTrace_290367
  have hstable : (prefixWord ++ tailWord_290367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290367).length < 2 ^ (prefixWord ++ tailWord_290367).sum := by decide
  have hdescent : baseEnd_290367 < baseStart_290367 := by decide
  rcases family_descends (prefixWord ++ tailWord_290367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290487 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_290487 : Nat := 118140960795 + 290487 * 2 ^ 59
def prefixEnd_290487 : Nat := 4983230072969 + 3 ^ 40 * 290487 * 2
def baseEnd_290487 : Nat := 99439636588473467984387

theorem tailTrace_290487 : CollatzResearch.WordTrace tailWord_290487 prefixEnd_290487 99439636588473467984387 := by
  unfold tailWord_290487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594931298622685074957715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7063287532415123383305143 10594931298622685074957715)
  ·
    refine ⟨15892396947934027612436573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10594931298622685074957715 15892396947934027612436573)
    ·
      refine ⟨5959648855475260354663715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15892396947934027612436573 5959648855475260354663715)
      ·
        refine ⟨8939473283212890531995573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959648855475260354663715 8939473283212890531995573)
        ·
          refine ⟨838075620301208487374585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8939473283212890531995573 838075620301208487374585)
          ·
            refine ⟨628556715225906365530939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838075620301208487374585 628556715225906365530939)
            ·
              refine ⟨942835072838859548296409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628556715225906365530939 942835072838859548296409)
              ·
                refine ⟨707126304629144661222307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942835072838859548296409 707126304629144661222307)
                ·
                  refine ⟨1060689456943716991833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707126304629144661222307 1060689456943716991833461)
                  ·
                    refine ⟨99439636588473467984387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1060689456943716991833461 99439636588473467984387)
                    ·
                      rfl

theorem cell22_290487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_290487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290487 prefixEnd_290487 := by exact prefixLift 290487
  have htrace : WordTrace (prefixWord ++ tailWord_290487) baseStart_290487 baseEnd_290487 := by
    simpa [prefixWord, tailWord_290487, baseEnd_290487] using wordTrace_append hprefix tailTrace_290487
  have hstable : (prefixWord ++ tailWord_290487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290487).length < 2 ^ (prefixWord ++ tailWord_290487).sum := by decide
  have hdescent : baseEnd_290487 < baseStart_290487 := by decide
  rcases family_descends (prefixWord ++ tailWord_290487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290504 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_290504 : Nat := 118140960795 + 290504 * 2 ^ 59
def prefixEnd_290504 : Nat := 4983230072969 + 3 ^ 40 * 290504 * 2
def baseEnd_290504 : Nat := 99445456035891090309335

theorem tailTrace_290504 : CollatzResearch.WordTrace tailWord_290504 prefixEnd_290504 99445456035891090309335 := by
  unfold tailWord_290504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297775669780548489163283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7063700893040731318884377 5297775669780548489163283)
  ·
    refine ⟨7946663504670822733744925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297775669780548489163283 7946663504670822733744925)
    ·
      refine ⟨2979998814251558525154347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7946663504670822733744925 2979998814251558525154347)
      ·
        refine ⟨4469998221377337787731521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979998814251558525154347 4469998221377337787731521)
        ·
          refine ⟨3352498666033003340798641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469998221377337787731521 3352498666033003340798641)
          ·
            refine ⟨2514373999524752505598981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352498666033003340798641 2514373999524752505598981)
            ·
              refine ⟨471445124910891094799809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514373999524752505598981 471445124910891094799809)
              ·
                refine ⟨353583843683168321099857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471445124910891094799809 353583843683168321099857)
                ·
                  refine ⟨265187882762376240824893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353583843683168321099857 265187882762376240824893)
                  ·
                    refine ⟨99445456035891090309335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265187882762376240824893 99445456035891090309335)
                    ·
                      rfl

theorem cell22_290504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_290504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290504 prefixEnd_290504 := by exact prefixLift 290504
  have htrace : WordTrace (prefixWord ++ tailWord_290504) baseStart_290504 baseEnd_290504 := by
    simpa [prefixWord, tailWord_290504, baseEnd_290504] using wordTrace_append hprefix tailTrace_290504
  have hstable : (prefixWord ++ tailWord_290504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290504).length < 2 ^ (prefixWord ++ tailWord_290504).sum := by decide
  have hdescent : baseEnd_290504 < baseStart_290504 := by decide
  rcases family_descends (prefixWord ++ tailWord_290504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290560 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_290560 : Nat := 118140960795 + 290560 * 2 ^ 59
def prefixEnd_290560 : Nat := 4983230072969 + 3 ^ 40 * 290560 * 2
def baseEnd_290560 : Nat := 99464625980325610909163

theorem tailTrace_290560 : CollatzResearch.WordTrace tailWord_290560 prefixEnd_290560 99464625980325610909163 := by
  unfold tailWord_290560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298796913679109271182567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7065062551572145694910089 5298796913679109271182567)
  ·
    refine ⟨7948195370518663906773851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298796913679109271182567 7948195370518663906773851)
    ·
      refine ⟨11922293055777995860160777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7948195370518663906773851 11922293055777995860160777)
      ·
        refine ⟨8941719791833496895120583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11922293055777995860160777 8941719791833496895120583)
        ·
          refine ⟨13412579687750245342680875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8941719791833496895120583 13412579687750245342680875)
          ·
            refine ⟨20118869531625368014021313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13412579687750245342680875 20118869531625368014021313)
            ·
              refine ⟨15089152148719026010515985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20118869531625368014021313 15089152148719026010515985)
              ·
                refine ⟨11316864111539269507886989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15089152148719026010515985 11316864111539269507886989)
                ·
                  refine ⟨4243824041827226065457621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11316864111539269507886989 4243824041827226065457621)
                  ·
                    refine ⟨99464625980325610909163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4243824041827226065457621 99464625980325610909163)
                    ·
                      rfl

theorem cell22_290560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_290560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290560 prefixEnd_290560 := by exact prefixLift 290560
  have htrace : WordTrace (prefixWord ++ tailWord_290560) baseStart_290560 baseEnd_290560 := by
    simpa [prefixWord, tailWord_290560, baseEnd_290560] using wordTrace_append hprefix tailTrace_290560
  have hstable : (prefixWord ++ tailWord_290560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290560).length < 2 ^ (prefixWord ++ tailWord_290560).sum := by decide
  have hdescent : baseEnd_290560 < baseStart_290560 := by decide
  rcases family_descends (prefixWord ++ tailWord_290560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290575 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_290575 : Nat := 118140960795 + 290575 * 2 ^ 59
def prefixEnd_290575 : Nat := 4983230072969 + 3 ^ 40 * 290575 * 2
def baseEnd_290575 : Nat := 99469760786870571784117

theorem tailTrace_290575 : CollatzResearch.WordTrace tailWord_290575 prefixEnd_290575 99469760786870571784117 := by
  unfold tailWord_290575
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598140922303876104161179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7065427281535917402774119 10598140922303876104161179)
  ·
    refine ⟨15897211383455814156241769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10598140922303876104161179 15897211383455814156241769)
    ·
      refine ⟨11922908537591860617181327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15897211383455814156241769 11922908537591860617181327)
      ·
        refine ⟨17884362806387790925771991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922908537591860617181327 17884362806387790925771991)
        ·
          refine ⟨26826544209581686388657987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17884362806387790925771991 26826544209581686388657987)
          ·
            refine ⟨40239816314372529582986981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26826544209581686388657987 40239816314372529582986981)
            ·
              refine ⟨7544965558944849296810059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40239816314372529582986981 7544965558944849296810059)
              ·
                refine ⟨11317448338417273945215089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7544965558944849296810059 11317448338417273945215089)
                ·
                  refine ⟨8488086253812955458911317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317448338417273945215089 8488086253812955458911317)
                  ·
                    refine ⟨99469760786870571784117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8488086253812955458911317 99469760786870571784117)
                    ·
                      rfl

theorem cell22_290575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_290575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290575 prefixEnd_290575 := by exact prefixLift 290575
  have htrace : WordTrace (prefixWord ++ tailWord_290575) baseStart_290575 baseEnd_290575 := by
    simpa [prefixWord, tailWord_290575, baseEnd_290575] using wordTrace_append hprefix tailTrace_290575
  have hstable : (prefixWord ++ tailWord_290575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290575).length < 2 ^ (prefixWord ++ tailWord_290575).sum := by decide
  have hdescent : baseEnd_290575 < baseStart_290575 := by decide
  rcases family_descends (prefixWord ++ tailWord_290575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290609 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_290609 : Nat := 118140960795 + 290609 * 2 ^ 59
def prefixEnd_290609 : Nat := 4983230072969 + 3 ^ 40 * 290609 * 2
def baseEnd_290609 : Nat := 99481399681705816434013

theorem tailTrace_290609 : CollatzResearch.WordTrace tailWord_290609 prefixEnd_290609 99481399681705816434013 := by
  unfold tailWord_290609
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599381004180699910898881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7066254002787133273932587 10599381004180699910898881)
  ·
    refine ⟨7949535753135524933174161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10599381004180699910898881 7949535753135524933174161)
    ·
      refine ⟨5962151814851643699880621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7949535753135524933174161 5962151814851643699880621)
      ·
        refine ⟨2235806930569366387455233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5962151814851643699880621 2235806930569366387455233)
        ·
          refine ⟨1676855197927024790591425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235806930569366387455233 1676855197927024790591425)
          ·
            refine ⟨1257641398445268592943569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676855197927024790591425 1257641398445268592943569)
            ·
              refine ⟨943231048833951444707677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257641398445268592943569 943231048833951444707677)
              ·
                refine ⟨353711643312731791765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943231048833951444707677 353711643312731791765379)
                ·
                  refine ⟨530567464969097687648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353711643312731791765379 530567464969097687648069)
                  ·
                    refine ⟨99481399681705816434013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530567464969097687648069 99481399681705816434013)
                    ·
                      rfl

theorem cell22_290609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_290609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290609 prefixEnd_290609 := by exact prefixLift 290609
  have htrace : WordTrace (prefixWord ++ tailWord_290609) baseStart_290609 baseEnd_290609 := by
    simpa [prefixWord, tailWord_290609, baseEnd_290609] using wordTrace_append hprefix tailTrace_290609
  have hstable : (prefixWord ++ tailWord_290609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290609).length < 2 ^ (prefixWord ++ tailWord_290609).sum := by decide
  have hdescent : baseEnd_290609 < baseStart_290609 := by decide
  rcases family_descends (prefixWord ++ tailWord_290609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290630 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_290630 : Nat := 118140960795 + 290630 * 2 ^ 59
def prefixEnd_290630 : Nat := 4983230072969 + 3 ^ 40 * 290630 * 2
def baseEnd_290630 : Nat := 33162862803622920552983

theorem tailTrace_290630 : CollatzResearch.WordTrace tailWord_290630 prefixEnd_290630 33162862803622920552983 := by
  unfold tailWord_290630
  simp only [CollatzResearch.WordTrace]
  refine ⟨331254591784519390544167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7066764624736413664942229 331254591784519390544167)
  ·
    refine ⟨496881887676779085816251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331254591784519390544167 496881887676779085816251)
    ·
      refine ⟨745322831515168628724377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496881887676779085816251 745322831515168628724377)
      ·
        refine ⟨558992123636376471543283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745322831515168628724377 558992123636376471543283)
        ·
          refine ⟨838488185454564707314925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558992123636376471543283 838488185454564707314925)
          ·
            refine ⟨314433069545461765243097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 838488185454564707314925 314433069545461765243097)
            ·
              refine ⟨235824802159096323932323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314433069545461765243097 235824802159096323932323)
              ·
                refine ⟨353737203238644485898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235824802159096323932323 353737203238644485898485)
                ·
                  refine ⟨33162862803622920552983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 353737203238644485898485 33162862803622920552983)
                  ·
                    rfl

theorem cell22_290630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_290630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290630 prefixEnd_290630 := by exact prefixLift 290630
  have htrace : WordTrace (prefixWord ++ tailWord_290630) baseStart_290630 baseEnd_290630 := by
    simpa [prefixWord, tailWord_290630, baseEnd_290630] using wordTrace_append hprefix tailTrace_290630
  have hstable : (prefixWord ++ tailWord_290630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290630).length < 2 ^ (prefixWord ++ tailWord_290630).sum := by decide
  have hdescent : baseEnd_290630 < baseStart_290630 := by decide
  rcases family_descends (prefixWord ++ tailWord_290630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290682 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_290682 : Nat := 118140960795 + 290682 * 2 ^ 59
def prefixEnd_290682 : Nat := 4983230072969 + 3 ^ 40 * 290682 * 2
def baseEnd_290682 : Nat := 99506389073557959358789

theorem tailTrace_290682 : CollatzResearch.WordTrace tailWord_290682 prefixEnd_290682 99506389073557959358789 := by
  unfold tailWord_290682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650510883229058344576575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7068029021944155585537533 2650510883229058344576575)
  ·
    refine ⟨3975766324843587516864863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650510883229058344576575 3975766324843587516864863)
    ·
      refine ⟨5963649487265381275297295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975766324843587516864863 5963649487265381275297295)
      ·
        refine ⟨8945474230898071912945943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963649487265381275297295 8945474230898071912945943)
        ·
          refine ⟨13418211346347107869418915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945474230898071912945943 13418211346347107869418915)
          ·
            refine ⟨20127317019520661804128373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13418211346347107869418915 20127317019520661804128373)
            ·
              refine ⟨1886935970580062044137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20127317019520661804128373 1886935970580062044137035)
              ·
                refine ⟨2830403955870093066205553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886935970580062044137035 2830403955870093066205553)
                ·
                  refine ⟨2122802966902569799654165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830403955870093066205553 2122802966902569799654165)
                  ·
                    refine ⟨99506389073557959358789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2122802966902569799654165 99506389073557959358789)
                    ·
                      rfl

theorem cell22_290682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_290682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290682 prefixEnd_290682 := by exact prefixLift 290682
  have htrace : WordTrace (prefixWord ++ tailWord_290682) baseStart_290682 baseEnd_290682 := by
    simpa [prefixWord, tailWord_290682, baseEnd_290682] using wordTrace_append hprefix tailTrace_290682
  have hstable : (prefixWord ++ tailWord_290682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290682).length < 2 ^ (prefixWord ++ tailWord_290682).sum := by decide
  have hdescent : baseEnd_290682 < baseStart_290682 := by decide
  rcases family_descends (prefixWord ++ tailWord_290682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290686 : List Nat := [4, 2, 3, 1, 1, 1, 3, 7]
def baseStart_290686 : Nat := 118140960795 + 290686 * 2 ^ 59
def prefixEnd_290686 : Nat := 4983230072969 + 3 ^ 40 * 290686 * 2
def baseEnd_290686 : Nat := 11056417595033698028753

theorem tailTrace_290686 : CollatzResearch.WordTrace tailWord_290686 prefixEnd_290686 11056417595033698028753 := by
  unfold tailWord_290686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325273678112717757681489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7068126283267828040967941 1325273678112717757681489)
  ·
    refine ⟨993955258584538318261117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1325273678112717757681489 993955258584538318261117)
    ·
      refine ⟨372733221969201869347919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 993955258584538318261117 372733221969201869347919)
      ·
        refine ⟨559099832953802804021879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372733221969201869347919 559099832953802804021879)
        ·
          refine ⟨838649749430704206032819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559099832953802804021879 838649749430704206032819)
          ·
            refine ⟨1257974624146056309049229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838649749430704206032819 1257974624146056309049229)
            ·
              refine ⟨471740484054771115893461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1257974624146056309049229 471740484054771115893461)
              ·
                refine ⟨11056417595033698028753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 471740484054771115893461 11056417595033698028753)
                ·
                  rfl

theorem cell22_290686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_290686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290686 prefixEnd_290686 := by exact prefixLift 290686
  have htrace : WordTrace (prefixWord ++ tailWord_290686) baseStart_290686 baseEnd_290686 := by
    simpa [prefixWord, tailWord_290686, baseEnd_290686] using wordTrace_append hprefix tailTrace_290686
  have hstable : (prefixWord ++ tailWord_290686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290686).length < 2 ^ (prefixWord ++ tailWord_290686).sum := by decide
  have hdescent : baseEnd_290686 < baseStart_290686 := by decide
  rcases family_descends (prefixWord ++ tailWord_290686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290808 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_290808 : Nat := 118140960795 + 290808 * 2 ^ 59
def prefixEnd_290808 : Nat := 4983230072969 + 3 ^ 40 * 290808 * 2
def baseEnd_290808 : Nat := 99549521448535630708403

theorem tailTrace_290808 : CollatzResearch.WordTrace tailWord_290808 prefixEnd_290808 99549521448535630708403 := by
  unfold tailWord_290808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303319565229878448696539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7071092753639837931595385 5303319565229878448696539)
  ·
    refine ⟨7954979347844817673044809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303319565229878448696539 7954979347844817673044809)
    ·
      refine ⟨5966234510883613254783607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7954979347844817673044809 5966234510883613254783607)
      ·
        refine ⟨8949351766325419882175411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966234510883613254783607 8949351766325419882175411)
        ·
          refine ⟨13424027649488129823263117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8949351766325419882175411 13424027649488129823263117)
          ·
            refine ⟨5034010368558048683723669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13424027649488129823263117 5034010368558048683723669)
            ·
              refine ⟨235969236026158532049547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5034010368558048683723669 235969236026158532049547)
              ·
                refine ⟨353953854039237798074321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235969236026158532049547 353953854039237798074321)
                ·
                  refine ⟨265465390529428348555741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353953854039237798074321 265465390529428348555741)
                  ·
                    refine ⟨99549521448535630708403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265465390529428348555741 99549521448535630708403)
                    ·
                      rfl

theorem cell22_290808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_290808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290808 prefixEnd_290808 := by exact prefixLift 290808
  have htrace : WordTrace (prefixWord ++ tailWord_290808) baseStart_290808 baseEnd_290808 := by
    simpa [prefixWord, tailWord_290808, baseEnd_290808] using wordTrace_append hprefix tailTrace_290808
  have hstable : (prefixWord ++ tailWord_290808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290808).length < 2 ^ (prefixWord ++ tailWord_290808).sum := by decide
  have hdescent : baseEnd_290808 < baseStart_290808 := by decide
  rcases family_descends (prefixWord ++ tailWord_290808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290829 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_290829 : Nat := 118140960795 + 290829 * 2 ^ 59
def prefixEnd_290829 : Nat := 4983230072969 + 3 ^ 40 * 290829 * 2
def baseEnd_290829 : Nat := 99556710177698575933339

theorem tailTrace_290829 : CollatzResearch.WordTrace tailWord_290829 prefixEnd_290829 99556710177698575933339 := by
  unfold tailWord_290829
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607405063383677483907541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7071603375589118322605027 10607405063383677483907541)
  ·
    refine ⟨248611056173054941029083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10607405063383677483907541 248611056173054941029083)
    ·
      refine ⟨372916584259582411543625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248611056173054941029083 372916584259582411543625)
      ·
        refine ⟨279687438194686808657719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372916584259582411543625 279687438194686808657719)
        ·
          refine ⟨419531157292030212986579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279687438194686808657719 419531157292030212986579)
          ·
            refine ⟨629296735938045319479869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419531157292030212986579 629296735938045319479869)
            ·
              refine ⟨235986275976766994804951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 629296735938045319479869 235986275976766994804951)
              ·
                refine ⟨353979413965150492207427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235986275976766994804951 353979413965150492207427)
                ·
                  refine ⟨530969120947725738311141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353979413965150492207427 530969120947725738311141)
                  ·
                    refine ⟨99556710177698575933339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530969120947725738311141 99556710177698575933339)
                    ·
                      rfl

theorem cell22_290829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_290829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290829 prefixEnd_290829 := by exact prefixLift 290829
  have htrace : WordTrace (prefixWord ++ tailWord_290829) baseStart_290829 baseEnd_290829 := by
    simpa [prefixWord, tailWord_290829, baseEnd_290829] using wordTrace_append hprefix tailTrace_290829
  have hstable : (prefixWord ++ tailWord_290829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290829).length < 2 ^ (prefixWord ++ tailWord_290829).sum := by decide
  have hdescent : baseEnd_290829 < baseStart_290829 := by decide
  rcases family_descends (prefixWord ++ tailWord_290829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290855 : List Nat := [1, 1, 7, 1, 3, 1, 1, 7]
def baseStart_290855 : Nat := 118140960795 + 290855 * 2 ^ 59
def prefixEnd_290855 : Nat := 4983230072969 + 3 ^ 40 * 290855 * 2
def baseEnd_290855 : Nat := 11062845612115908309251

theorem tailTrace_290855 : CollatzResearch.WordTrace tailWord_290855 prefixEnd_290855 11062845612115908309251 := by
  unfold tailWord_290855
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608353361289483924354019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072235574192989282902679 10608353361289483924354019)
  ·
    refine ⟨15912530041934225886531029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608353361289483924354019 15912530041934225886531029)
    ·
      refine ⟨372949922857833419215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15912530041934225886531029 372949922857833419215571)
      ·
        refine ⟨559424884286750128823357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372949922857833419215571 559424884286750128823357)
        ·
          refine ⟨209784331607531298308759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559424884286750128823357 209784331607531298308759)
          ·
            refine ⟨314676497411296947463139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209784331607531298308759 314676497411296947463139)
            ·
              refine ⟨472014746116945421194709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314676497411296947463139 472014746116945421194709)
              ·
                refine ⟨11062845612115908309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 472014746116945421194709 11062845612115908309251)
                ·
                  rfl

theorem cell22_290855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 7].length) (baseStart_290855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290855 prefixEnd_290855 := by exact prefixLift 290855
  have htrace : WordTrace (prefixWord ++ tailWord_290855) baseStart_290855 baseEnd_290855 := by
    simpa [prefixWord, tailWord_290855, baseEnd_290855] using wordTrace_append hprefix tailTrace_290855
  have hstable : (prefixWord ++ tailWord_290855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290855).length < 2 ^ (prefixWord ++ tailWord_290855).sum := by decide
  have hdescent : baseEnd_290855 < baseStart_290855 := by decide
  rcases family_descends (prefixWord ++ tailWord_290855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290864 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_290864 : Nat := 118140960795 + 290864 * 2 ^ 59
def prefixEnd_290864 : Nat := 4983230072969 + 3 ^ 40 * 290864 * 2
def baseEnd_290864 : Nat := 99568691392970151308231

theorem tailTrace_290864 : CollatzResearch.WordTrace tailWord_290864 prefixEnd_290864 99568691392970151308231 := by
  unfold tailWord_290864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304340809128439230715823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7072454412171252307621097 5304340809128439230715823)
  ·
    refine ⟨7956511213692658846073735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5304340809128439230715823 7956511213692658846073735)
    ·
      refine ⟨11934766820538988269110603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7956511213692658846073735 11934766820538988269110603)
      ·
        refine ⟨17902150230808482403665905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11934766820538988269110603 17902150230808482403665905)
        ·
          refine ⟨13426612673106361802749429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17902150230808482403665905 13426612673106361802749429)
          ·
            refine ⟨1258744938103721419007759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13426612673106361802749429 1258744938103721419007759)
            ·
              refine ⟨1888117407155582128511639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258744938103721419007759 1888117407155582128511639)
              ·
                refine ⟨2832176110733373192767459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888117407155582128511639 2832176110733373192767459)
                ·
                  refine ⟨4248264166100059789151189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832176110733373192767459 4248264166100059789151189)
                  ·
                    refine ⟨99568691392970151308231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4248264166100059789151189 99568691392970151308231)
                    ·
                      rfl

theorem cell22_290864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_290864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290864 prefixEnd_290864 := by exact prefixLift 290864
  have htrace : WordTrace (prefixWord ++ tailWord_290864) baseStart_290864 baseEnd_290864 := by
    simpa [prefixWord, tailWord_290864, baseEnd_290864] using wordTrace_append hprefix tailTrace_290864
  have hstable : (prefixWord ++ tailWord_290864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290864).length < 2 ^ (prefixWord ++ tailWord_290864).sum := by decide
  have hdescent : baseEnd_290864 < baseStart_290864 := by decide
  rcases family_descends (prefixWord ++ tailWord_290864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290866 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_290866 : Nat := 118140960795 + 290866 * 2 ^ 59
def prefixEnd_290866 : Nat := 4983230072969 + 3 ^ 40 * 290866 * 2
def baseEnd_290866 : Nat := 33189792011280937586075

theorem tailTrace_290866 : CollatzResearch.WordTrace tailWord_290866 prefixEnd_290866 33189792011280937586075 := by
  unfold tailWord_290866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652188641062408200751113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7072503042833088535336301 2652188641062408200751113)
  ·
    refine ⟨1989141480796806150563335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652188641062408200751113 1989141480796806150563335)
    ·
      refine ⟨2983712221195209225845003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989141480796806150563335 2983712221195209225845003)
      ·
        refine ⟨4475568331792813838767505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983712221195209225845003 4475568331792813838767505)
        ·
          refine ⟨3356676248844610379075629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4475568331792813838767505 3356676248844610379075629)
          ·
            refine ⟨1258753593316728892153361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3356676248844610379075629 1258753593316728892153361)
            ·
              refine ⟨944065194987546669115021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258753593316728892153361 944065194987546669115021)
              ·
                refine ⟨354024448120330000918133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944065194987546669115021 354024448120330000918133)
                ·
                  refine ⟨33189792011280937586075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354024448120330000918133 33189792011280937586075)
                  ·
                    rfl

theorem cell22_290866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_290866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290866 prefixEnd_290866 := by exact prefixLift 290866
  have htrace : WordTrace (prefixWord ++ tailWord_290866) baseStart_290866 baseEnd_290866 := by
    simpa [prefixWord, tailWord_290866, baseEnd_290866] using wordTrace_append hprefix tailTrace_290866
  have hstable : (prefixWord ++ tailWord_290866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290866).length < 2 ^ (prefixWord ++ tailWord_290866).sum := by decide
  have hdescent : baseEnd_290866 < baseStart_290866 := by decide
  rcases family_descends (prefixWord ++ tailWord_290866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290941 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_290941 : Nat := 118140960795 + 290941 * 2 ^ 59
def prefixEnd_290941 : Nat := 4983230072969 + 3 ^ 40 * 290941 * 2
def baseEnd_290941 : Nat := 99595050066567617132995

theorem tailTrace_290941 : CollatzResearch.WordTrace tailWord_290941 prefixEnd_290941 99595050066567617132995 := by
  unfold tailWord_290941
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611490038977920611984677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074326692651947074656451 10611490038977920611984677)
  ·
    refine ⟨1989654382308360114747127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10611490038977920611984677 1989654382308360114747127)
    ·
      refine ⟨2984481573462540172120691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989654382308360114747127 2984481573462540172120691)
      ·
        refine ⟨4476722360193810258181037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984481573462540172120691 4476722360193810258181037)
        ·
          refine ⟨1678770885072678846817889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4476722360193810258181037 1678770885072678846817889)
          ·
            refine ⟨1259078163804509135113417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678770885072678846817889 1259078163804509135113417)
            ·
              refine ⟨944308622853381851335063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259078163804509135113417 944308622853381851335063)
              ·
                refine ⟨1416462934280072777002595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944308622853381851335063 1416462934280072777002595)
                ·
                  refine ⟨2124694401420109165503893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416462934280072777002595 2124694401420109165503893)
                  ·
                    refine ⟨99595050066567617132995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2124694401420109165503893 99595050066567617132995)
                    ·
                      rfl

theorem cell22_290941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_290941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290941 prefixEnd_290941 := by exact prefixLift 290941
  have htrace : WordTrace (prefixWord ++ tailWord_290941) baseStart_290941 baseEnd_290941 := by
    simpa [prefixWord, tailWord_290941, baseEnd_290941] using wordTrace_append hprefix tailTrace_290941
  have hstable : (prefixWord ++ tailWord_290941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290941).length < 2 ^ (prefixWord ++ tailWord_290941).sum := by decide
  have hdescent : baseEnd_290941 < baseStart_290941 := by decide
  rcases family_descends (prefixWord ++ tailWord_290941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290971 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 7, 3]
def baseStart_290971 : Nat := 118140960795 + 290971 * 2 ^ 59
def prefixEnd_290971 : Nat := 4983230072969 + 3 ^ 40 * 290971 * 2
def baseEnd_290971 : Nat := 99605319679657538882903

theorem tailTrace_290971 : CollatzResearch.WordTrace tailWord_290971 prefixEnd_290971 99605319679657538882903 := by
  unfold tailWord_290971
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612584228869235735576767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7075056152579490490384511 10612584228869235735576767)
  ·
    refine ⟨15918876343303853603365151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10612584228869235735576767 15918876343303853603365151)
    ·
      refine ⟨23878314514955780405047727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15918876343303853603365151 23878314514955780405047727)
      ·
        refine ⟨35817471772433670607571591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23878314514955780405047727 35817471772433670607571591)
        ·
          refine ⟨53726207658650505911357387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35817471772433670607571591 53726207658650505911357387)
          ·
            refine ⟨80589311487975758867036081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53726207658650505911357387 80589311487975758867036081)
            ·
              refine ⟨60441983615981819150277061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80589311487975758867036081 60441983615981819150277061)
              ·
                refine ⟨11332871927996591090676949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60441983615981819150277061 11332871927996591090676949)
                ·
                  refine ⟨265614185812420103687741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11332871927996591090676949 265614185812420103687741)
                  ·
                    refine ⟨99605319679657538882903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265614185812420103687741 99605319679657538882903)
                    ·
                      rfl

theorem cell22_290971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].length) (baseStart_290971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290971 prefixEnd_290971 := by exact prefixLift 290971
  have htrace : WordTrace (prefixWord ++ tailWord_290971) baseStart_290971 baseEnd_290971 := by
    simpa [prefixWord, tailWord_290971, baseEnd_290971] using wordTrace_append hprefix tailTrace_290971
  have hstable : (prefixWord ++ tailWord_290971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290971).length < 2 ^ (prefixWord ++ tailWord_290971).sum := by decide
  have hdescent : baseEnd_290971 < baseStart_290971 := by decide
  rcases family_descends (prefixWord ++ tailWord_290971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290977 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_290977 : Nat := 118140960795 + 290977 * 2 ^ 59
def prefixEnd_290977 : Nat := 4983230072969 + 3 ^ 40 * 290977 * 2
def baseEnd_290977 : Nat := 99607373602275523232885

theorem tailTrace_290977 : CollatzResearch.WordTrace tailWord_290977 prefixEnd_290977 99607373602275523232885 := by
  unfold tailWord_290977
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612803066847498760295185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7075202044564999173530123 10612803066847498760295185)
  ·
    refine ⟨7959602300135624070221389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10612803066847498760295185 7959602300135624070221389)
    ·
      refine ⟨2984850862550859026333021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7959602300135624070221389 2984850862550859026333021)
      ·
        refine ⟨1119319073456572134874883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2984850862550859026333021 1119319073456572134874883)
        ·
          refine ⟨1678978610184858202312325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119319073456572134874883 1678978610184858202312325)
          ·
            refine ⟨314808489409660912933561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1678978610184858202312325 314808489409660912933561)
            ·
              refine ⟨236106367057245684700171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314808489409660912933561 236106367057245684700171)
              ·
                refine ⟨354159550585868527050257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236106367057245684700171 354159550585868527050257)
                ·
                  refine ⟨265619662939401395287693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354159550585868527050257 265619662939401395287693)
                  ·
                    refine ⟨99607373602275523232885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265619662939401395287693 99607373602275523232885)
                    ·
                      rfl

theorem cell22_290977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_290977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_290977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_290977 prefixEnd_290977 := by exact prefixLift 290977
  have htrace : WordTrace (prefixWord ++ tailWord_290977) baseStart_290977 baseEnd_290977 := by
    simpa [prefixWord, tailWord_290977, baseEnd_290977] using wordTrace_append hprefix tailTrace_290977
  have hstable : (prefixWord ++ tailWord_290977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290977).length < 2 ^ (prefixWord ++ tailWord_290977).sum := by decide
  have hdescent : baseEnd_290977 < baseStart_290977 := by decide
  rcases family_descends (prefixWord ++ tailWord_290977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291005 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_291005 : Nat := 118140960795 + 291005 * 2 ^ 59
def prefixEnd_291005 : Nat := 4983230072969 + 3 ^ 40 * 291005 * 2
def baseEnd_291005 : Nat := 99616958574492783532799

theorem tailTrace_291005 : CollatzResearch.WordTrace tailWord_291005 prefixEnd_291005 99616958574492783532799 := by
  unfold tailWord_291005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613824310746059542314469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7075882873830706361542979 10613824310746059542314469)
  ·
    refine ⟨1990092058264886164183963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10613824310746059542314469 1990092058264886164183963)
    ·
      refine ⟨2985138087397329246275945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990092058264886164183963 2985138087397329246275945)
      ·
        refine ⟨2238853565547996934706959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985138087397329246275945 2238853565547996934706959)
        ·
          refine ⟨3358280348321995402060439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238853565547996934706959 3358280348321995402060439)
          ·
            refine ⟨5037420522482993103090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358280348321995402060439 5037420522482993103090659)
            ·
              refine ⟨7556130783724489654635989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037420522482993103090659 7556130783724489654635989)
              ·
                refine ⟨177096815243542726280531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7556130783724489654635989 177096815243542726280531)
                ·
                  refine ⟨265645222865314089420797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177096815243542726280531 265645222865314089420797)
                  ·
                    refine ⟨99616958574492783532799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265645222865314089420797 99616958574492783532799)
                    ·
                      rfl

theorem cell22_291005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_291005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291005 prefixEnd_291005 := by exact prefixLift 291005
  have htrace : WordTrace (prefixWord ++ tailWord_291005) baseStart_291005 baseEnd_291005 := by
    simpa [prefixWord, tailWord_291005, baseEnd_291005] using wordTrace_append hprefix tailTrace_291005
  have hstable : (prefixWord ++ tailWord_291005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291005).length < 2 ^ (prefixWord ++ tailWord_291005).sum := by decide
  have hdescent : baseEnd_291005 < baseStart_291005 := by decide
  rcases family_descends (prefixWord ++ tailWord_291005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291016 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_291016 : Nat := 118140960795 + 291016 * 2 ^ 59
def prefixEnd_291016 : Nat := 4983230072969 + 3 ^ 40 * 291016 * 2
def baseEnd_291016 : Nat := 99620724099292421507765

theorem tailTrace_291016 : CollatzResearch.WordTrace tailWord_291016 prefixEnd_291016 99620724099292421507765 := by
  unfold tailWord_291016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307112756853104210482451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7076150342470805613976601 5307112756853104210482451)
  ·
    refine ⟨7960669135279656315723677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307112756853104210482451 7960669135279656315723677)
    ·
      refine ⟨2985250925729871118396379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7960669135279656315723677 2985250925729871118396379)
      ·
        refine ⟨4477876388594806677594569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985250925729871118396379 4477876388594806677594569)
        ·
          refine ⟨3358407291446105008195927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4477876388594806677594569 3358407291446105008195927)
          ·
            refine ⟨5037610937169157512293891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358407291446105008195927 5037610937169157512293891)
            ·
              refine ⟨7556416405753736268440837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037610937169157512293891 7556416405753736268440837)
              ·
                refine ⟨1416828076078825550332657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7556416405753736268440837 1416828076078825550332657)
                ·
                  refine ⟨1062621057059119162749493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416828076078825550332657 1062621057059119162749493)
                  ·
                    refine ⟨99620724099292421507765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1062621057059119162749493 99620724099292421507765)
                    ·
                      rfl

theorem cell22_291016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_291016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291016 prefixEnd_291016 := by exact prefixLift 291016
  have htrace : WordTrace (prefixWord ++ tailWord_291016) baseStart_291016 baseEnd_291016 := by
    simpa [prefixWord, tailWord_291016, baseEnd_291016] using wordTrace_append hprefix tailTrace_291016
  have hstable : (prefixWord ++ tailWord_291016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291016).length < 2 ^ (prefixWord ++ tailWord_291016).sum := by decide
  have hdescent : baseEnd_291016 < baseStart_291016 := by decide
  rcases family_descends (prefixWord ++ tailWord_291016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291018 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_291018 : Nat := 118140960795 + 291018 * 2 ^ 59
def prefixEnd_291018 : Nat := 4983230072969 + 3 ^ 40 * 291018 * 2
def baseEnd_291018 : Nat := 33207136246721694319253

theorem tailTrace_291018 : CollatzResearch.WordTrace tailWord_291018 prefixEnd_291018 33207136246721694319253 := by
  unfold tailWord_291018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653574614924740690634427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7076198973132641841691805 2653574614924740690634427)
  ·
    refine ⟨3980361922387111035951641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2653574614924740690634427 3980361922387111035951641)
    ·
      refine ⟨2985271441790333276963731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3980361922387111035951641 2985271441790333276963731)
      ·
        refine ⟨4477907162685499915445597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985271441790333276963731 4477907162685499915445597)
        ·
          refine ⟨1679215186007062468292099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4477907162685499915445597 1679215186007062468292099)
          ·
            refine ⟨2518822779010593702438149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679215186007062468292099 2518822779010593702438149)
            ·
              refine ⟨472279271064486319207153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2518822779010593702438149 472279271064486319207153)
              ·
                refine ⟨354209453298364739405365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472279271064486319207153 354209453298364739405365)
                ·
                  refine ⟨33207136246721694319253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354209453298364739405365 33207136246721694319253)
                  ·
                    rfl

theorem cell22_291018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_291018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291018 prefixEnd_291018 := by exact prefixLift 291018
  have htrace : WordTrace (prefixWord ++ tailWord_291018) baseStart_291018 baseEnd_291018 := by
    simpa [prefixWord, tailWord_291018, baseEnd_291018] using wordTrace_append hprefix tailTrace_291018
  have hstable : (prefixWord ++ tailWord_291018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291018).length < 2 ^ (prefixWord ++ tailWord_291018).sum := by decide
  have hdescent : baseEnd_291018 < baseStart_291018 := by decide
  rcases family_descends (prefixWord ++ tailWord_291018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291022 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_291022 : Nat := 118140960795 + 291022 * 2 ^ 59
def prefixEnd_291022 : Nat := 4983230072969 + 3 ^ 40 * 291022 * 2
def baseEnd_291022 : Nat := 99622778021910405857747

theorem tailTrace_291022 : CollatzResearch.WordTrace tailWord_291022 prefixEnd_291022 99622778021910405857747 := by
  unfold tailWord_291022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326805543960558930710415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7076296234456314297122213 1326805543960558930710415)
  ·
    refine ⟨1990208315940838396065623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326805543960558930710415 1990208315940838396065623)
    ·
      refine ⟨2985312473911257594098435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990208315940838396065623 2985312473911257594098435)
      ·
        refine ⟨4477968710866886391147653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985312473911257594098435 4477968710866886391147653)
        ·
          refine ⟨839619133287541198340185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4477968710866886391147653 839619133287541198340185)
          ·
            refine ⟨629714349965655898755139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839619133287541198340185 629714349965655898755139)
            ·
              refine ⟨944571524948483848132709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629714349965655898755139 944571524948483848132709)
              ·
                refine ⟨177107160927840721524883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 944571524948483848132709 177107160927840721524883)
                ·
                  refine ⟨265660741391761082287325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177107160927840721524883 265660741391761082287325)
                  ·
                    refine ⟨99622778021910405857747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265660741391761082287325 99622778021910405857747)
                    ·
                      rfl

theorem cell22_291022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_291022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291022 prefixEnd_291022 := by exact prefixLift 291022
  have htrace : WordTrace (prefixWord ++ tailWord_291022) baseStart_291022 baseEnd_291022 := by
    simpa [prefixWord, tailWord_291022, baseEnd_291022] using wordTrace_append hprefix tailTrace_291022
  have hstable : (prefixWord ++ tailWord_291022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291022).length < 2 ^ (prefixWord ++ tailWord_291022).sum := by decide
  have hdescent : baseEnd_291022 < baseStart_291022 := by decide
  rcases family_descends (prefixWord ++ tailWord_291022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291048 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_291048 : Nat := 118140960795 + 291048 * 2 ^ 59
def prefixEnd_291048 : Nat := 4983230072969 + 3 ^ 40 * 291048 * 2
def baseEnd_291048 : Nat := 99631678353255004707667

theorem tailTrace_291048 : CollatzResearch.WordTrace tailWord_291048 prefixEnd_291048 99631678353255004707667 := by
  unfold tailWord_291048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307696324795138943064899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7076928433060185257419865 5307696324795138943064899)
  ·
    refine ⟨7961544487192708414597349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307696324795138943064899 7961544487192708414597349)
    ·
      refine ⟨1492789591348632827737003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7961544487192708414597349 1492789591348632827737003)
      ·
        refine ⟨2239184387022949241605505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492789591348632827737003 2239184387022949241605505)
        ·
          refine ⟨1679388290267211931204129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2239184387022949241605505 1679388290267211931204129)
          ·
            refine ⟨1259541217700408948403097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679388290267211931204129 1259541217700408948403097)
            ·
              refine ⟨944655913275306711302323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259541217700408948403097 944655913275306711302323)
              ·
                refine ⟨1416983869912960066953485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944655913275306711302323 1416983869912960066953485)
                ·
                  refine ⟨531368951217360025107557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1416983869912960066953485 531368951217360025107557)
                  ·
                    refine ⟨99631678353255004707667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 531368951217360025107557 99631678353255004707667)
                    ·
                      rfl

theorem cell22_291048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_291048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291048 prefixEnd_291048 := by exact prefixLift 291048
  have htrace : WordTrace (prefixWord ++ tailWord_291048) baseStart_291048 baseEnd_291048 := by
    simpa [prefixWord, tailWord_291048, baseEnd_291048] using wordTrace_append hprefix tailTrace_291048
  have hstable : (prefixWord ++ tailWord_291048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291048).length < 2 ^ (prefixWord ++ tailWord_291048).sum := by decide
  have hdescent : baseEnd_291048 < baseStart_291048 := by decide
  rcases family_descends (prefixWord ++ tailWord_291048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291080 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_291080 : Nat := 118140960795 + 291080 * 2 ^ 59
def prefixEnd_291080 : Nat := 4983230072969 + 3 ^ 40 * 291080 * 2
def baseEnd_291080 : Nat := 33214210869072529302523

theorem tailTrace_291080 : CollatzResearch.WordTrace tailWord_291080 prefixEnd_291080 33214210869072529302523 := by
  unfold tailWord_291080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308279892737173675647347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7077706523649564900863129 5308279892737173675647347)
  ·
    refine ⟨7962419839105760513471021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5308279892737173675647347 7962419839105760513471021)
    ·
      refine ⟨2985907439664660192551633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7962419839105760513471021 2985907439664660192551633)
      ·
        refine ⟨2239430579748495144413725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985907439664660192551633 2239430579748495144413725)
        ·
          refine ⟨839786467405685679155147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2239430579748495144413725 839786467405685679155147)
          ·
            refine ⟨1259679701108528518732721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839786467405685679155147 1259679701108528518732721)
            ·
              refine ⟨944759775831396389049541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259679701108528518732721 944759775831396389049541)
              ·
                refine ⟨177142457968386822946789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 944759775831396389049541 177142457968386822946789)
                ·
                  refine ⟨33214210869072529302523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177142457968386822946789 33214210869072529302523)
                  ·
                    rfl

theorem cell22_291080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_291080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291080 prefixEnd_291080 := by exact prefixLift 291080
  have htrace : WordTrace (prefixWord ++ tailWord_291080) baseStart_291080 baseEnd_291080 := by
    simpa [prefixWord, tailWord_291080, baseEnd_291080] using wordTrace_append hprefix tailTrace_291080
  have hstable : (prefixWord ++ tailWord_291080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291080).length < 2 ^ (prefixWord ++ tailWord_291080).sum := by decide
  have hdescent : baseEnd_291080 < baseStart_291080 := by decide
  rcases family_descends (prefixWord ++ tailWord_291080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291095 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 5]
def baseStart_291095 : Nat := 118140960795 + 291095 * 2 ^ 59
def prefixEnd_291095 : Nat := 4983230072969 + 3 ^ 40 * 291095 * 2
def baseEnd_291095 : Nat := 99647767413762548782523

theorem tailTrace_291095 : CollatzResearch.WordTrace tailWord_291095 prefixEnd_291095 99647767413762548782523 := by
  unfold tailWord_291095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617106880420004913090739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7078071253613336608727159 10617106880420004913090739)
  ·
    refine ⟨15925660320630007369636109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10617106880420004913090739 15925660320630007369636109)
    ·
      refine ⟨5972122620236252763613541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15925660320630007369636109 5972122620236252763613541)
      ·
        refine ⟨1119772991294297393177539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5972122620236252763613541 1119772991294297393177539)
        ·
          refine ⟨1679659486941446089766309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119772991294297393177539 1679659486941446089766309)
          ·
            refine ⟨314936153801521141831183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1679659486941446089766309 314936153801521141831183)
            ·
              refine ⟨472404230702281712746775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314936153801521141831183 472404230702281712746775)
              ·
                refine ⟨708606346053422569120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472404230702281712746775 708606346053422569120163)
                ·
                  refine ⟨1062909519080133853680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708606346053422569120163 1062909519080133853680245)
                  ·
                    refine ⟨99647767413762548782523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1062909519080133853680245 99647767413762548782523)
                    ·
                      rfl

theorem cell22_291095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_291095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291095 prefixEnd_291095 := by exact prefixLift 291095
  have htrace : WordTrace (prefixWord ++ tailWord_291095) baseStart_291095 baseEnd_291095 := by
    simpa [prefixWord, tailWord_291095, baseEnd_291095] using wordTrace_append hprefix tailTrace_291095
  have hstable : (prefixWord ++ tailWord_291095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291095).length < 2 ^ (prefixWord ++ tailWord_291095).sum := by decide
  have hdescent : baseEnd_291095 < baseStart_291095 := by decide
  rcases family_descends (prefixWord ++ tailWord_291095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291108 : List Nat := [2, 3, 1, 3, 1, 3, 1, 8]
def baseStart_291108 : Nat := 118140960795 + 291108 * 2 ^ 59
def prefixEnd_291108 : Nat := 4983230072969 + 3 ^ 40 * 291108 * 2
def baseEnd_291108 : Nat := 11072468619937205356387

theorem tailTrace_291108 : CollatzResearch.WordTrace tailWord_291108 prefixEnd_291108 11072468619937205356387 := by
  unfold tailWord_291108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308790514686454066656989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7078387352915272088875985 5308790514686454066656989)
  ·
    refine ⟨1990796443007420274996371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5308790514686454066656989 1990796443007420274996371)
    ·
      refine ⟨2986194664511130412494557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990796443007420274996371 2986194664511130412494557)
      ·
        refine ⟨1119822999191673904685459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2986194664511130412494557 1119822999191673904685459)
        ·
          refine ⟨1679734498787510857028189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119822999191673904685459 1679734498787510857028189)
          ·
            refine ⟨629900437045316571385571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1679734498787510857028189 629900437045316571385571)
            ·
              refine ⟨944850655567974857078357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629900437045316571385571 944850655567974857078357)
              ·
                refine ⟨11072468619937205356387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 944850655567974857078357 11072468619937205356387)
                ·
                  rfl

theorem cell22_291108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_291108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291108 prefixEnd_291108 := by exact prefixLift 291108
  have htrace : WordTrace (prefixWord ++ tailWord_291108) baseStart_291108 baseEnd_291108 := by
    simpa [prefixWord, tailWord_291108, baseEnd_291108] using wordTrace_append hprefix tailTrace_291108
  have hstable : (prefixWord ++ tailWord_291108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291108).length < 2 ^ (prefixWord ++ tailWord_291108).sum := by decide
  have hdescent : baseEnd_291108 < baseStart_291108 := by decide
  rcases family_descends (prefixWord ++ tailWord_291108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291114 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_291114 : Nat := 118140960795 + 291114 * 2 ^ 59
def prefixEnd_291114 : Nat := 4983230072969 + 3 ^ 40 * 291114 * 2
def baseEnd_291114 : Nat := 33218090500684277519155

theorem tailTrace_291114 : CollatzResearch.WordTrace tailWord_291114 prefixEnd_291114 33218090500684277519155 := by
  unfold tailWord_291114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2654449966837792789508099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7078533244900780772021597 2654449966837792789508099)
  ·
    refine ⟨3981674950256689184262149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2654449966837792789508099 3981674950256689184262149)
    ·
      refine ⟨746564053173129222049153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3981674950256689184262149 746564053173129222049153)
      ·
        refine ⟨559923039879846916536865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746564053173129222049153 559923039879846916536865)
        ·
          refine ⟨419942279909885187402649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559923039879846916536865 419942279909885187402649)
          ·
            refine ⟨314956709932413890551987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419942279909885187402649 314956709932413890551987)
            ·
              refine ⟨472435064898620835827981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314956709932413890551987 472435064898620835827981)
              ·
                refine ⟨177163149336982813435493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472435064898620835827981 177163149336982813435493)
                ·
                  refine ⟨33218090500684277519155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177163149336982813435493 33218090500684277519155)
                  ·
                    rfl

theorem cell22_291114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_291114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291114 prefixEnd_291114 := by exact prefixLift 291114
  have htrace : WordTrace (prefixWord ++ tailWord_291114) baseStart_291114 baseEnd_291114 := by
    simpa [prefixWord, tailWord_291114, baseEnd_291114] using wordTrace_append hprefix tailTrace_291114
  have hstable : (prefixWord ++ tailWord_291114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291114).length < 2 ^ (prefixWord ++ tailWord_291114).sum := by decide
  have hdescent : baseEnd_291114 < baseStart_291114 := by decide
  rcases family_descends (prefixWord ++ tailWord_291114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291232 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_291232 : Nat := 118140960795 + 291232 * 2 ^ 59
def prefixEnd_291232 : Nat := 4983230072969 + 3 ^ 40 * 291232 * 2
def baseEnd_291232 : Nat := 33231555104513286035701

theorem tailTrace_291232 : CollatzResearch.WordTrace tailWord_291232 prefixEnd_291232 33231555104513286035701 := by
  unfold tailWord_291232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5311051840461838655413975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7081402453949118207218633 5311051840461838655413975)
  ·
    refine ⟨7966577760692757983120963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5311051840461838655413975 7966577760692757983120963)
    ·
      refine ⟨11949866641039136974681445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966577760692757983120963 11949866641039136974681445)
      ·
        refine ⟨2240599995194838182752771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11949866641039136974681445 2240599995194838182752771)
        ·
          refine ⟨3360899992792257274129157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240599995194838182752771 3360899992792257274129157)
          ·
            refine ⟨630168748648548238899217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3360899992792257274129157 630168748648548238899217)
            ·
              refine ⟨472626561486411179174413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630168748648548238899217 472626561486411179174413)
              ·
                refine ⟨177234960557404192190405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472626561486411179174413 177234960557404192190405)
                ·
                  refine ⟨33231555104513286035701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177234960557404192190405 33231555104513286035701)
                  ·
                    rfl

theorem cell22_291232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_291232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291232 prefixEnd_291232 := by exact prefixLift 291232
  have htrace : WordTrace (prefixWord ++ tailWord_291232) baseStart_291232 baseEnd_291232 := by
    simpa [prefixWord, tailWord_291232, baseEnd_291232] using wordTrace_append hprefix tailTrace_291232
  have hstable : (prefixWord ++ tailWord_291232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291232).length < 2 ^ (prefixWord ++ tailWord_291232).sum := by decide
  have hdescent : baseEnd_291232 < baseStart_291232 := by decide
  rcases family_descends (prefixWord ++ tailWord_291232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291273 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_291273 : Nat := 118140960795 + 291273 * 2 ^ 59
def prefixEnd_291273 : Nat := 4983230072969 + 3 ^ 40 * 291273 * 2
def baseEnd_291273 : Nat := 99708700451429417831977

theorem tailTrace_291273 : CollatzResearch.WordTrace tailWord_291273 prefixEnd_291273 99708700451429417831977 := by
  unfold tailWord_291273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623599073775141313070473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7082399382516760875380315 10623599073775141313070473)
  ·
    refine ⟨7967699305331355984802855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10623599073775141313070473 7967699305331355984802855)
    ·
      refine ⟨11951548957997033977204283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7967699305331355984802855 11951548957997033977204283)
      ·
        refine ⟨17927323436995550965806425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11951548957997033977204283 17927323436995550965806425)
        ·
          refine ⟨13445492577746663224354819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17927323436995550965806425 13445492577746663224354819)
          ·
            refine ⟨20168238866619994836532229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13445492577746663224354819 20168238866619994836532229)
            ·
              refine ⟨3781544787491249031849793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20168238866619994836532229 3781544787491249031849793)
              ·
                refine ⟨2836158590618436773887345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781544787491249031849793 2836158590618436773887345)
                ·
                  refine ⟨2127118942963827580415509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836158590618436773887345 2127118942963827580415509)
                  ·
                    refine ⟨99708700451429417831977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2127118942963827580415509 99708700451429417831977)
                    ·
                      rfl

theorem cell22_291273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_291273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291273 prefixEnd_291273 := by exact prefixLift 291273
  have htrace : WordTrace (prefixWord ++ tailWord_291273) baseStart_291273 baseEnd_291273 := by
    simpa [prefixWord, tailWord_291273, baseEnd_291273] using wordTrace_append hprefix tailTrace_291273
  have hstable : (prefixWord ++ tailWord_291273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291273).length < 2 ^ (prefixWord ++ tailWord_291273).sum := by decide
  have hdescent : baseEnd_291273 < baseStart_291273 := by decide
  rcases family_descends (prefixWord ++ tailWord_291273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291309 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_291309 : Nat := 118140960795 + 291309 * 2 ^ 59
def prefixEnd_291309 : Nat := 4983230072969 + 3 ^ 40 * 291309 * 2
def baseEnd_291309 : Nat := 99721023987137323931867

theorem tailTrace_291309 : CollatzResearch.WordTrace tailWord_291309 prefixEnd_291309 99721023987137323931867 := by
  unfold tailWord_291309
  simp only [CollatzResearch.WordTrace]
  refine ⟨10624912101644719461380981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7083274734429812974253987 10624912101644719461380981)
  ·
    refine ⟨996085509529192449504467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10624912101644719461380981 996085509529192449504467)
    ·
      refine ⟨1494128264293788674256701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996085509529192449504467 1494128264293788674256701)
      ·
        refine ⟨560298099110170752846263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1494128264293788674256701 560298099110170752846263)
        ·
          refine ⟨840447148665256129269395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560298099110170752846263 840447148665256129269395)
          ·
            refine ⟨1260670722997884193904093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840447148665256129269395 1260670722997884193904093)
            ·
              refine ⟨472751521124206572714035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1260670722997884193904093 472751521124206572714035)
              ·
                refine ⟨709127281686309859071053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472751521124206572714035 709127281686309859071053)
                ·
                  refine ⟨265922730632366197151645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709127281686309859071053 265922730632366197151645)
                  ·
                    refine ⟨99721023987137323931867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265922730632366197151645 99721023987137323931867)
                    ·
                      rfl

theorem cell22_291309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_291309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291309 prefixEnd_291309 := by exact prefixLift 291309
  have htrace : WordTrace (prefixWord ++ tailWord_291309) baseStart_291309 baseEnd_291309 := by
    simpa [prefixWord, tailWord_291309, baseEnd_291309] using wordTrace_append hprefix tailTrace_291309
  have hstable : (prefixWord ++ tailWord_291309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291309).length < 2 ^ (prefixWord ++ tailWord_291309).sum := by decide
  have hdescent : baseEnd_291309 < baseStart_291309 := by decide
  rcases family_descends (prefixWord ++ tailWord_291309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291360 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_291360 : Nat := 118140960795 + 291360 * 2 ^ 59
def prefixEnd_291360 : Nat := 4983230072969 + 3 ^ 40 * 291360 * 2
def baseEnd_291360 : Nat := 99738482329390190906711

theorem tailTrace_291360 : CollatzResearch.WordTrace tailWord_291360 prefixEnd_291360 99738482329390190906711 := by
  unfold tailWord_291360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313386112229977585743767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7084514816306636780991689 5313386112229977585743767)
  ·
    refine ⟨7970079168344966378615651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5313386112229977585743767 7970079168344966378615651)
    ·
      refine ⟨11955118752517449567923477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970079168344966378615651 11955118752517449567923477)
      ·
        refine ⟨560396191524255448496413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11955118752517449567923477 560396191524255448496413)
        ·
          refine ⟨210148571821595793186155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560396191524255448496413 210148571821595793186155)
          ·
            refine ⟨315222857732393689779233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210148571821595793186155 315222857732393689779233)
            ·
              refine ⟨236417143299295267334425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315222857732393689779233 236417143299295267334425)
              ·
                refine ⟨177312857474471450500819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236417143299295267334425 177312857474471450500819)
                ·
                  refine ⟨265969286211707175751229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177312857474471450500819 265969286211707175751229)
                  ·
                    refine ⟨99738482329390190906711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265969286211707175751229 99738482329390190906711)
                    ·
                      rfl

theorem cell22_291360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_291360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291360 prefixEnd_291360 := by exact prefixLift 291360
  have htrace : WordTrace (prefixWord ++ tailWord_291360) baseStart_291360 baseEnd_291360 := by
    simpa [prefixWord, tailWord_291360, baseEnd_291360] using wordTrace_append hprefix tailTrace_291360
  have hstable : (prefixWord ++ tailWord_291360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291360).length < 2 ^ (prefixWord ++ tailWord_291360).sum := by decide
  have hdescent : baseEnd_291360 < baseStart_291360 := by decide
  rcases family_descends (prefixWord ++ tailWord_291360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291397 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_291397 : Nat := 118140960795 + 291397 * 2 ^ 59
def prefixEnd_291397 : Nat := 4983230072969 + 3 ^ 40 * 291397 * 2
def baseEnd_291397 : Nat := 99751148185534427731597

theorem tailTrace_291397 : CollatzResearch.WordTrace tailWord_291397 prefixEnd_291397 99751148185534427731597 := by
  unfold tailWord_291397
  simp only [CollatzResearch.WordTrace]
  refine ⟨10628121725325910490584445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7085414483550606993722963 10628121725325910490584445)
  ·
    refine ⟨3985545646997216433969167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10628121725325910490584445 3985545646997216433969167)
    ·
      refine ⟨5978318470495824650953751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985545646997216433969167 5978318470495824650953751)
      ·
        refine ⟨8967477705743736976430627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978318470495824650953751 8967477705743736976430627)
        ·
          refine ⟨13451216558615605464645941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967477705743736976430627 13451216558615605464645941)
          ·
            refine ⟨1261051552370213012310557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13451216558615605464645941 1261051552370213012310557)
            ·
              refine ⟨472894332138829879616459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1261051552370213012310557 472894332138829879616459)
              ·
                refine ⟨709341498208244819424689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472894332138829879616459 709341498208244819424689)
                ·
                  refine ⟨532006123656183614568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709341498208244819424689 532006123656183614568517)
                  ·
                    refine ⟨99751148185534427731597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532006123656183614568517 99751148185534427731597)
                    ·
                      rfl

theorem cell22_291397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_291397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291397 prefixEnd_291397 := by exact prefixLift 291397
  have htrace : WordTrace (prefixWord ++ tailWord_291397) baseStart_291397 baseEnd_291397 := by
    simpa [prefixWord, tailWord_291397, baseEnd_291397] using wordTrace_append hprefix tailTrace_291397
  have hstable : (prefixWord ++ tailWord_291397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291397).length < 2 ^ (prefixWord ++ tailWord_291397).sum := by decide
  have hdescent : baseEnd_291397 < baseStart_291397 := by decide
  rcases family_descends (prefixWord ++ tailWord_291397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291446 : List Nat := [5, 1, 1, 2, 3, 2, 2, 6]
def baseStart_291446 : Nat := 118140960795 + 291446 * 2 ^ 59
def prefixEnd_291446 : Nat := 4983230072969 + 3 ^ 40 * 291446 * 2
def baseEnd_291446 : Nat := 11085324654101625917383

theorem tailTrace_291446 : CollatzResearch.WordTrace tailWord_291446 prefixEnd_291446 11085324654101625917383 := by
  unfold tailWord_291446
  simp only [CollatzResearch.WordTrace]
  refine ⟨664369306384274491194887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7086605934765594572745461 664369306384274491194887)
  ·
    refine ⟨996553959576411736792331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664369306384274491194887 996553959576411736792331)
    ·
      refine ⟨1494830939364617605188497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996553959576411736792331 1494830939364617605188497)
      ·
        refine ⟨1121123204523463203891373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1494830939364617605188497 1121123204523463203891373)
        ·
          refine ⟨420421201696298701459265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1121123204523463203891373 420421201696298701459265)
          ·
            refine ⟨315315901272224026094449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420421201696298701459265 315315901272224026094449)
            ·
              refine ⟨236486925954168019570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315315901272224026094449 236486925954168019570837)
              ·
                refine ⟨11085324654101625917383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236486925954168019570837 11085324654101625917383)
                ·
                  rfl

theorem cell22_291446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_291446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291446 prefixEnd_291446 := by exact prefixLift 291446
  have htrace : WordTrace (prefixWord ++ tailWord_291446) baseStart_291446 baseEnd_291446 := by
    simpa [prefixWord, tailWord_291446, baseEnd_291446] using wordTrace_append hprefix tailTrace_291446
  have hstable : (prefixWord ++ tailWord_291446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291446).length < 2 ^ (prefixWord ++ tailWord_291446).sum := by decide
  have hdescent : baseEnd_291446 < baseStart_291446 := by decide
  rcases family_descends (prefixWord ++ tailWord_291446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291455 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_291455 : Nat := 118140960795 + 291455 * 2 ^ 59
def prefixEnd_291455 : Nat := 4983230072969 + 3 ^ 40 * 291455 * 2
def baseEnd_291455 : Nat := 99771002770841609781419

theorem tailTrace_291455 : CollatzResearch.WordTrace tailWord_291455 prefixEnd_291455 99771002770841609781419 := by
  unfold tailWord_291455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630237159115786396195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086824772743857597463879 10630237159115786396195819)
  ·
    refine ⟨15945355738673679594293729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10630237159115786396195819 15945355738673679594293729)
    ·
      refine ⟨11959016804005259695720297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15945355738673679594293729 11959016804005259695720297)
      ·
        refine ⟨8969262603003944771790223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11959016804005259695720297 8969262603003944771790223)
        ·
          refine ⟨13453893904505917157685335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8969262603003944771790223 13453893904505917157685335)
          ·
            refine ⟨20180840856758875736528003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13453893904505917157685335 20180840856758875736528003)
            ·
              refine ⟨30271261285138313604792005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20180840856758875736528003 30271261285138313604792005)
              ·
                refine ⟨5675861490963433800898501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30271261285138313604792005 5675861490963433800898501)
                ·
                  refine ⟨1064224029555643837668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5675861490963433800898501 1064224029555643837668469)
                  ·
                    refine ⟨99771002770841609781419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1064224029555643837668469 99771002770841609781419)
                    ·
                      rfl

theorem cell22_291455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_291455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291455 prefixEnd_291455 := by exact prefixLift 291455
  have htrace : WordTrace (prefixWord ++ tailWord_291455) baseStart_291455 baseEnd_291455 := by
    simpa [prefixWord, tailWord_291455, baseEnd_291455] using wordTrace_append hprefix tailTrace_291455
  have hstable : (prefixWord ++ tailWord_291455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291455).length < 2 ^ (prefixWord ++ tailWord_291455).sum := by decide
  have hdescent : baseEnd_291455 < baseStart_291455 := by decide
  rcases family_descends (prefixWord ++ tailWord_291455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291461 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_291461 : Nat := 118140960795 + 291461 * 2 ^ 59
def prefixEnd_291461 : Nat := 4983230072969 + 3 ^ 40 * 291461 * 2
def baseEnd_291461 : Nat := 99773056693459594131401

theorem tailTrace_291461 : CollatzResearch.WordTrace tailWord_291461 prefixEnd_291461 99773056693459594131401 := by
  unfold tailWord_291461
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630455997094049420914237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086970664729366280609491 10630455997094049420914237)
  ·
    refine ⟨3986420998910268532842839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10630455997094049420914237 3986420998910268532842839)
    ·
      refine ⟨5979631498365402799264259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3986420998910268532842839 5979631498365402799264259)
      ·
        refine ⟨8969447247548104198896389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979631498365402799264259 8969447247548104198896389)
        ·
          refine ⟨1681771358915269537293073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8969447247548104198896389 1681771358915269537293073)
          ·
            refine ⟨1261328519186452152969805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1681771358915269537293073 1261328519186452152969805)
            ·
              refine ⟨472998194694919557363677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1261328519186452152969805 472998194694919557363677)
              ·
                refine ⟨177374323010594834011379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472998194694919557363677 177374323010594834011379)
                ·
                  refine ⟨266061484515892251017069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177374323010594834011379 266061484515892251017069)
                  ·
                    refine ⟨99773056693459594131401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266061484515892251017069 99773056693459594131401)
                    ·
                      rfl

theorem cell22_291461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_291461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291461 prefixEnd_291461 := by exact prefixLift 291461
  have htrace : WordTrace (prefixWord ++ tailWord_291461) baseStart_291461 baseEnd_291461 := by
    simpa [prefixWord, tailWord_291461, baseEnd_291461] using wordTrace_append hprefix tailTrace_291461
  have hstable : (prefixWord ++ tailWord_291461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291461).length < 2 ^ (prefixWord ++ tailWord_291461).sum := by decide
  have hdescent : baseEnd_291461 < baseStart_291461 := by decide
  rcases family_descends (prefixWord ++ tailWord_291461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291517 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_291517 : Nat := 118140960795 + 291517 * 2 ^ 59
def prefixEnd_291517 : Nat := 4983230072969 + 3 ^ 40 * 291517 * 2
def baseEnd_291517 : Nat := 99792226637894114731229

theorem tailTrace_291517 : CollatzResearch.WordTrace tailWord_291517 prefixEnd_291517 99792226637894114731229 := by
  unfold tailWord_291517
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632498484891170984952805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7088332323260780656635203 10632498484891170984952805)
  ·
    refine ⟨1993593465917094559678651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10632498484891170984952805 1993593465917094559678651)
    ·
      refine ⟨2990390198875641839517977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1993593465917094559678651 2990390198875641839517977)
      ·
        refine ⟨2242792649156731379638483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2990390198875641839517977 2242792649156731379638483)
        ·
          refine ⟨3364188973735097069457725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242792649156731379638483 3364188973735097069457725)
          ·
            refine ⟨1261570865150661401046647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3364188973735097069457725 1261570865150661401046647)
            ·
              refine ⟨1892356297725992101569971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261570865150661401046647 1892356297725992101569971)
              ·
                refine ⟨2838534446588988152354957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892356297725992101569971 2838534446588988152354957)
                ·
                  refine ⟨1064450417470870557133109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2838534446588988152354957 1064450417470870557133109)
                  ·
                    refine ⟨99792226637894114731229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1064450417470870557133109 99792226637894114731229)
                    ·
                      rfl

theorem cell22_291517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_291517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291517 prefixEnd_291517 := by exact prefixLift 291517
  have htrace : WordTrace (prefixWord ++ tailWord_291517) baseStart_291517 baseEnd_291517 := by
    simpa [prefixWord, tailWord_291517, baseEnd_291517] using wordTrace_append hprefix tailTrace_291517
  have hstable : (prefixWord ++ tailWord_291517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291517).length < 2 ^ (prefixWord ++ tailWord_291517).sum := by decide
  have hdescent : baseEnd_291517 < baseStart_291517 := by decide
  rcases family_descends (prefixWord ++ tailWord_291517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291566 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_291566 : Nat := 118140960795 + 291566 * 2 ^ 59
def prefixEnd_291566 : Nat := 4983230072969 + 3 ^ 40 * 291566 * 2
def baseEnd_291566 : Nat := 99809000339274320256079

theorem tailTrace_291566 : CollatzResearch.WordTrace tailWord_291566 prefixEnd_291566 99809000339274320256079 := by
  unfold tailWord_291566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329285707714206544185819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7089523774475768235657701 1329285707714206544185819)
  ·
    refine ⟨1993928561571309816278729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329285707714206544185819 1993928561571309816278729)
    ·
      refine ⟨1495446421178482362209047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993928561571309816278729 1495446421178482362209047)
      ·
        refine ⟨2243169631767723543313571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495446421178482362209047 2243169631767723543313571)
        ·
          refine ⟨3364754447651585314970357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243169631767723543313571 3364754447651585314970357)
          ·
            refine ⟨315445729467336123278471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3364754447651585314970357 315445729467336123278471)
            ·
              refine ⟨473168594201004184917707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315445729467336123278471 473168594201004184917707)
              ·
                refine ⟨709752891301506277376561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473168594201004184917707 709752891301506277376561)
                ·
                  refine ⟨532314668476129708032421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709752891301506277376561 532314668476129708032421)
                  ·
                    refine ⟨99809000339274320256079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532314668476129708032421 99809000339274320256079)
                    ·
                      rfl

theorem cell22_291566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_291566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291566 prefixEnd_291566 := by exact prefixLift 291566
  have htrace : WordTrace (prefixWord ++ tailWord_291566) baseStart_291566 baseEnd_291566 := by
    simpa [prefixWord, tailWord_291566, baseEnd_291566] using wordTrace_append hprefix tailTrace_291566
  have hstable : (prefixWord ++ tailWord_291566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291566).length < 2 ^ (prefixWord ++ tailWord_291566).sum := by decide
  have hdescent : baseEnd_291566 < baseStart_291566 := by decide
  rcases family_descends (prefixWord ++ tailWord_291566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291572 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_291572 : Nat := 118140960795 + 291572 * 2 ^ 59
def prefixEnd_291572 : Nat := 4983230072969 + 3 ^ 40 * 291572 * 2
def baseEnd_291572 : Nat := 99811054261892304606061

theorem tailTrace_291572 : CollatzResearch.WordTrace tailWord_291572 prefixEnd_291572 99811054261892304606061 := by
  unfold tailWord_291572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317252249845957689102485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7089669666461276918803313 5317252249845957689102485)
  ·
    refine ⟨249246199211529266676679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5317252249845957689102485 249246199211529266676679)
    ·
      refine ⟨373869298817293900015019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249246199211529266676679 373869298817293900015019)
      ·
        refine ⟨560803948225940850022529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373869298817293900015019 560803948225940850022529)
        ·
          refine ⟨420602961169455637516897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560803948225940850022529 420602961169455637516897)
          ·
            refine ⟨315452220877091728137673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420602961169455637516897 315452220877091728137673)
            ·
              refine ⟨236589165657818796103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315452220877091728137673 236589165657818796103255)
              ·
                refine ⟨354883748486728194154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236589165657818796103255 354883748486728194154883)
                ·
                  refine ⟨532325622730092291232325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354883748486728194154883 532325622730092291232325)
                  ·
                    refine ⟨99811054261892304606061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532325622730092291232325 99811054261892304606061)
                    ·
                      rfl

theorem cell22_291572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_291572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291572 prefixEnd_291572 := by exact prefixLift 291572
  have htrace : WordTrace (prefixWord ++ tailWord_291572) baseStart_291572 baseEnd_291572 := by
    simpa [prefixWord, tailWord_291572, baseEnd_291572] using wordTrace_append hprefix tailTrace_291572
  have hstable : (prefixWord ++ tailWord_291572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291572).length < 2 ^ (prefixWord ++ tailWord_291572).sum := by decide
  have hdescent : baseEnd_291572 < baseStart_291572 := by decide
  rcases family_descends (prefixWord ++ tailWord_291572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291630 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_291630 : Nat := 118140960795 + 291630 * 2 ^ 59
def prefixEnd_291630 : Nat := 4983230072969 + 3 ^ 40 * 291630 * 2
def baseEnd_291630 : Nat := 99830908847199486655883

theorem tailTrace_291630 : CollatzResearch.WordTrace tailWord_291630 prefixEnd_291630 99830908847199486655883 := by
  unfold tailWord_291630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329577491685223910477043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7091079955654527522544229 1329577491685223910477043)
  ·
    refine ⟨1994366237527835865715565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329577491685223910477043 1994366237527835865715565)
    ·
      refine ⟨747887339072938449643337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1994366237527835865715565 747887339072938449643337)
      ·
        refine ⟨560915504304703837232503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 747887339072938449643337 560915504304703837232503)
        ·
          refine ⟨841373256457055755848755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560915504304703837232503 841373256457055755848755)
          ·
            refine ⟨1262059884685583633773133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841373256457055755848755 1262059884685583633773133)
            ·
              refine ⟨473272456757093862664925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1262059884685583633773133 473272456757093862664925)
              ·
                refine ⟨177477171283910198499347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473272456757093862664925 177477171283910198499347)
                ·
                  refine ⟨266215756925865297749021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177477171283910198499347 266215756925865297749021)
                  ·
                    refine ⟨99830908847199486655883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266215756925865297749021 99830908847199486655883)
                    ·
                      rfl

theorem cell22_291630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_291630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291630 prefixEnd_291630 := by exact prefixLift 291630
  have htrace : WordTrace (prefixWord ++ tailWord_291630) baseStart_291630 baseEnd_291630 := by
    simpa [prefixWord, tailWord_291630, baseEnd_291630] using wordTrace_append hprefix tailTrace_291630
  have hstable : (prefixWord ++ tailWord_291630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291630).length < 2 ^ (prefixWord ++ tailWord_291630).sum := by decide
  have hdescent : baseEnd_291630 < baseStart_291630 := by decide
  rcases family_descends (prefixWord ++ tailWord_291630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291639 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 1, 4]
def baseStart_291639 : Nat := 118140960795 + 291639 * 2 ^ 59
def prefixEnd_291639 : Nat := 4983230072969 + 3 ^ 40 * 291639 * 2
def baseEnd_291639 : Nat := 99833989731126463180855

theorem tailTrace_291639 : CollatzResearch.WordTrace tailWord_291639 prefixEnd_291639 99833989731126463180855 := by
  unfold tailWord_291639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10636948190449185820893971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7091298793632790547262647 10636948190449185820893971)
  ·
    refine ⟨15955422285673778731340957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10636948190449185820893971 15955422285673778731340957)
    ·
      refine ⟨5983283357127667024252859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15955422285673778731340957 5983283357127667024252859)
      ·
        refine ⟨8974925035691500536379289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5983283357127667024252859 8974925035691500536379289)
        ·
          refine ⟨6731193776768625402284467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8974925035691500536379289 6731193776768625402284467)
          ·
            refine ⟨10096790665152938103426701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731193776768625402284467 10096790665152938103426701)
            ·
              refine ⟨3786296499432351788785013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10096790665152938103426701 3786296499432351788785013)
              ·
                refine ⟨354965296821782980198595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3786296499432351788785013 354965296821782980198595)
                ·
                  refine ⟨532447945232674470297893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354965296821782980198595 532447945232674470297893)
                  ·
                    refine ⟨99833989731126463180855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532447945232674470297893 99833989731126463180855)
                    ·
                      rfl

theorem cell22_291639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_291639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291639 prefixEnd_291639 := by exact prefixLift 291639
  have htrace : WordTrace (prefixWord ++ tailWord_291639) baseStart_291639 baseEnd_291639 := by
    simpa [prefixWord, tailWord_291639, baseEnd_291639] using wordTrace_append hprefix tailTrace_291639
  have hstable : (prefixWord ++ tailWord_291639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291639).length < 2 ^ (prefixWord ++ tailWord_291639).sum := by decide
  have hdescent : baseEnd_291639 < baseStart_291639 := by decide
  rcases family_descends (prefixWord ++ tailWord_291639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291667 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_291667 : Nat := 118140960795 + 291667 * 2 ^ 59
def prefixEnd_291667 : Nat := 4983230072969 + 3 ^ 40 * 291667 * 2
def baseEnd_291667 : Nat := 99843574703343723480769

theorem tailTrace_291667 : CollatzResearch.WordTrace tailWord_291667 prefixEnd_291667 99843574703343723480769 := by
  unfold tailWord_291667
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637969434347746602913255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7091979622898497735275503 10637969434347746602913255)
  ·
    refine ⟨15956954151521619904369883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10637969434347746602913255 15956954151521619904369883)
    ·
      refine ⟨23935431227282429856554825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15956954151521619904369883 23935431227282429856554825)
      ·
        refine ⟨17951573420461822392416119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23935431227282429856554825 17951573420461822392416119)
        ·
          refine ⟨26927360130692733588624179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17951573420461822392416119 26927360130692733588624179)
          ·
            refine ⟨40391040196039100382936269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26927360130692733588624179 40391040196039100382936269)
            ·
              refine ⟨15146640073514662643601101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40391040196039100382936269 15146640073514662643601101)
              ·
                refine ⟨5679990027567998491350413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15146640073514662643601101 5679990027567998491350413)
                ·
                  refine ⟨2129996260337999434256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5679990027567998491350413 2129996260337999434256405)
                  ·
                    refine ⟨99843574703343723480769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2129996260337999434256405 99843574703343723480769)
                    ·
                      rfl

theorem cell22_291667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_291667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291667 prefixEnd_291667 := by exact prefixLift 291667
  have htrace : WordTrace (prefixWord ++ tailWord_291667) baseStart_291667 baseEnd_291667 := by
    simpa [prefixWord, tailWord_291667, baseEnd_291667] using wordTrace_append hprefix tailTrace_291667
  have hstable : (prefixWord ++ tailWord_291667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291667).length < 2 ^ (prefixWord ++ tailWord_291667).sum := by decide
  have hdescent : baseEnd_291667 < baseStart_291667 := by decide
  rcases family_descends (prefixWord ++ tailWord_291667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291669 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_291669 : Nat := 118140960795 + 291669 * 2 ^ 59
def prefixEnd_291669 : Nat := 4983230072969 + 3 ^ 40 * 291669 * 2
def baseEnd_291669 : Nat := 99844259344216384930763

theorem tailTrace_291669 : CollatzResearch.WordTrace tailWord_291669 prefixEnd_291669 99844259344216384930763 := by
  unfold tailWord_291669
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638042380340500944486061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7092028253560333962990707 10638042380340500944486061)
  ·
    refine ⟨3989265892627687854182273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10638042380340500944486061 3989265892627687854182273)
    ·
      refine ⟨2991949419470765890636705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3989265892627687854182273 2991949419470765890636705)
      ·
        refine ⟨2243962064603074417977529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991949419470765890636705 2243962064603074417977529)
        ·
          refine ⟨1682971548452305813483147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243962064603074417977529 1682971548452305813483147)
          ·
            refine ⟨2524457322678458720224721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682971548452305813483147 2524457322678458720224721)
            ·
              refine ⟨1893342992008844040168541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2524457322678458720224721 1893342992008844040168541)
              ·
                refine ⟨710003622003316515063203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1893342992008844040168541 710003622003316515063203)
                ·
                  refine ⟨1065005433004974772594805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710003622003316515063203 1065005433004974772594805)
                  ·
                    refine ⟨99844259344216384930763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1065005433004974772594805 99844259344216384930763)
                    ·
                      rfl

theorem cell22_291669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_291669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291669 prefixEnd_291669 := by exact prefixLift 291669
  have htrace : WordTrace (prefixWord ++ tailWord_291669) baseStart_291669 baseEnd_291669 := by
    simpa [prefixWord, tailWord_291669, baseEnd_291669] using wordTrace_append hprefix tailTrace_291669
  have hstable : (prefixWord ++ tailWord_291669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291669).length < 2 ^ (prefixWord ++ tailWord_291669).sum := by decide
  have hdescent : baseEnd_291669 < baseStart_291669 := by decide
  rcases family_descends (prefixWord ++ tailWord_291669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291701 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_291701 : Nat := 118140960795 + 291701 * 2 ^ 59
def prefixEnd_291701 : Nat := 4983230072969 + 3 ^ 40 * 291701 * 2
def baseEnd_291701 : Nat := 99855213598178968130665

theorem tailTrace_291701 : CollatzResearch.WordTrace tailWord_291701 prefixEnd_291701 99855213598178968130665 := by
  unfold tailWord_291701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639209516224570409650957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7092806344149713606433971 10639209516224570409650957)
  ·
    refine ⟨3989703568584213903619109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10639209516224570409650957 3989703568584213903619109)
    ·
      refine ⟨748069419109540106928583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3989703568584213903619109 748069419109540106928583)
      ·
        refine ⟨1122104128664310160392875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748069419109540106928583 1122104128664310160392875)
        ·
          refine ⟨1683156192996465240589313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122104128664310160392875 1683156192996465240589313)
          ·
            refine ⟨1262367144747348930441985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683156192996465240589313 1262367144747348930441985)
            ·
              refine ⟨946775358560511697831489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262367144747348930441985 946775358560511697831489)
              ·
                refine ⟨710081518920383773373617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946775358560511697831489 710081518920383773373617)
                ·
                  refine ⟨532561139190287830030213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710081518920383773373617 532561139190287830030213)
                  ·
                    refine ⟨99855213598178968130665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532561139190287830030213 99855213598178968130665)
                    ·
                      rfl

theorem cell22_291701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_291701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291701 prefixEnd_291701 := by exact prefixLift 291701
  have htrace : WordTrace (prefixWord ++ tailWord_291701) baseStart_291701 baseEnd_291701 := by
    simpa [prefixWord, tailWord_291701, baseEnd_291701] using wordTrace_append hprefix tailTrace_291701
  have hstable : (prefixWord ++ tailWord_291701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291701).length < 2 ^ (prefixWord ++ tailWord_291701).sum := by decide
  have hdescent : baseEnd_291701 < baseStart_291701 := by decide
  rcases family_descends (prefixWord ++ tailWord_291701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291761 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 7]
def baseStart_291761 : Nat := 118140960795 + 291761 * 2 ^ 59
def prefixEnd_291761 : Nat := 4983230072969 + 3 ^ 40 * 291761 * 2
def baseEnd_291761 : Nat := 33291917608119603876827

theorem tailTrace_291761 : CollatzResearch.WordTrace tailWord_291761 prefixEnd_291761 33291917608119603876827 := by
  unfold tailWord_291761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641397896007200656835137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7094265264004800437890091 10641397896007200656835137)
  ·
    refine ⟨7981048422005400492626353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10641397896007200656835137 7981048422005400492626353)
    ·
      refine ⟨5985786316504050369469765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7981048422005400492626353 5985786316504050369469765)
      ·
        refine ⟨1122334934344509444275581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5985786316504050369469765 1122334934344509444275581)
        ·
          refine ⟨420875600379191041603343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1122334934344509444275581 420875600379191041603343)
          ·
            refine ⟨631313400568786562405015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420875600379191041603343 631313400568786562405015)
            ·
              refine ⟨946970100853179843607523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631313400568786562405015 946970100853179843607523)
              ·
                refine ⟨1420455151279769765411285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946970100853179843607523 1420455151279769765411285)
                ·
                  refine ⟨33291917608119603876827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1420455151279769765411285 33291917608119603876827)
                  ·
                    rfl

theorem cell22_291761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_291761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291761 prefixEnd_291761 := by exact prefixLift 291761
  have htrace : WordTrace (prefixWord ++ tailWord_291761) baseStart_291761 baseEnd_291761 := by
    simpa [prefixWord, tailWord_291761, baseEnd_291761] using wordTrace_append hprefix tailTrace_291761
  have hstable : (prefixWord ++ tailWord_291761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291761).length < 2 ^ (prefixWord ++ tailWord_291761).sum := by decide
  have hdescent : baseEnd_291761 < baseStart_291761 := by decide
  rcases family_descends (prefixWord ++ tailWord_291761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291791 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 1, 4]
def baseStart_291791 : Nat := 118140960795 + 291791 * 2 ^ 59
def prefixEnd_291791 : Nat := 4983230072969 + 3 ^ 40 * 291791 * 2
def baseEnd_291791 : Nat := 99886022437448733380389

theorem tailTrace_291791 : CollatzResearch.WordTrace tailWord_291791 prefixEnd_291791 99886022437448733380389 := by
  unfold tailWord_291791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642492085898515780427227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7094994723932343853618151 10642492085898515780427227)
  ·
    refine ⟨15963738128847773670640841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10642492085898515780427227 15963738128847773670640841)
    ·
      refine ⟨11972803596635830252980631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15963738128847773670640841 11972803596635830252980631)
      ·
        refine ⟨17959205394953745379470947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972803596635830252980631 17959205394953745379470947)
        ·
          refine ⟨26938808092430618069206421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17959205394953745379470947 26938808092430618069206421)
          ·
            refine ⟨1262756629332685221994051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26938808092430618069206421 1262756629332685221994051)
            ·
              refine ⟨1894134943999027832991077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262756629332685221994051 1894134943999027832991077)
              ·
                refine ⟨355150301999817718685827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1894134943999027832991077 355150301999817718685827)
                ·
                  refine ⟨532725452999726578028741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355150301999817718685827 532725452999726578028741)
                  ·
                    refine ⟨99886022437448733380389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532725452999726578028741 99886022437448733380389)
                    ·
                      rfl

theorem cell22_291791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_291791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291791 prefixEnd_291791 := by exact prefixLift 291791
  have htrace : WordTrace (prefixWord ++ tailWord_291791) baseStart_291791 baseEnd_291791 := by
    simpa [prefixWord, tailWord_291791, baseEnd_291791] using wordTrace_append hprefix tailTrace_291791
  have hstable : (prefixWord ++ tailWord_291791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291791).length < 2 ^ (prefixWord ++ tailWord_291791).sum := by decide
  have hdescent : baseEnd_291791 < baseStart_291791 := by decide
  rcases family_descends (prefixWord ++ tailWord_291791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291829 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 5]
def baseStart_291829 : Nat := 118140960795 + 291829 * 2 ^ 59
def prefixEnd_291829 : Nat := 4983230072969 + 3 ^ 40 * 291829 * 2
def baseEnd_291829 : Nat := 33299676871343100310091

theorem tailTrace_291829 : CollatzResearch.WordTrace tailWord_291829 prefixEnd_291829 33299676871343100310091 := by
  unfold tailWord_291829
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643878059760848270310541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7095918706507232180207027 10643878059760848270310541)
  ·
    refine ⟨3991454272410318101366453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10643878059760848270310541 3991454272410318101366453)
    ·
      refine ⟨374198838038467322003105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3991454272410318101366453 374198838038467322003105)
      ·
        refine ⟨280649128528850491502329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374198838038467322003105 280649128528850491502329)
        ·
          refine ⟨210486846396637868626747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280649128528850491502329 210486846396637868626747)
          ·
            refine ⟨315730269594956802940121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210486846396637868626747 315730269594956802940121)
            ·
              refine ⟨236797702196217602205091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315730269594956802940121 236797702196217602205091)
              ·
                refine ⟨355196553294326403307637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236797702196217602205091 355196553294326403307637)
                ·
                  refine ⟨33299676871343100310091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 355196553294326403307637 33299676871343100310091)
                  ·
                    rfl

theorem cell22_291829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_291829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291829 prefixEnd_291829 := by exact prefixLift 291829
  have htrace : WordTrace (prefixWord ++ tailWord_291829) baseStart_291829 baseEnd_291829 := by
    simpa [prefixWord, tailWord_291829, baseEnd_291829] using wordTrace_append hprefix tailTrace_291829
  have hstable : (prefixWord ++ tailWord_291829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291829).length < 2 ^ (prefixWord ++ tailWord_291829).sum := by decide
  have hdescent : baseEnd_291829 < baseStart_291829 := by decide
  rcases family_descends (prefixWord ++ tailWord_291829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291849 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_291849 : Nat := 118140960795 + 291849 * 2 ^ 59
def prefixEnd_291849 : Nat := 4983230072969 + 3 ^ 40 * 291849 * 2
def baseEnd_291849 : Nat := 99905877022755915430211

theorem tailTrace_291849 : CollatzResearch.WordTrace tailWord_291849 prefixEnd_291849 99905877022755915430211 := by
  unfold tailWord_291849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644607519688391686038601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7096405013125594457359067 10644607519688391686038601)
  ·
    refine ⟨7983455639766293764528951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10644607519688391686038601 7983455639766293764528951)
    ·
      refine ⟨11975183459649440646793427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983455639766293764528951 11975183459649440646793427)
      ·
        refine ⟨17962775189474160970190141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11975183459649440646793427 17962775189474160970190141)
        ·
          refine ⟨6736040696052810363821303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17962775189474160970190141 6736040696052810363821303)
          ·
            refine ⟨10104061044079215545731955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736040696052810363821303 10104061044079215545731955)
            ·
              refine ⟨15156091566118823318597933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104061044079215545731955 15156091566118823318597933)
              ·
                refine ⟨5683534337294558744474225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15156091566118823318597933 5683534337294558744474225)
                ·
                  refine ⟨4262650752970919058355669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683534337294558744474225 4262650752970919058355669)
                  ·
                    refine ⟨99905877022755915430211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4262650752970919058355669 99905877022755915430211)
                    ·
                      rfl

theorem cell22_291849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_291849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291849 prefixEnd_291849 := by exact prefixLift 291849
  have htrace : WordTrace (prefixWord ++ tailWord_291849) baseStart_291849 baseEnd_291849 := by
    simpa [prefixWord, tailWord_291849, baseEnd_291849] using wordTrace_append hprefix tailTrace_291849
  have hstable : (prefixWord ++ tailWord_291849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291849).length < 2 ^ (prefixWord ++ tailWord_291849).sum := by decide
  have hdescent : baseEnd_291849 < baseStart_291849 := by decide
  rcases family_descends (prefixWord ++ tailWord_291849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291872 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_291872 : Nat := 118140960795 + 291872 * 2 ^ 59
def prefixEnd_291872 : Nat := 4983230072969 + 3 ^ 40 * 291872 * 2
def baseEnd_291872 : Nat := 99913750392791522105141

theorem tailTrace_291872 : CollatzResearch.WordTrace tailWord_291872 prefixEnd_291872 99913750392791522105141 := by
  unfold tailWord_291872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322723199302533307062935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7096964265736711076083913 5322723199302533307062935)
  ·
    refine ⟨7984084798953799960594403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322723199302533307062935 7984084798953799960594403)
    ·
      refine ⟨11976127198430699940891605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984084798953799960594403 11976127198430699940891605)
      ·
        refine ⟨280690481213219529864647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11976127198430699940891605 280690481213219529864647)
        ·
          refine ⟨421035721819829294796971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280690481213219529864647 421035721819829294796971)
          ·
            refine ⟨631553582729743942195457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421035721819829294796971 631553582729743942195457)
            ·
              refine ⟨473665187047307956646593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631553582729743942195457 473665187047307956646593)
              ·
                refine ⟨355248890285480967484945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473665187047307956646593 355248890285480967484945)
                ·
                  refine ⟨266436667714110725613709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355248890285480967484945 266436667714110725613709)
                  ·
                    refine ⟨99913750392791522105141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266436667714110725613709 99913750392791522105141)
                    ·
                      rfl

theorem cell22_291872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_291872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291872 prefixEnd_291872 := by exact prefixLift 291872
  have htrace : WordTrace (prefixWord ++ tailWord_291872) baseStart_291872 baseEnd_291872 := by
    simpa [prefixWord, tailWord_291872, baseEnd_291872] using wordTrace_append hprefix tailTrace_291872
  have hstable : (prefixWord ++ tailWord_291872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291872).length < 2 ^ (prefixWord ++ tailWord_291872).sum := by decide
  have hdescent : baseEnd_291872 < baseStart_291872 := by decide
  rcases family_descends (prefixWord ++ tailWord_291872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291917 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_291917 : Nat := 118140960795 + 291917 * 2 ^ 59
def prefixEnd_291917 : Nat := 4983230072969 + 3 ^ 40 * 291917 * 2
def baseEnd_291917 : Nat := 99929154812426404730003

theorem tailTrace_291917 : CollatzResearch.WordTrace tailWord_291917 prefixEnd_291917 99929154812426404730003 := by
  unfold tailWord_291917
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647087683442039299514005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7098058455628026199676003 10647087683442039299514005)
  ·
    refine ⟨499082235161345592164719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10647087683442039299514005 499082235161345592164719)
    ·
      refine ⟨748623352742018388247079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499082235161345592164719 748623352742018388247079)
      ·
        refine ⟨1122935029113027582370619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748623352742018388247079 1122935029113027582370619)
        ·
          refine ⟨1684402543669541373555929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122935029113027582370619 1684402543669541373555929)
          ·
            refine ⟨1263301907752156030166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684402543669541373555929 1263301907752156030166947)
            ·
              refine ⟨1894952861628234045250421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263301907752156030166947 1894952861628234045250421)
              ·
                refine ⟨177651830777646941742227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1894952861628234045250421 177651830777646941742227)
                ·
                  refine ⟨266477746166470412613341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177651830777646941742227 266477746166470412613341)
                  ·
                    refine ⟨99929154812426404730003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266477746166470412613341 99929154812426404730003)
                    ·
                      rfl

theorem cell22_291917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_291917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291917 prefixEnd_291917 := by exact prefixLift 291917
  have htrace : WordTrace (prefixWord ++ tailWord_291917) baseStart_291917 baseEnd_291917 := by
    simpa [prefixWord, tailWord_291917, baseEnd_291917] using wordTrace_append hprefix tailTrace_291917
  have hstable : (prefixWord ++ tailWord_291917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291917).length < 2 ^ (prefixWord ++ tailWord_291917).sum := by decide
  have hdescent : baseEnd_291917 < baseStart_291917 := by decide
  rcases family_descends (prefixWord ++ tailWord_291917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291934 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_291934 : Nat := 118140960795 + 291934 * 2 ^ 59
def prefixEnd_291934 : Nat := 4983230072969 + 3 ^ 40 * 291934 * 2
def baseEnd_291934 : Nat := 99934974259844027054951

theorem tailTrace_291934 : CollatzResearch.WordTrace tailWord_291934 prefixEnd_291934 99934974259844027054951 := by
  unfold tailWord_291934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330963465547556400360357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7098471816253634135255237 1330963465547556400360357)
  ·
    refine ⟨249555649790166825067567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1330963465547556400360357 249555649790166825067567)
    ·
      refine ⟨374333474685250237601351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249555649790166825067567 374333474685250237601351)
      ·
        refine ⟨561500212027875356402027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374333474685250237601351 561500212027875356402027)
        ·
          refine ⟨842250318041813034603041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561500212027875356402027 842250318041813034603041)
          ·
            refine ⟨631687738531359775952281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842250318041813034603041 631687738531359775952281)
            ·
              refine ⟨473765803898519831964211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631687738531359775952281 473765803898519831964211)
              ·
                refine ⟨710648705847779747946317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473765803898519831964211 710648705847779747946317)
                ·
                  refine ⟨266493264692917405479869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710648705847779747946317 266493264692917405479869)
                  ·
                    refine ⟨99934974259844027054951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266493264692917405479869 99934974259844027054951)
                    ·
                      rfl

theorem cell22_291934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_291934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291934 prefixEnd_291934 := by exact prefixLift 291934
  have htrace : WordTrace (prefixWord ++ tailWord_291934) baseStart_291934 baseEnd_291934 := by
    simpa [prefixWord, tailWord_291934, baseEnd_291934] using wordTrace_append hprefix tailTrace_291934
  have hstable : (prefixWord ++ tailWord_291934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291934).length < 2 ^ (prefixWord ++ tailWord_291934).sum := by decide
  have hdescent : baseEnd_291934 < baseStart_291934 := by decide
  rcases family_descends (prefixWord ++ tailWord_291934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291958 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_291958 : Nat := 118140960795 + 291958 * 2 ^ 59
def prefixEnd_291958 : Nat := 4983230072969 + 3 ^ 40 * 291958 * 2
def baseEnd_291958 : Nat := 33314396650105321484959

theorem tailTrace_291958 : CollatzResearch.WordTrace tailWord_291958 prefixEnd_291958 33314396650105321484959 := by
  unfold tailWord_291958
  simp only [CollatzResearch.WordTrace]
  refine ⟨665536442268343956359783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7099055384195668867837685 665536442268343956359783)
  ·
    refine ⟨998304663402515934539675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665536442268343956359783 998304663402515934539675)
    ·
      refine ⟨1497456995103773901809513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998304663402515934539675 1497456995103773901809513)
      ·
        refine ⟨1123092746327830426357135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497456995103773901809513 1123092746327830426357135)
        ·
          refine ⟨1684639119491745639535703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123092746327830426357135 1684639119491745639535703)
          ·
            refine ⟨2526958679237618459303555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684639119491745639535703 2526958679237618459303555)
            ·
              refine ⟨3790438018856427688955333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526958679237618459303555 3790438018856427688955333)
              ·
                refine ⟨710707128535580191679125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3790438018856427688955333 710707128535580191679125)
                ·
                  refine ⟨33314396650105321484959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 710707128535580191679125 33314396650105321484959)
                  ·
                    rfl

theorem cell22_291958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_291958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291958 prefixEnd_291958 := by exact prefixLift 291958
  have htrace : WordTrace (prefixWord ++ tailWord_291958) baseStart_291958 baseEnd_291958 := by
    simpa [prefixWord, tailWord_291958, baseEnd_291958] using wordTrace_append hprefix tailTrace_291958
  have hstable : (prefixWord ++ tailWord_291958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291958).length < 2 ^ (prefixWord ++ tailWord_291958).sum := by decide
  have hdescent : baseEnd_291958 < baseStart_291958 := by decide
  rcases family_descends (prefixWord ++ tailWord_291958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291971 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_291971 : Nat := 118140960795 + 291971 * 2 ^ 59
def prefixEnd_291971 : Nat := 4983230072969 + 3 ^ 40 * 291971 * 2
def baseEnd_291971 : Nat := 99947640115988263879837

theorem tailTrace_291971 : CollatzResearch.WordTrace tailWord_291971 prefixEnd_291971 99947640115988263879837 := by
  unfold tailWord_291971
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649057225246406521979767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7099371483497604347986511 10649057225246406521979767)
  ·
    refine ⟨15973585837869609782969651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10649057225246406521979767 15973585837869609782969651)
    ·
      refine ⟨23960378756804414674454477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15973585837869609782969651 23960378756804414674454477)
      ·
        refine ⟨8985142033801655502920429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23960378756804414674454477 8985142033801655502920429)
        ·
          refine ⟨3369428262675620813595161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8985142033801655502920429 3369428262675620813595161)
          ·
            refine ⟨2527071197006715610196371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369428262675620813595161 2527071197006715610196371)
            ·
              refine ⟨3790606795510073415294557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527071197006715610196371 3790606795510073415294557)
              ·
                refine ⟨1421477548316277530735459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3790606795510073415294557 1421477548316277530735459)
                ·
                  refine ⟨2132216322474416296103189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421477548316277530735459 2132216322474416296103189)
                  ·
                    refine ⟨99947640115988263879837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2132216322474416296103189 99947640115988263879837)
                    ·
                      rfl

theorem cell22_291971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_291971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291971 prefixEnd_291971 := by exact prefixLift 291971
  have htrace : WordTrace (prefixWord ++ tailWord_291971) baseStart_291971 baseEnd_291971 := by
    simpa [prefixWord, tailWord_291971, baseEnd_291971] using wordTrace_append hprefix tailTrace_291971
  have hstable : (prefixWord ++ tailWord_291971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291971).length < 2 ^ (prefixWord ++ tailWord_291971).sum := by decide
  have hdescent : baseEnd_291971 < baseStart_291971 := by decide
  rcases family_descends (prefixWord ++ tailWord_291971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291992 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_291992 : Nat := 118140960795 + 291992 * 2 ^ 59
def prefixEnd_291992 : Nat := 4983230072969 + 3 ^ 40 * 291992 * 2
def baseEnd_291992 : Nat := 33318276281717069701591

theorem tailTrace_291992 : CollatzResearch.WordTrace tailWord_291992 prefixEnd_291992 33318276281717069701591 := by
  unfold tailWord_291992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324911579085163554247115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7099882105446884738996153 5324911579085163554247115)
  ·
    refine ⟨7987367368627745331370673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324911579085163554247115 7987367368627745331370673)
    ·
      refine ⟨5990525526470808998528005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7987367368627745331370673 5990525526470808998528005)
      ·
        refine ⟨1123223536213276687224001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5990525526470808998528005 1123223536213276687224001)
        ·
          refine ⟨842417652159957515418001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123223536213276687224001 842417652159957515418001)
          ·
            refine ⟨631813239119968136563501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842417652159957515418001 631813239119968136563501)
            ·
              refine ⟨236929964669988051211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631813239119968136563501 236929964669988051211313)
              ·
                refine ⟨177697473502491038408485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236929964669988051211313 177697473502491038408485)
                ·
                  refine ⟨33318276281717069701591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177697473502491038408485 33318276281717069701591)
                  ·
                    rfl

theorem cell22_291992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_291992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_291992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_291992 prefixEnd_291992 := by exact prefixLift 291992
  have htrace : WordTrace (prefixWord ++ tailWord_291992) baseStart_291992 baseEnd_291992 := by
    simpa [prefixWord, tailWord_291992, baseEnd_291992] using wordTrace_append hprefix tailTrace_291992
  have hstable : (prefixWord ++ tailWord_291992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291992).length < 2 ^ (prefixWord ++ tailWord_291992).sum := by decide
  have hdescent : baseEnd_291992 < baseStart_291992 := by decide
  rcases family_descends (prefixWord ++ tailWord_291992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292007 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 2, 3]
def baseStart_292007 : Nat := 118140960795 + 292007 * 2 ^ 59
def prefixEnd_292007 : Nat := 4983230072969 + 3 ^ 40 * 292007 * 2
def baseEnd_292007 : Nat := 99959963651696169979727

theorem tailTrace_292007 : CollatzResearch.WordTrace tailWord_292007 prefixEnd_292007 99959963651696169979727 := by
  unfold tailWord_292007
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650370253115984670290275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7100246835410656446860183 10650370253115984670290275)
  ·
    refine ⟨15975555379673977005435413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10650370253115984670290275 15975555379673977005435413)
    ·
      refine ⟨748854158422217672129785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15975555379673977005435413 748854158422217672129785)
      ·
        refine ⟨561640618816663254097339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748854158422217672129785 561640618816663254097339)
        ·
          refine ⟨842460928224994881146009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561640618816663254097339 842460928224994881146009)
          ·
            refine ⟨631845696168746160859507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842460928224994881146009 631845696168746160859507)
            ·
              refine ⟨947768544253119241289261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631845696168746160859507 947768544253119241289261)
              ·
                refine ⟨355413204094919715483473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947768544253119241289261 355413204094919715483473)
                ·
                  refine ⟨266559903071189786612605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355413204094919715483473 266559903071189786612605)
                  ·
                    refine ⟨99959963651696169979727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266559903071189786612605 99959963651696169979727)
                    ·
                      rfl

theorem cell22_292007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_292007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292007 prefixEnd_292007 := by exact prefixLift 292007
  have htrace : WordTrace (prefixWord ++ tailWord_292007) baseStart_292007 baseEnd_292007 := by
    simpa [prefixWord, tailWord_292007, baseEnd_292007] using wordTrace_append hprefix tailTrace_292007
  have hstable : (prefixWord ++ tailWord_292007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292007).length < 2 ^ (prefixWord ++ tailWord_292007).sum := by decide
  have hdescent : baseEnd_292007 < baseStart_292007 := by decide
  rcases family_descends (prefixWord ++ tailWord_292007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292016 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_292016 : Nat := 118140960795 + 292016 * 2 ^ 59
def prefixEnd_292016 : Nat := 4983230072969 + 3 ^ 40 * 292016 * 2
def baseEnd_292016 : Nat := 99963044535623146504699

theorem tailTrace_292016 : CollatzResearch.WordTrace tailWord_292016 prefixEnd_292016 99963044535623146504699 := by
  unfold tailWord_292016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325349255041689603683951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7100465673388919471578601 5325349255041689603683951)
  ·
    refine ⟨7988023882562534405525927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5325349255041689603683951 7988023882562534405525927)
    ·
      refine ⟨11982035823843801608288891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7988023882562534405525927 11982035823843801608288891)
      ·
        refine ⟨17973053735765702412433337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11982035823843801608288891 17973053735765702412433337)
        ·
          refine ⟨13479790301824276809325003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17973053735765702412433337 13479790301824276809325003)
          ·
            refine ⟨20219685452736415213987505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13479790301824276809325003 20219685452736415213987505)
            ·
              refine ⟨15164764089552311410490629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20219685452736415213987505 15164764089552311410490629)
              ·
                refine ⟨2843393266791058389466993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15164764089552311410490629 2843393266791058389466993)
                ·
                  refine ⟨2132544950093293792100245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843393266791058389466993 2132544950093293792100245)
                  ·
                    refine ⟨99963044535623146504699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2132544950093293792100245 99963044535623146504699)
                    ·
                      rfl

theorem cell22_292016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_292016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292016 prefixEnd_292016 := by exact prefixLift 292016
  have htrace : WordTrace (prefixWord ++ tailWord_292016) baseStart_292016 baseEnd_292016 := by
    simpa [prefixWord, tailWord_292016, baseEnd_292016] using wordTrace_append hprefix tailTrace_292016
  have hstable : (prefixWord ++ tailWord_292016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292016).length < 2 ^ (prefixWord ++ tailWord_292016).sum := by decide
  have hdescent : baseEnd_292016 < baseStart_292016 := by decide
  rcases family_descends (prefixWord ++ tailWord_292016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292031 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 9]
def baseStart_292031 : Nat := 118140960795 + 292031 * 2 ^ 59
def prefixEnd_292031 : Nat := 4983230072969 + 3 ^ 40 * 292031 * 2
def baseEnd_292031 : Nat := 33322726447389369126551

theorem tailTrace_292031 : CollatzResearch.WordTrace tailWord_292031 prefixEnd_292031 33322726447389369126551 := by
  unfold tailWord_292031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651245605029036769163947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7100830403352691179442631 10651245605029036769163947)
  ·
    refine ⟨15976868407543555153745921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10651245605029036769163947 15976868407543555153745921)
    ·
      refine ⟨11982651305657666365309441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15976868407543555153745921 11982651305657666365309441)
      ·
        refine ⟨8986988479243249773982081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11982651305657666365309441 8986988479243249773982081)
        ·
          refine ⟨6740241359432437330486561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8986988479243249773982081 6740241359432437330486561)
          ·
            refine ⟨5055181019574327997864921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6740241359432437330486561 5055181019574327997864921)
            ·
              refine ⟨3791385764680745998398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5055181019574327997864921 3791385764680745998398691)
              ·
                refine ⟨5687078647021118997598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791385764680745998398691 5687078647021118997598037)
                ·
                  refine ⟨33322726447389369126551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5687078647021118997598037 33322726447389369126551)
                  ·
                    rfl

theorem cell22_292031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_292031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292031 prefixEnd_292031 := by exact prefixLift 292031
  have htrace : WordTrace (prefixWord ++ tailWord_292031) baseStart_292031 baseEnd_292031 := by
    simpa [prefixWord, tailWord_292031, baseEnd_292031] using wordTrace_append hprefix tailTrace_292031
  have hstable : (prefixWord ++ tailWord_292031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292031).length < 2 ^ (prefixWord ++ tailWord_292031).sum := by decide
  have hdescent : baseEnd_292031 < baseStart_292031 := by decide
  rcases family_descends (prefixWord ++ tailWord_292031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292054 : List Nat := [5, 2, 1, 2, 3, 1, 1, 7]
def baseStart_292054 : Nat := 118140960795 + 292054 * 2 ^ 59
def prefixEnd_292054 : Nat := 4983230072969 + 3 ^ 40 * 292054 * 2
def baseEnd_292054 : Nat := 11108450301355968228287

theorem tailTrace_292054 : CollatzResearch.WordTrace tailWord_292054 prefixEnd_292054 11108450301355968228287 := by
  unfold tailWord_292054
  simp only [CollatzResearch.WordTrace]
  refine ⟨665755280246606981078201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7101389655963807798167477 665755280246606981078201)
  ·
    refine ⟨499316460184955235808651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665755280246606981078201 499316460184955235808651)
    ·
      refine ⟨748974690277432853712977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499316460184955235808651 748974690277432853712977)
      ·
        refine ⟨561731017708074640284733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748974690277432853712977 561731017708074640284733)
        ·
          refine ⟨210649131640527990106775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561731017708074640284733 210649131640527990106775)
          ·
            refine ⟨315973697460791985160163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210649131640527990106775 315973697460791985160163)
            ·
              refine ⟨473960546191187977740245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315973697460791985160163 473960546191187977740245)
              ·
                refine ⟨11108450301355968228287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 473960546191187977740245 11108450301355968228287)
                ·
                  rfl

theorem cell22_292054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_292054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292054 prefixEnd_292054 := by exact prefixLift 292054
  have htrace : WordTrace (prefixWord ++ tailWord_292054) baseStart_292054 baseEnd_292054 := by
    simpa [prefixWord, tailWord_292054, baseEnd_292054] using wordTrace_append hprefix tailTrace_292054
  have hstable : (prefixWord ++ tailWord_292054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292054).length < 2 ^ (prefixWord ++ tailWord_292054).sum := by decide
  have hdescent : baseEnd_292054 < baseStart_292054 := by decide
  rcases family_descends (prefixWord ++ tailWord_292054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292095 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 1, 4]
def baseStart_292095 : Nat := 118140960795 + 292095 * 2 ^ 59
def prefixEnd_292095 : Nat := 4983230072969 + 3 ^ 40 * 292095 * 2
def baseEnd_292095 : Nat := 99990087850093273779457

theorem tailTrace_292095 : CollatzResearch.WordTrace tailWord_292095 prefixEnd_292095 99990087850093273779457 := by
  unfold tailWord_292095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653579876797175699493739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7102386584531450466329159 10653579876797175699493739)
  ·
    refine ⟨15980369815195763549240609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10653579876797175699493739 15980369815195763549240609)
    ·
      refine ⟨11985277361396822661930457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980369815195763549240609 11985277361396822661930457)
      ·
        refine ⟨8988958021047616996447843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11985277361396822661930457 8988958021047616996447843)
        ·
          refine ⟨13483437031571425494671765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988958021047616996447843 13483437031571425494671765)
          ·
            refine ⟨632036110854910570062739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13483437031571425494671765 632036110854910570062739)
            ·
              refine ⟨948054166282365855094109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632036110854910570062739 948054166282365855094109)
              ·
                refine ⟨355520312355887195660291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948054166282365855094109 355520312355887195660291)
                ·
                  refine ⟨533280468533830793490437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355520312355887195660291 533280468533830793490437)
                  ·
                    refine ⟨99990087850093273779457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533280468533830793490437 99990087850093273779457)
                    ·
                      rfl

theorem cell22_292095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_292095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292095 prefixEnd_292095 := by exact prefixLift 292095
  have htrace : WordTrace (prefixWord ++ tailWord_292095) baseStart_292095 baseEnd_292095 := by
    simpa [prefixWord, tailWord_292095, baseEnd_292095] using wordTrace_append hprefix tailTrace_292095
  have hstable : (prefixWord ++ tailWord_292095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292095).length < 2 ^ (prefixWord ++ tailWord_292095).sum := by decide
  have hdescent : baseEnd_292095 < baseStart_292095 := by decide
  rcases family_descends (prefixWord ++ tailWord_292095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292110 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_292110 : Nat := 118140960795 + 292110 * 2 ^ 59
def prefixEnd_292110 : Nat := 4983230072969 + 3 ^ 40 * 292110 * 2
def baseEnd_292110 : Nat := 33331740885546078218137

theorem tailTrace_292110 : CollatzResearch.WordTrace tailWord_292110 prefixEnd_292110 33331740885546078218137 := by
  unfold tailWord_292110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331765871467854157661223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7102751314495222174193189 1331765871467854157661223)
  ·
    refine ⟨1997648807201781236491835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1331765871467854157661223 1997648807201781236491835)
    ·
      refine ⟨2996473210802671854737753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1997648807201781236491835 2996473210802671854737753)
      ·
        refine ⟨2247354908102003891053315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996473210802671854737753 2247354908102003891053315)
        ·
          refine ⟨3371032362153005836579973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247354908102003891053315 3371032362153005836579973)
          ·
            refine ⟨632068567903688594358745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3371032362153005836579973 632068567903688594358745)
            ·
              refine ⟨474051425927766445769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632068567903688594358745 474051425927766445769059)
              ·
                refine ⟨711077138891649668653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474051425927766445769059 711077138891649668653589)
                ·
                  refine ⟨33331740885546078218137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 711077138891649668653589 33331740885546078218137)
                  ·
                    rfl

theorem cell22_292110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_292110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292110 prefixEnd_292110 := by exact prefixLift 292110
  have htrace : WordTrace (prefixWord ++ tailWord_292110) baseStart_292110 baseEnd_292110 := by
    simpa [prefixWord, tailWord_292110, baseEnd_292110] using wordTrace_append hprefix tailTrace_292110
  have hstable : (prefixWord ++ tailWord_292110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292110).length < 2 ^ (prefixWord ++ tailWord_292110).sum := by decide
  have hdescent : baseEnd_292110 < baseStart_292110 := by decide
  rcases family_descends (prefixWord ++ tailWord_292110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292168 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_292168 : Nat := 118140960795 + 292168 * 2 ^ 59
def prefixEnd_292168 : Nat := 4983230072969 + 3 ^ 40 * 292168 * 2
def baseEnd_292168 : Nat := 100015077241945416704233

theorem tailTrace_292168 : CollatzResearch.WordTrace tailWord_292168 prefixEnd_292168 100015077241945416704233 := by
  unfold tailWord_292168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328121202766354583450579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7104161603688472777934105 5328121202766354583450579)
  ·
    refine ⟨7992181804149531875175869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328121202766354583450579 7992181804149531875175869)
    ·
      refine ⟨2997068176556074453190951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7992181804149531875175869 2997068176556074453190951)
      ·
        refine ⟨4495602264834111679786427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997068176556074453190951 4495602264834111679786427)
        ·
          refine ⟨6743403397251167519679641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495602264834111679786427 6743403397251167519679641)
          ·
            refine ⟨5057552547938375639759731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6743403397251167519679641 5057552547938375639759731)
            ·
              refine ⟨7586328821907563459639597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057552547938375639759731 7586328821907563459639597)
              ·
                refine ⟨2844873308215336297364849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7586328821907563459639597 2844873308215336297364849)
                ·
                  refine ⟨2133654981161502223023637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844873308215336297364849 2133654981161502223023637)
                  ·
                    refine ⟨100015077241945416704233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2133654981161502223023637 100015077241945416704233)
                    ·
                      rfl

theorem cell22_292168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_292168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292168 prefixEnd_292168 := by exact prefixLift 292168
  have htrace : WordTrace (prefixWord ++ tailWord_292168) baseStart_292168 baseEnd_292168 := by
    simpa [prefixWord, tailWord_292168, baseEnd_292168] using wordTrace_append hprefix tailTrace_292168
  have hstable : (prefixWord ++ tailWord_292168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292168).length < 2 ^ (prefixWord ++ tailWord_292168).sum := by decide
  have hdescent : baseEnd_292168 < baseStart_292168 := by decide
  rcases family_descends (prefixWord ++ tailWord_292168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292275 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_292275 : Nat := 118140960795 + 292275 * 2 ^ 59
def prefixEnd_292275 : Nat := 4983230072969 + 3 ^ 40 * 292275 * 2
def baseEnd_292275 : Nat := 100051705528632804278905

theorem tailTrace_292275 : CollatzResearch.WordTrace tailWord_292275 prefixEnd_292275 100051705528632804278905 := by
  unfold tailWord_292275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660145016145066441046279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106763344096710960697519 10660145016145066441046279)
  ·
    refine ⟨15990217524217599661569419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10660145016145066441046279 15990217524217599661569419)
    ·
      refine ⟨23985326286326399492354129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15990217524217599661569419 23985326286326399492354129)
      ·
        refine ⟨17988994714744799619265597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23985326286326399492354129 17988994714744799619265597)
        ·
          refine ⟨6745873018029299857224599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17988994714744799619265597 6745873018029299857224599)
          ·
            refine ⟨10118809527043949785836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745873018029299857224599 10118809527043949785836899)
            ·
              refine ⟨15178214290565924678755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10118809527043949785836899 15178214290565924678755349)
              ·
                refine ⟨711478794870277719316657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15178214290565924678755349 711478794870277719316657)
                ·
                  refine ⟨533609096152708289487493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711478794870277719316657 533609096152708289487493)
                  ·
                    refine ⟨100051705528632804278905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533609096152708289487493 100051705528632804278905)
                    ·
                      rfl

theorem cell22_292275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_292275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292275 prefixEnd_292275 := by exact prefixLift 292275
  have htrace : WordTrace (prefixWord ++ tailWord_292275) baseStart_292275 baseEnd_292275 := by
    simpa [prefixWord, tailWord_292275, baseEnd_292275] using wordTrace_append hprefix tailTrace_292275
  have hstable : (prefixWord ++ tailWord_292275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292275).length < 2 ^ (prefixWord ++ tailWord_292275).sum := by decide
  have hdescent : baseEnd_292275 < baseStart_292275 := by decide
  rcases family_descends (prefixWord ++ tailWord_292275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292292 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_292292 : Nat := 118140960795 + 292292 * 2 ^ 59
def prefixEnd_292292 : Nat := 4983230072969 + 3 ^ 40 * 292292 * 2
def baseEnd_292292 : Nat := 100057524976050426603853

theorem tailTrace_292292 : CollatzResearch.WordTrace tailWord_292292 prefixEnd_292292 100057524976050426603853 := by
  unfold tailWord_292292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330382528541739172207565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7107176704722318896276753 5330382528541739172207565)
  ·
    refine ⟨1998893448203152189577837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5330382528541739172207565 1998893448203152189577837)
    ·
      refine ⟨749585043076182071091689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1998893448203152189577837 749585043076182071091689)
      ·
        refine ⟨562188782307136553318767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749585043076182071091689 562188782307136553318767)
        ·
          refine ⟨843283173460704829978151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562188782307136553318767 843283173460704829978151)
          ·
            refine ⟨1264924760191057244967227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843283173460704829978151 1264924760191057244967227)
            ·
              refine ⟨1897387140286585867450841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264924760191057244967227 1897387140286585867450841)
              ·
                refine ⟨1423040355214939400588131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897387140286585867450841 1423040355214939400588131)
                ·
                  refine ⟨2134560532822409100882197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423040355214939400588131 2134560532822409100882197)
                  ·
                    refine ⟨100057524976050426603853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2134560532822409100882197 100057524976050426603853)
                    ·
                      rfl

theorem cell22_292292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_292292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292292 prefixEnd_292292 := by exact prefixLift 292292
  have htrace : WordTrace (prefixWord ++ tailWord_292292) baseStart_292292 baseEnd_292292 := by
    simpa [prefixWord, tailWord_292292, baseEnd_292292] using wordTrace_append hprefix tailTrace_292292
  have hstable : (prefixWord ++ tailWord_292292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292292).length < 2 ^ (prefixWord ++ tailWord_292292).sum := by decide
  have hdescent : baseEnd_292292 < baseStart_292292 := by decide
  rcases family_descends (prefixWord ++ tailWord_292292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292335 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 7]
def baseStart_292335 : Nat := 118140960795 + 292335 * 2 ^ 59
def prefixEnd_292335 : Nat := 4983230072969 + 3 ^ 40 * 292335 * 2
def baseEnd_292335 : Nat := 33357414918270882592907

theorem tailTrace_292335 : CollatzResearch.WordTrace tailWord_292335 prefixEnd_292335 33357414918270882592907 := by
  unfold tailWord_292335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10662333395927696688230459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7108222263951797792153639 10662333395927696688230459)
  ·
    refine ⟨15993500093891545032345689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10662333395927696688230459 15993500093891545032345689)
    ·
      refine ⟨11995125070418658774259267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15993500093891545032345689 11995125070418658774259267)
      ·
        refine ⟨17992687605627988161388901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995125070418658774259267 17992687605627988161388901)
        ·
          refine ⟨3373628926055247780260419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17992687605627988161388901 3373628926055247780260419)
          ·
            refine ⟨5060443389082871670390629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373628926055247780260419 5060443389082871670390629)
            ·
              refine ⟨948833135453038438198243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5060443389082871670390629 948833135453038438198243)
              ·
                refine ⟨1423249703179557657297365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948833135453038438198243 1423249703179557657297365)
                ·
                  refine ⟨33357414918270882592907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1423249703179557657297365 33357414918270882592907)
                  ·
                    rfl

theorem cell22_292335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_292335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292335 prefixEnd_292335 := by exact prefixLift 292335
  have htrace : WordTrace (prefixWord ++ tailWord_292335) baseStart_292335 baseEnd_292335 := by
    simpa [prefixWord, tailWord_292335, baseEnd_292335] using wordTrace_append hprefix tailTrace_292335
  have hstable : (prefixWord ++ tailWord_292335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292335).length < 2 ^ (prefixWord ++ tailWord_292335).sum := by decide
  have hdescent : baseEnd_292335 < baseStart_292335 := by decide
  rcases family_descends (prefixWord ++ tailWord_292335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292425 : List Nat := [1, 2, 1, 1, 2, 2, 1, 12]
def baseStart_292425 : Nat := 118140960795 + 292425 * 2 ^ 59
def prefixEnd_292425 : Nat := 4983230072969 + 3 ^ 40 * 292425 * 2
def baseEnd_292425 : Nat := 11122561510453601447605

theorem tailTrace_292425 : CollatzResearch.WordTrace tailWord_292425 prefixEnd_292425 11122561510453601447605 := by
  unfold tailWord_292425
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665615965601642059006729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110410643734428039337819 10665615965601642059006729)
  ·
    refine ⟨7999211974201231544255047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10665615965601642059006729 7999211974201231544255047)
    ·
      refine ⟨11998817961301847316382571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999211974201231544255047 11998817961301847316382571)
      ·
        refine ⟨17998226941952770974573857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11998817961301847316382571 17998226941952770974573857)
        ·
          refine ⟨13498670206464578230930393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17998226941952770974573857 13498670206464578230930393)
          ·
            refine ⟨10124002654848433673197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13498670206464578230930393 10124002654848433673197795)
            ·
              refine ⟨15186003982272650509796693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124002654848433673197795 15186003982272650509796693)
              ·
                refine ⟨11122561510453601447605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 15186003982272650509796693 11122561510453601447605)
                ·
                  rfl

theorem cell22_292425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 12].length) (baseStart_292425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292425 prefixEnd_292425 := by exact prefixLift 292425
  have htrace : WordTrace (prefixWord ++ tailWord_292425) baseStart_292425 baseEnd_292425 := by
    simpa [prefixWord, tailWord_292425, baseEnd_292425] using wordTrace_append hprefix tailTrace_292425
  have hstable : (prefixWord ++ tailWord_292425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292425).length < 2 ^ (prefixWord ++ tailWord_292425).sum := by decide
  have hdescent : baseEnd_292425 < baseStart_292425 := by decide
  rcases family_descends (prefixWord ++ tailWord_292425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292487 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 7]
def baseStart_292487 : Nat := 118140960795 + 292487 * 2 ^ 59
def prefixEnd_292487 : Nat := 4983230072969 + 3 ^ 40 * 292487 * 2
def baseEnd_292487 : Nat := 33374759153711639326085

theorem tailTrace_292487 : CollatzResearch.WordTrace tailWord_292487 prefixEnd_292487 33374759153711639326085 := by
  unfold tailWord_292487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667877291377026647763715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7111918194251351098509143 10667877291377026647763715)
  ·
    refine ⟨16001815937065539971645573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10667877291377026647763715 16001815937065539971645573)
    ·
      refine ⟨3000340488199788744683545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16001815937065539971645573 3000340488199788744683545)
      ·
        refine ⟨2250255366149841558512659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3000340488199788744683545 2250255366149841558512659)
        ·
          refine ⟨3375383049224762337768989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250255366149841558512659 3375383049224762337768989)
          ·
            refine ⟨1265768643459285876663371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3375383049224762337768989 1265768643459285876663371)
            ·
              refine ⟨1898652965188928814995057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265768643459285876663371 1898652965188928814995057)
              ·
                refine ⟨1423989723891696611246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898652965188928814995057 1423989723891696611246293)
                ·
                  refine ⟨33374759153711639326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1423989723891696611246293 33374759153711639326085)
                  ·
                    rfl

theorem cell22_292487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_292487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292487 prefixEnd_292487 := by exact prefixLift 292487
  have htrace : WordTrace (prefixWord ++ tailWord_292487) baseStart_292487 baseEnd_292487 := by
    simpa [prefixWord, tailWord_292487, baseEnd_292487] using wordTrace_append hprefix tailTrace_292487
  have hstable : (prefixWord ++ tailWord_292487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292487).length < 2 ^ (prefixWord ++ tailWord_292487).sum := by decide
  have hdescent : baseEnd_292487 < baseStart_292487 := by decide
  rcases family_descends (prefixWord ++ tailWord_292487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292508 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_292508 : Nat := 118140960795 + 292508 * 2 ^ 59
def prefixEnd_292508 : Nat := 4983230072969 + 3 ^ 40 * 292508 * 2
def baseEnd_292508 : Nat := 100131466190297863203191

theorem tailTrace_292508 : CollatzResearch.WordTrace tailWord_292508 prefixEnd_292508 100131466190297863203191 := by
  unfold tailWord_292508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334321612150473617139089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7112428816200631489518785 5334321612150473617139089)
  ·
    refine ⟨4000741209112855212854317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5334321612150473617139089 4000741209112855212854317)
    ·
      refine ⟨1500277953417320704820369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4000741209112855212854317 1500277953417320704820369)
      ·
        refine ⟨1125208465062990528615277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1500277953417320704820369 1125208465062990528615277)
        ·
          refine ⟨421953174398621448230729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1125208465062990528615277 421953174398621448230729)
          ·
            refine ⟨316464880798966086173047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421953174398621448230729 316464880798966086173047)
            ·
              refine ⟨474697321198449129259571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316464880798966086173047 474697321198449129259571)
              ·
                refine ⟨712045981797673693889357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474697321198449129259571 712045981797673693889357)
                ·
                  refine ⟨267017243174127635208509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712045981797673693889357 267017243174127635208509)
                  ·
                    refine ⟨100131466190297863203191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267017243174127635208509 100131466190297863203191)
                    ·
                      rfl

theorem cell22_292508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_292508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292508 prefixEnd_292508 := by exact prefixLift 292508
  have htrace : WordTrace (prefixWord ++ tailWord_292508) baseStart_292508 baseEnd_292508 := by
    simpa [prefixWord, tailWord_292508, baseEnd_292508] using wordTrace_append hprefix tailTrace_292508
  have hstable : (prefixWord ++ tailWord_292508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292508).length < 2 ^ (prefixWord ++ tailWord_292508).sum := by decide
  have hdescent : baseEnd_292508 < baseStart_292508 := by decide
  rcases family_descends (prefixWord ++ tailWord_292508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292551 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 1, 4]
def baseStart_292551 : Nat := 118140960795 + 292551 * 2 ^ 59
def prefixEnd_292551 : Nat := 4983230072969 + 3 ^ 40 * 292551 * 2
def baseEnd_292551 : Nat := 100146185969060084378059

theorem tailTrace_292551 : CollatzResearch.WordTrace tailWord_292551 prefixEnd_292551 100146185969060084378059 := by
  unfold tailWord_292551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670211563145165578093507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7113474375430110385395671 10670211563145165578093507)
  ·
    refine ⟨16005317344717748367140261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10670211563145165578093507 16005317344717748367140261)
    ·
      refine ⟨3000997002134577818838799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16005317344717748367140261 3000997002134577818838799)
      ·
        refine ⟨4501495503201866728258199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000997002134577818838799 4501495503201866728258199)
        ·
          refine ⟨6752243254802800092387299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501495503201866728258199 6752243254802800092387299)
          ·
            refine ⟨10128364882204200138580949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6752243254802800092387299 10128364882204200138580949)
            ·
              refine ⟨237383551926660940747991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10128364882204200138580949 237383551926660940747991)
              ·
                refine ⟨356075327889991411121987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237383551926660940747991 356075327889991411121987)
                ·
                  refine ⟨534112991834987116682981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356075327889991411121987 534112991834987116682981)
                  ·
                    refine ⟨100146185969060084378059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534112991834987116682981 100146185969060084378059)
                    ·
                      rfl

theorem cell22_292551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_292551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292551 prefixEnd_292551 := by exact prefixLift 292551
  have htrace : WordTrace (prefixWord ++ tailWord_292551) baseStart_292551 baseEnd_292551 := by
    simpa [prefixWord, tailWord_292551, baseEnd_292551] using wordTrace_append hprefix tailTrace_292551
  have hstable : (prefixWord ++ tailWord_292551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292551).length < 2 ^ (prefixWord ++ tailWord_292551).sum := by decide
  have hdescent : baseEnd_292551 < baseStart_292551 := by decide
  rcases family_descends (prefixWord ++ tailWord_292551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292581 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_292581 : Nat := 118140960795 + 292581 * 2 ^ 59
def prefixEnd_292581 : Nat := 4983230072969 + 3 ^ 40 * 292581 * 2
def baseEnd_292581 : Nat := 100156455582150006127967

theorem tailTrace_292581 : CollatzResearch.WordTrace tailWord_292581 prefixEnd_292581 100156455582150006127967 := by
  unfold tailWord_292581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671305753036480701685597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7114203835357653801123731 10671305753036480701685597)
  ·
    refine ⟨4001739657388680263132099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10671305753036480701685597 4001739657388680263132099)
    ·
      refine ⟨6002609486083020394698149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001739657388680263132099 6002609486083020394698149)
      ·
        refine ⟨1125489278640566324005903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6002609486083020394698149 1125489278640566324005903)
        ·
          refine ⟨1688233917960849486008855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125489278640566324005903 1688233917960849486008855)
          ·
            refine ⟨2532350876941274229013283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688233917960849486008855 2532350876941274229013283)
            ·
              refine ⟨3798526315411911343519925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532350876941274229013283 3798526315411911343519925)
              ·
                refine ⟨356111842069866688454993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3798526315411911343519925 356111842069866688454993)
                ·
                  refine ⟨267083881552400016341245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356111842069866688454993 267083881552400016341245)
                  ·
                    refine ⟨100156455582150006127967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267083881552400016341245 100156455582150006127967)
                    ·
                      rfl

theorem cell22_292581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_292581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292581 prefixEnd_292581 := by exact prefixLift 292581
  have htrace : WordTrace (prefixWord ++ tailWord_292581) baseStart_292581 baseEnd_292581 := by
    simpa [prefixWord, tailWord_292581, baseEnd_292581] using wordTrace_append hprefix tailTrace_292581
  have hstable : (prefixWord ++ tailWord_292581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292581).length < 2 ^ (prefixWord ++ tailWord_292581).sum := by decide
  have hdescent : baseEnd_292581 < baseStart_292581 := by decide
  rcases family_descends (prefixWord ++ tailWord_292581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292592 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_292592 : Nat := 118140960795 + 292592 * 2 ^ 59
def prefixEnd_292592 : Nat := 4983230072969 + 3 ^ 40 * 292592 * 2
def baseEnd_292592 : Nat := 100160221106949644102933

theorem tailTrace_292592 : CollatzResearch.WordTrace tailWord_292592 prefixEnd_292592 100160221106949644102933 := by
  unfold tailWord_292592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335853477998314790168015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7114471303997753053557353 5335853477998314790168015)
  ·
    refine ⟨8003780216997472185252023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5335853477998314790168015 8003780216997472185252023)
    ·
      refine ⟨12005670325496208277878035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8003780216997472185252023 12005670325496208277878035)
      ·
        refine ⟨18008505488244312416817053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12005670325496208277878035 18008505488244312416817053)
        ·
          refine ⟨6753189558091617156306395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18008505488244312416817053 6753189558091617156306395)
          ·
            refine ⟨10129784337137425734459593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753189558091617156306395 10129784337137425734459593)
            ·
              refine ⟨7597338252853069300844695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10129784337137425734459593 7597338252853069300844695)
              ·
                refine ⟨11396007379279603951267043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7597338252853069300844695 11396007379279603951267043)
                ·
                  refine ⟨17094011068919405926900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11396007379279603951267043 17094011068919405926900565)
                  ·
                    refine ⟨100160221106949644102933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17094011068919405926900565 100160221106949644102933)
                    ·
                      rfl

theorem cell22_292592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_292592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292592 prefixEnd_292592 := by exact prefixLift 292592
  have htrace : WordTrace (prefixWord ++ tailWord_292592) baseStart_292592 baseEnd_292592 := by
    simpa [prefixWord, tailWord_292592, baseEnd_292592] using wordTrace_append hprefix tailTrace_292592
  have hstable : (prefixWord ++ tailWord_292592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292592).length < 2 ^ (prefixWord ++ tailWord_292592).sum := by decide
  have hdescent : baseEnd_292592 < baseStart_292592 := by decide
  rcases family_descends (prefixWord ++ tailWord_292592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292615 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 2, 3]
def baseStart_292615 : Nat := 118140960795 + 292615 * 2 ^ 59
def prefixEnd_292615 : Nat := 4983230072969 + 3 ^ 40 * 292615 * 2
def baseEnd_292615 : Nat := 100168094476985250777863

theorem tailTrace_292615 : CollatzResearch.WordTrace tailWord_292615 prefixEnd_292615 100168094476985250777863 := by
  unfold tailWord_292615
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672545834913304508423299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7115030556608869672282199 10672545834913304508423299)
  ·
    refine ⟨16008818752369956762634949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10672545834913304508423299 16008818752369956762634949)
    ·
      refine ⟨3001653516069366892994053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16008818752369956762634949 3001653516069366892994053)
      ·
        refine ⟨562810034263006292436385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3001653516069366892994053 562810034263006292436385)
        ·
          refine ⟨422107525697254719327289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562810034263006292436385 422107525697254719327289)
          ·
            refine ⟨316580644272941039495467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422107525697254719327289 316580644272941039495467)
            ·
              refine ⟨474870966409411559243201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316580644272941039495467 474870966409411559243201)
              ·
                refine ⟨356153224807058669432401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474870966409411559243201 356153224807058669432401)
                ·
                  refine ⟨267114918605294002074301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356153224807058669432401 267114918605294002074301)
                  ·
                    refine ⟨100168094476985250777863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267114918605294002074301 100168094476985250777863)
                    ·
                      rfl

theorem cell22_292615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_292615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292615 prefixEnd_292615 := by exact prefixLift 292615
  have htrace : WordTrace (prefixWord ++ tailWord_292615) baseStart_292615 baseEnd_292615 := by
    simpa [prefixWord, tailWord_292615, baseEnd_292615] using wordTrace_append hprefix tailTrace_292615
  have hstable : (prefixWord ++ tailWord_292615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292615).length < 2 ^ (prefixWord ++ tailWord_292615).sum := by decide
  have hdescent : baseEnd_292615 < baseStart_292615 := by decide
  rcases family_descends (prefixWord ++ tailWord_292615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292703 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 1, 4]
def baseStart_292703 : Nat := 118140960795 + 292703 * 2 ^ 59
def prefixEnd_292703 : Nat := 4983230072969 + 3 ^ 40 * 292703 * 2
def baseEnd_292703 : Nat := 100198218675382354577593

theorem tailTrace_292703 : CollatzResearch.WordTrace tailWord_292703 prefixEnd_292703 100198218675382354577593 := by
  unfold tailWord_292703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10675755458594495537626763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7117170305729663691751175 10675755458594495537626763)
  ·
    refine ⟨16013633187891743306440145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10675755458594495537626763 16013633187891743306440145)
    ·
      refine ⟨12010224890918807479830109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16013633187891743306440145 12010224890918807479830109)
      ·
        refine ⟨4503834334094552804936291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12010224890918807479830109 4503834334094552804936291)
        ·
          refine ⟨6755751501141829207404437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4503834334094552804936291 6755751501141829207404437)
          ·
            refine ⟨316675851616023244097083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6755751501141829207404437 316675851616023244097083)
            ·
              refine ⟨475013777424034866145625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316675851616023244097083 475013777424034866145625)
              ·
                refine ⟨356260333068026149609219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475013777424034866145625 356260333068026149609219)
                ·
                  refine ⟨534390499602039224413829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356260333068026149609219 534390499602039224413829)
                  ·
                    refine ⟨100198218675382354577593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534390499602039224413829 100198218675382354577593)
                    ·
                      rfl

theorem cell22_292703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_292703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292703 prefixEnd_292703 := by exact prefixLift 292703
  have htrace : WordTrace (prefixWord ++ tailWord_292703) baseStart_292703 baseEnd_292703 := by
    simpa [prefixWord, tailWord_292703, baseEnd_292703] using wordTrace_append hprefix tailTrace_292703
  have hstable : (prefixWord ++ tailWord_292703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292703).length < 2 ^ (prefixWord ++ tailWord_292703).sum := by decide
  have hdescent : baseEnd_292703 < baseStart_292703 := by decide
  rcases family_descends (prefixWord ++ tailWord_292703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292716 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_292716 : Nat := 118140960795 + 292716 * 2 ^ 59
def prefixEnd_292716 : Nat := 4983230072969 + 3 ^ 40 * 292716 * 2
def baseEnd_292716 : Nat := 100202668841054654002553

theorem tailTrace_292716 : CollatzResearch.WordTrace tailWord_292716 prefixEnd_292716 100202668841054654002553 := by
  unfold tailWord_292716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5338114803773699378925001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7117486405031599171900001 5338114803773699378925001)
  ·
    refine ⟨4003586102830274534193751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5338114803773699378925001 4003586102830274534193751)
    ·
      refine ⟨6005379154245411801290627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003586102830274534193751 6005379154245411801290627)
      ·
        refine ⟨9008068731368117701935941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005379154245411801290627 9008068731368117701935941)
        ·
          refine ⟨1689012887131522069112989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9008068731368117701935941 1689012887131522069112989)
          ·
            refine ⟨633379832674320775917371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1689012887131522069112989 633379832674320775917371)
            ·
              refine ⟨950069749011481163876057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633379832674320775917371 950069749011481163876057)
              ·
                refine ⟨712552311758610872907043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950069749011481163876057 712552311758610872907043)
                ·
                  refine ⟨1068828467637916309360565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712552311758610872907043 1068828467637916309360565)
                  ·
                    refine ⟨100202668841054654002553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1068828467637916309360565 100202668841054654002553)
                    ·
                      rfl

theorem cell22_292716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_292716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292716 prefixEnd_292716 := by exact prefixLift 292716
  have htrace : WordTrace (prefixWord ++ tailWord_292716) baseStart_292716 baseEnd_292716 := by
    simpa [prefixWord, tailWord_292716, baseEnd_292716] using wordTrace_append hprefix tailTrace_292716
  have hstable : (prefixWord ++ tailWord_292716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292716).length < 2 ^ (prefixWord ++ tailWord_292716).sum := by decide
  have hdescent : baseEnd_292716 < baseStart_292716 := by decide
  rcases family_descends (prefixWord ++ tailWord_292716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292750 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_292750 : Nat := 118140960795 + 292750 * 2 ^ 59
def prefixEnd_292750 : Nat := 4983230072969 + 3 ^ 40 * 292750 * 2
def baseEnd_292750 : Nat := 100214307735889898652449

theorem tailTrace_292750 : CollatzResearch.WordTrace tailWord_292750 prefixEnd_292750 100214307735889898652449 := by
  unfold tailWord_292750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334683711178027820573463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7118313126282815043058469 1334683711178027820573463)
  ·
    refine ⟨2002025566767041730860195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334683711178027820573463 2002025566767041730860195)
    ·
      refine ⟨3003038350150562596290293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002025566767041730860195 3003038350150562596290293)
      ·
        refine ⟨281534845326615243402215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3003038350150562596290293 281534845326615243402215)
        ·
          refine ⟨422302267989922865103323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281534845326615243402215 422302267989922865103323)
          ·
            refine ⟨633453401984884297654985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422302267989922865103323 633453401984884297654985)
            ·
              refine ⟨475090051488663223241239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633453401984884297654985 475090051488663223241239)
              ·
                refine ⟨712635077232994834861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475090051488663223241239 712635077232994834861859)
                ·
                  refine ⟨1068952615849492252292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712635077232994834861859 1068952615849492252292789)
                  ·
                    refine ⟨100214307735889898652449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1068952615849492252292789 100214307735889898652449)
                    ·
                      rfl

theorem cell22_292750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_292750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292750 prefixEnd_292750 := by exact prefixLift 292750
  have htrace : WordTrace (prefixWord ++ tailWord_292750) baseStart_292750 baseEnd_292750 := by
    simpa [prefixWord, tailWord_292750, baseEnd_292750] using wordTrace_append hprefix tailTrace_292750
  have hstable : (prefixWord ++ tailWord_292750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292750).length < 2 ^ (prefixWord ++ tailWord_292750).sum := by decide
  have hdescent : baseEnd_292750 < baseStart_292750 := by decide
  rcases family_descends (prefixWord ++ tailWord_292750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292761 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_292761 : Nat := 118140960795 + 292761 * 2 ^ 59
def prefixEnd_292761 : Nat := 4983230072969 + 3 ^ 40 * 292761 * 2
def baseEnd_292761 : Nat := 100218073260689536627415

theorem tailTrace_292761 : CollatzResearch.WordTrace tailWord_292761 prefixEnd_292761 100218073260689536627415 := by
  unfold tailWord_292761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677870892384371443238137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7118580594922914295492091 10677870892384371443238137)
  ·
    refine ⟨8008403169288278582428603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10677870892384371443238137 8008403169288278582428603)
    ·
      refine ⟨12012604753932417873642905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8008403169288278582428603 12012604753932417873642905)
      ·
        refine ⟨9009453565449313405232179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12012604753932417873642905 9009453565449313405232179)
        ·
          refine ⟨13514180348173970107848269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9009453565449313405232179 13514180348173970107848269)
          ·
            refine ⟨5067817630565238790443101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13514180348173970107848269 5067817630565238790443101)
            ·
              refine ⟨1900431611461964546416163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5067817630565238790443101 1900431611461964546416163)
              ·
                refine ⟨2850647417192946819624245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900431611461964546416163 2850647417192946819624245)
                ·
                  refine ⟨267248195361838764339773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850647417192946819624245 267248195361838764339773)
                  ·
                    refine ⟨100218073260689536627415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267248195361838764339773 100218073260689536627415)
                    ·
                      rfl

theorem cell22_292761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_292761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292761 prefixEnd_292761 := by exact prefixLift 292761
  have htrace : WordTrace (prefixWord ++ tailWord_292761) baseStart_292761 baseEnd_292761 := by
    simpa [prefixWord, tailWord_292761, baseEnd_292761] using wordTrace_append hprefix tailTrace_292761
  have hstable : (prefixWord ++ tailWord_292761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292761).length < 2 ^ (prefixWord ++ tailWord_292761).sum := by decide
  have hdescent : baseEnd_292761 < baseStart_292761 := by decide
  rcases family_descends (prefixWord ++ tailWord_292761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292829 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_292829 : Nat := 118140960795 + 292829 * 2 ^ 59
def prefixEnd_292829 : Nat := 4983230072969 + 3 ^ 40 * 292829 * 2
def baseEnd_292829 : Nat := 100241351050360025927207

theorem tailTrace_292829 : CollatzResearch.WordTrace tailWord_292829 prefixEnd_292829 100241351050360025927207 := by
  unfold tailWord_292829
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680351056138019056713541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7120234037425346037809027 10680351056138019056713541)
  ·
    refine ⟨2002565823025878573133789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10680351056138019056713541 2002565823025878573133789)
    ·
      refine ⟨750962183634704464925171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2002565823025878573133789 750962183634704464925171)
      ·
        refine ⟨1126443275452056697387757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750962183634704464925171 1126443275452056697387757)
        ·
          refine ⟨422416228294521261520409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126443275452056697387757 422416228294521261520409)
          ·
            refine ⟨316812171220890946140307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422416228294521261520409 316812171220890946140307)
            ·
              refine ⟨475218256831336419210461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316812171220890946140307 475218256831336419210461)
              ·
                refine ⟨178206846311751157203923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475218256831336419210461 178206846311751157203923)
                ·
                  refine ⟨267310269467626735805885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178206846311751157203923 267310269467626735805885)
                  ·
                    refine ⟨100241351050360025927207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267310269467626735805885 100241351050360025927207)
                    ·
                      rfl

theorem cell22_292829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_292829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292829 prefixEnd_292829 := by exact prefixLift 292829
  have htrace : WordTrace (prefixWord ++ tailWord_292829) baseStart_292829 baseEnd_292829 := by
    simpa [prefixWord, tailWord_292829, baseEnd_292829] using wordTrace_append hprefix tailTrace_292829
  have hstable : (prefixWord ++ tailWord_292829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292829).length < 2 ^ (prefixWord ++ tailWord_292829).sum := by decide
  have hdescent : baseEnd_292829 < baseStart_292829 := by decide
  rcases family_descends (prefixWord ++ tailWord_292829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292960 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_292960 : Nat := 118140960795 + 292960 * 2 ^ 59
def prefixEnd_292960 : Nat := 4983230072969 + 3 ^ 40 * 292960 * 2
def baseEnd_292960 : Nat := 33428731675839783633935

theorem tailTrace_292960 : CollatzResearch.WordTrace tailWord_292960 prefixEnd_292960 33428731675839783633935 := by
  unfold tailWord_292960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342564509331714214866167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7123419345775618953154889 5342564509331714214866167)
  ·
    refine ⟨8013846763997571322299251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342564509331714214866167 8013846763997571322299251)
    ·
      refine ⟨12020770145996356983448877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013846763997571322299251 12020770145996356983448877)
      ·
        refine ⟨4507788804748633868793329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12020770145996356983448877 4507788804748633868793329)
        ·
          refine ⟨3380841603561475401594997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4507788804748633868793329 3380841603561475401594997)
          ·
            refine ⟨316953900333888318899531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3380841603561475401594997 316953900333888318899531)
            ·
              refine ⟨475430850500832478349297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316953900333888318899531 475430850500832478349297)
              ·
                refine ⟨356573137875624358761973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475430850500832478349297 356573137875624358761973)
                ·
                  refine ⟨33428731675839783633935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 356573137875624358761973 33428731675839783633935)
                  ·
                    rfl

theorem cell22_292960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_292960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292960 prefixEnd_292960 := by exact prefixLift 292960
  have htrace : WordTrace (prefixWord ++ tailWord_292960) baseStart_292960 baseEnd_292960 := by
    simpa [prefixWord, tailWord_292960, baseEnd_292960] using wordTrace_append hprefix tailTrace_292960
  have hstable : (prefixWord ++ tailWord_292960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292960).length < 2 ^ (prefixWord ++ tailWord_292960).sum := by decide
  have hdescent : baseEnd_292960 < baseStart_292960 := by decide
  rcases family_descends (prefixWord ++ tailWord_292960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292988 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_292988 : Nat := 118140960795 + 292988 * 2 ^ 59
def prefixEnd_292988 : Nat := 4983230072969 + 3 ^ 40 * 292988 * 2
def baseEnd_292988 : Nat := 33431926666578870400573

theorem tailTrace_292988 : CollatzResearch.WordTrace tailWord_292988 prefixEnd_292988 33431926666578870400573 := by
  unfold tailWord_292988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343075131280994605875809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7124100175041326141167745 5343075131280994605875809)
  ·
    refine ⟨4007306348460745954406857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5343075131280994605875809 4007306348460745954406857)
    ·
      refine ⟨3005479761345559465805143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007306348460745954406857 3005479761345559465805143)
      ·
        refine ⟨4508219642018339198707715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005479761345559465805143 4508219642018339198707715)
        ·
          refine ⟨6762329463027508798061573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508219642018339198707715 6762329463027508798061573)
          ·
            refine ⟨1267936774317657899636545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6762329463027508798061573 1267936774317657899636545)
            ·
              refine ⟨950952580738243424727409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267936774317657899636545 950952580738243424727409)
              ·
                refine ⟨713214435553682568545557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950952580738243424727409 713214435553682568545557)
                ·
                  refine ⟨33431926666578870400573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 713214435553682568545557 33431926666578870400573)
                  ·
                    rfl

theorem cell22_292988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_292988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_292988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_292988 prefixEnd_292988 := by exact prefixLift 292988
  have htrace : WordTrace (prefixWord ++ tailWord_292988) baseStart_292988 baseEnd_292988 := by
    simpa [prefixWord, tailWord_292988, baseEnd_292988] using wordTrace_append hprefix tailTrace_292988
  have hstable : (prefixWord ++ tailWord_292988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292988).length < 2 ^ (prefixWord ++ tailWord_292988).sum := by decide
  have hdescent : baseEnd_292988 < baseStart_292988 := by decide
  rcases family_descends (prefixWord ++ tailWord_292988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293020 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_293020 : Nat := 118140960795 + 293020 * 2 ^ 59
def prefixEnd_293020 : Nat := 4983230072969 + 3 ^ 40 * 293020 * 2
def baseEnd_293020 : Nat := 100306734253699194401621

theorem tailTrace_293020 : CollatzResearch.WordTrace tailWord_293020 prefixEnd_293020 100306734253699194401621 := by
  unfold tailWord_293020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343658699223029338458257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7124878265630705784611009 5343658699223029338458257)
  ·
    refine ⟨4007744024417272003843693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5343658699223029338458257 4007744024417272003843693)
    ·
      refine ⟨1502904009156477001441385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4007744024417272003843693 1502904009156477001441385)
      ·
        refine ⟨1127178006867357751081039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502904009156477001441385 1127178006867357751081039)
        ·
          refine ⟨1690767010301036626621559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127178006867357751081039 1690767010301036626621559)
          ·
            refine ⟨2536150515451554939932339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690767010301036626621559 2536150515451554939932339)
            ·
              refine ⟨3804225773177332409898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536150515451554939932339 3804225773177332409898509)
              ·
                refine ⟨1426584664941499653711941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3804225773177332409898509 1426584664941499653711941)
                ·
                  refine ⟨267484624676531185070989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1426584664941499653711941 267484624676531185070989)
                  ·
                    refine ⟨100306734253699194401621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267484624676531185070989 100306734253699194401621)
                    ·
                      rfl

theorem cell22_293020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_293020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293020 prefixEnd_293020 := by exact prefixLift 293020
  have htrace : WordTrace (prefixWord ++ tailWord_293020) baseStart_293020 baseEnd_293020 := by
    simpa [prefixWord, tailWord_293020, baseEnd_293020] using wordTrace_append hprefix tailTrace_293020
  have hstable : (prefixWord ++ tailWord_293020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293020).length < 2 ^ (prefixWord ++ tailWord_293020).sum := by decide
  have hdescent : baseEnd_293020 < baseStart_293020 := by decide
  rcases family_descends (prefixWord ++ tailWord_293020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293052 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_293052 : Nat := 118140960795 + 293052 * 2 ^ 59
def prefixEnd_293052 : Nat := 4983230072969 + 3 ^ 40 * 293052 * 2
def baseEnd_293052 : Nat := 100317688507661777601523

theorem tailTrace_293052 : CollatzResearch.WordTrace tailWord_293052 prefixEnd_293052 100317688507661777601523 := by
  unfold tailWord_293052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344242267165064071040705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7125656356220085428054273 5344242267165064071040705)
  ·
    refine ⟨4008181700373798053280529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5344242267165064071040705 4008181700373798053280529)
    ·
      refine ⟨3006136275280348539960397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008181700373798053280529 3006136275280348539960397)
      ·
        refine ⟨1127301103230130702485149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3006136275280348539960397 1127301103230130702485149)
        ·
          refine ⟨422737913711299013431931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1127301103230130702485149 422737913711299013431931)
          ·
            refine ⟨634106870566948520147897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422737913711299013431931 634106870566948520147897)
            ·
              refine ⟨475580152925211390110923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634106870566948520147897 475580152925211390110923)
              ·
                refine ⟨713370229387817085166385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475580152925211390110923 713370229387817085166385)
                ·
                  refine ⟨535027672040862813874789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713370229387817085166385 535027672040862813874789)
                  ·
                    refine ⟨100317688507661777601523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535027672040862813874789 100317688507661777601523)
                    ·
                      rfl

theorem cell22_293052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_293052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293052 prefixEnd_293052 := by exact prefixLift 293052
  have htrace : WordTrace (prefixWord ++ tailWord_293052) baseStart_293052 baseEnd_293052 := by
    simpa [prefixWord, tailWord_293052, baseEnd_293052] using wordTrace_append hprefix tailTrace_293052
  have hstable : (prefixWord ++ tailWord_293052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293052).length < 2 ^ (prefixWord ++ tailWord_293052).sum := by decide
  have hdescent : baseEnd_293052 < baseStart_293052 := by decide
  rcases family_descends (prefixWord ++ tailWord_293052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293084 : List Nat := [2, 2, 5, 2, 1, 2, 1, 7]
def baseStart_293084 : Nat := 118140960795 + 293084 * 2 ^ 59
def prefixEnd_293084 : Nat := 4983230072969 + 3 ^ 40 * 293084 * 2
def baseEnd_293084 : Nat := 11147626973513817866825

theorem tailTrace_293084 : CollatzResearch.WordTrace tailWord_293084 prefixEnd_293084 11147626973513817866825 := by
  unfold tailWord_293084
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344825835107098803623153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7126434446809465071497537 5344825835107098803623153)
  ·
    refine ⟨4008619376330324102717365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5344825835107098803623153 4008619376330324102717365)
    ·
      refine ⟨375808066530967884629753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4008619376330324102717365 375808066530967884629753)
      ·
        refine ⟨281856049898225913472315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375808066530967884629753 281856049898225913472315)
        ·
          refine ⟨422784074847338870208473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281856049898225913472315 422784074847338870208473)
          ·
            refine ⟨317088056135504152656355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422784074847338870208473 317088056135504152656355)
            ·
              refine ⟨475632084203256228984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317088056135504152656355 475632084203256228984533)
              ·
                refine ⟨11147626973513817866825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 475632084203256228984533 11147626973513817866825)
                ·
                  rfl

theorem cell22_293084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_293084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293084 prefixEnd_293084 := by exact prefixLift 293084
  have htrace : WordTrace (prefixWord ++ tailWord_293084) baseStart_293084 baseEnd_293084 := by
    simpa [prefixWord, tailWord_293084, baseEnd_293084] using wordTrace_append hprefix tailTrace_293084
  have hstable : (prefixWord ++ tailWord_293084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293084).length < 2 ^ (prefixWord ++ tailWord_293084).sum := by decide
  have hdescent : baseEnd_293084 < baseStart_293084 := by decide
  rcases family_descends (prefixWord ++ tailWord_293084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293123 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 8]
def baseStart_293123 : Nat := 118140960795 + 293123 * 2 ^ 59
def prefixEnd_293123 : Nat := 4983230072969 + 3 ^ 40 * 293123 * 2
def baseEnd_293123 : Nat := 33447331086213753025435

theorem tailTrace_293123 : CollatzResearch.WordTrace tailWord_293123 prefixEnd_293123 33447331086213753025435 := by
  unfold tailWord_293123
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691074117072907267916023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127382744715271511944015 10691074117072907267916023)
  ·
    refine ⟨16036611175609360901874035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691074117072907267916023 16036611175609360901874035)
    ·
      refine ⟨24054916763414041352811053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16036611175609360901874035 24054916763414041352811053)
      ·
        refine ⟨9020593786280265507304145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24054916763414041352811053 9020593786280265507304145)
        ·
          refine ⟨6765445339710199130478109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020593786280265507304145 6765445339710199130478109)
          ·
            refine ⟨2537042002391324673929291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6765445339710199130478109 2537042002391324673929291)
            ·
              refine ⟨3805563003586987010893937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537042002391324673929291 3805563003586987010893937)
              ·
                refine ⟨2854172252690240258170453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805563003586987010893937 2854172252690240258170453)
                ·
                  refine ⟨33447331086213753025435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2854172252690240258170453 33447331086213753025435)
                  ·
                    rfl

theorem cell22_293123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_293123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293123 prefixEnd_293123 := by exact prefixLift 293123
  have htrace : WordTrace (prefixWord ++ tailWord_293123) baseStart_293123 baseEnd_293123 := by
    simpa [prefixWord, tailWord_293123, baseEnd_293123] using wordTrace_append hprefix tailTrace_293123
  have hstable : (prefixWord ++ tailWord_293123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293123).length < 2 ^ (prefixWord ++ tailWord_293123).sum := by decide
  have hdescent : baseEnd_293123 < baseStart_293123 := by decide
  rcases family_descends (prefixWord ++ tailWord_293123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293251 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 1, 3]
def baseStart_293251 : Nat := 118140960795 + 293251 * 2 ^ 59
def prefixEnd_293251 : Nat := 4983230072969 + 3 ^ 40 * 293251 * 2
def baseEnd_293251 : Nat := 100385810274491591875913

theorem tailTrace_293251 : CollatzResearch.WordTrace tailWord_293251 prefixEnd_293251 100385810274491591875913 := by
  unfold tailWord_293251
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695742660609185128575607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7130495107072790085717071 10695742660609185128575607)
  ·
    refine ⟨16043613990913777692863411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695742660609185128575607 16043613990913777692863411)
    ·
      refine ⟨24065420986370666539295117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16043613990913777692863411 24065420986370666539295117)
      ·
        refine ⟨9024532869888999952235669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24065420986370666539295117 9024532869888999952235669)
        ·
          refine ⟨423024978276046872761047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9024532869888999952235669 423024978276046872761047)
          ·
            refine ⟨634537467414070309141571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423024978276046872761047 634537467414070309141571)
            ·
              refine ⟨951806201121105463712357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634537467414070309141571 951806201121105463712357)
              ·
                refine ⟨178463662710207274446067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 951806201121105463712357 178463662710207274446067)
                ·
                  refine ⟨267695494065310911669101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178463662710207274446067 267695494065310911669101)
                  ·
                    refine ⟨100385810274491591875913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267695494065310911669101 100385810274491591875913)
                    ·
                      rfl

theorem cell22_293251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 3].length) (baseStart_293251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293251 prefixEnd_293251 := by exact prefixLift 293251
  have htrace : WordTrace (prefixWord ++ tailWord_293251) baseStart_293251 baseEnd_293251 := by
    simpa [prefixWord, tailWord_293251, baseEnd_293251] using wordTrace_append hprefix tailTrace_293251
  have hstable : (prefixWord ++ tailWord_293251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293251).length < 2 ^ (prefixWord ++ tailWord_293251).sum := by decide
  have hdescent : baseEnd_293251 < baseStart_293251 := by decide
  rcases family_descends (prefixWord ++ tailWord_293251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293262 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_293262 : Nat := 118140960795 + 293262 * 2 ^ 59
def prefixEnd_293262 : Nat := 4983230072969 + 3 ^ 40 * 293262 * 2
def baseEnd_293262 : Nat := 100389575799291229850879

theorem tailTrace_293262 : CollatzResearch.WordTrace tailWord_293262 prefixEnd_293262 100389575799291229850879 := by
  unfold tailWord_293262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337017982946166750903255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7130762575712889338150693 1337017982946166750903255)
  ·
    refine ⟨2005526974419250126354883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337017982946166750903255 2005526974419250126354883)
    ·
      refine ⟨3008290461628875189532325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005526974419250126354883 3008290461628875189532325)
      ·
        refine ⟨564054461555414098037311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3008290461628875189532325 564054461555414098037311)
        ·
          refine ⟨846081692333121147055967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564054461555414098037311 846081692333121147055967)
          ·
            refine ⟨1269122538499681720583951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846081692333121147055967 1269122538499681720583951)
            ·
              refine ⟨1903683807749522580875927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269122538499681720583951 1903683807749522580875927)
              ·
                refine ⟨2855525711624283871313891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903683807749522580875927 2855525711624283871313891)
                ·
                  refine ⟨4283288567436425806970837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855525711624283871313891 4283288567436425806970837)
                  ·
                    refine ⟨100389575799291229850879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4283288567436425806970837 100389575799291229850879)
                    ·
                      rfl

theorem cell22_293262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_293262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293262 prefixEnd_293262 := by exact prefixLift 293262
  have htrace : WordTrace (prefixWord ++ tailWord_293262) baseStart_293262 baseEnd_293262 := by
    simpa [prefixWord, tailWord_293262, baseEnd_293262] using wordTrace_append hprefix tailTrace_293262
  have hstable : (prefixWord ++ tailWord_293262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293262).length < 2 ^ (prefixWord ++ tailWord_293262).sum := by decide
  have hdescent : baseEnd_293262 < baseStart_293262 := by decide
  rcases family_descends (prefixWord ++ tailWord_293262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293309 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 4]
def baseStart_293309 : Nat := 118140960795 + 293309 * 2 ^ 59
def prefixEnd_293309 : Nat := 4983230072969 + 3 ^ 40 * 293309 * 2
def baseEnd_293309 : Nat := 33468554953266257975245

theorem tailTrace_293309 : CollatzResearch.WordTrace tailWord_293309 prefixEnd_293309 33468554953266257975245 := by
  unfold tailWord_293309
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697858094399061034186981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7131905396266040689457987 10697858094399061034186981)
  ·
    refine ⟨2005848392699823943910059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10697858094399061034186981 2005848392699823943910059)
    ·
      refine ⟨3008772589049735915865089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005848392699823943910059 3008772589049735915865089)
      ·
        refine ⟨2256579441787301936898817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008772589049735915865089 2256579441787301936898817)
        ·
          refine ⟨1692434581340476452674113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256579441787301936898817 1692434581340476452674113)
          ·
            refine ⟨1269325936005357339505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692434581340476452674113 1269325936005357339505585)
            ·
              refine ⟨951994452004018004629189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269325936005357339505585 951994452004018004629189)
              ·
                refine ⟨178498959750753375867973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 951994452004018004629189 178498959750753375867973)
                ·
                  refine ⟨33468554953266257975245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178498959750753375867973 33468554953266257975245)
                  ·
                    rfl

theorem cell22_293309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_293309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293309 prefixEnd_293309 := by exact prefixLift 293309
  have htrace : WordTrace (prefixWord ++ tailWord_293309) baseStart_293309 baseEnd_293309 := by
    simpa [prefixWord, tailWord_293309, baseEnd_293309] using wordTrace_append hprefix tailTrace_293309
  have hstable : (prefixWord ++ tailWord_293309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293309).length < 2 ^ (prefixWord ++ tailWord_293309).sum := by decide
  have hdescent : baseEnd_293309 < baseStart_293309 := by decide
  rcases family_descends (prefixWord ++ tailWord_293309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293369 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_293369 : Nat := 118140960795 + 293369 * 2 ^ 59
def prefixEnd_293369 : Nat := 4983230072969 + 3 ^ 40 * 293369 * 2
def baseEnd_293369 : Nat := 100426204085978617425551

theorem tailTrace_293369 : CollatzResearch.WordTrace tailWord_293369 prefixEnd_293369 100426204085978617425551 := by
  unfold tailWord_293369
  simp only [CollatzResearch.WordTrace]
  refine ⟨10700046474181691281371161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7133364316121127520914107 10700046474181691281371161)
  ·
    refine ⟨8025034855636268461028371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10700046474181691281371161 8025034855636268461028371)
    ·
      refine ⟨12037552283454402691542557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025034855636268461028371 12037552283454402691542557)
      ·
        refine ⟨4514082106295401009328459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12037552283454402691542557 4514082106295401009328459)
        ·
          refine ⟨6771123159443101513992689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514082106295401009328459 6771123159443101513992689)
          ·
            refine ⟨5078342369582326135494517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771123159443101513992689 5078342369582326135494517)
            ·
              refine ⟨476094597148343075202611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5078342369582326135494517 476094597148343075202611)
              ·
                refine ⟨714141895722514612803917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476094597148343075202611 714141895722514612803917)
                ·
                  refine ⟨267803210895942979801469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714141895722514612803917 267803210895942979801469)
                  ·
                    refine ⟨100426204085978617425551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267803210895942979801469 100426204085978617425551)
                    ·
                      rfl

theorem cell22_293369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_293369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293369 prefixEnd_293369 := by exact prefixLift 293369
  have htrace : WordTrace (prefixWord ++ tailWord_293369) baseStart_293369 baseEnd_293369 := by
    simpa [prefixWord, tailWord_293369, baseEnd_293369] using wordTrace_append hprefix tailTrace_293369
  have hstable : (prefixWord ++ tailWord_293369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293369).length < 2 ^ (prefixWord ++ tailWord_293369).sum := by decide
  have hdescent : baseEnd_293369 < baseStart_293369 := by decide
  rcases family_descends (prefixWord ++ tailWord_293369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293416 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_293416 : Nat := 118140960795 + 293416 * 2 ^ 59
def prefixEnd_293416 : Nat := 4983230072969 + 3 ^ 40 * 293416 * 2
def baseEnd_293416 : Nat := 33480764382162053833469

theorem tailTrace_293416 : CollatzResearch.WordTrace tailWord_293416 prefixEnd_293416 33480764382162053833469 := by
  unfold tailWord_293416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350880352505709154166051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7134507136674278872221401 5350880352505709154166051)
  ·
    refine ⟨8026320528758563731249077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350880352505709154166051 8026320528758563731249077)
    ·
      refine ⟨752467549571115349804601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8026320528758563731249077 752467549571115349804601)
      ·
        refine ⟨564350662178336512353451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 752467549571115349804601 564350662178336512353451)
        ·
          refine ⟨846525993267504768530177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564350662178336512353451 846525993267504768530177)
          ·
            refine ⟨634894494950628576397633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846525993267504768530177 634894494950628576397633)
            ·
              refine ⟨476170871212971432298225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634894494950628576397633 476170871212971432298225)
              ·
                refine ⟨357128153409728574223669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476170871212971432298225 357128153409728574223669)
                ·
                  refine ⟨33480764382162053833469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357128153409728574223669 33480764382162053833469)
                  ·
                    rfl

theorem cell22_293416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_293416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293416 prefixEnd_293416 := by exact prefixLift 293416
  have htrace : WordTrace (prefixWord ++ tailWord_293416) baseStart_293416 baseEnd_293416 := by
    simpa [prefixWord, tailWord_293416, baseEnd_293416] using wordTrace_append hprefix tailTrace_293416
  have hstable : (prefixWord ++ tailWord_293416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293416).length < 2 ^ (prefixWord ++ tailWord_293416).sum := by decide
  have hdescent : baseEnd_293416 < baseStart_293416 := by decide
  rcases family_descends (prefixWord ++ tailWord_293416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293427 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 6]
def baseStart_293427 : Nat := 118140960795 + 293427 * 2 ^ 59
def prefixEnd_293427 : Nat := 4983230072969 + 3 ^ 40 * 293427 * 2
def baseEnd_293427 : Nat := 33482019557095266491791

theorem tailTrace_293427 : CollatzResearch.WordTrace tailWord_293427 prefixEnd_293427 33482019557095266491791 := by
  unfold tailWord_293427
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702161907971567186982535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7134774605314378124655023 10702161907971567186982535)
  ·
    refine ⟨16053242861957350780473803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10702161907971567186982535 16053242861957350780473803)
    ·
      refine ⟨24079864292936026170710705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053242861957350780473803 24079864292936026170710705)
      ·
        refine ⟨18059898219702019628033029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24079864292936026170710705 18059898219702019628033029)
        ·
          refine ⟨3386230916194128680256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18059898219702019628033029 3386230916194128680256193)
          ·
            refine ⟨2539673187145596510192145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386230916194128680256193 2539673187145596510192145)
            ·
              refine ⟨1904754890359197382644109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539673187145596510192145 1904754890359197382644109)
              ·
                refine ⟨714283083884699018491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904754890359197382644109 714283083884699018491541)
                ·
                  refine ⟨33482019557095266491791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 714283083884699018491541 33482019557095266491791)
                  ·
                    rfl

theorem cell22_293427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_293427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293427 prefixEnd_293427 := by exact prefixLift 293427
  have htrace : WordTrace (prefixWord ++ tailWord_293427) baseStart_293427 baseEnd_293427 := by
    simpa [prefixWord, tailWord_293427, baseEnd_293427] using wordTrace_append hprefix tailTrace_293427
  have hstable : (prefixWord ++ tailWord_293427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293427).length < 2 ^ (prefixWord ++ tailWord_293427).sum := by decide
  have hdescent : baseEnd_293427 < baseStart_293427 := by decide
  rcases family_descends (prefixWord ++ tailWord_293427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293493 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_293493 : Nat := 118140960795 + 293493 * 2 ^ 59
def prefixEnd_293493 : Nat := 4983230072969 + 3 ^ 40 * 293493 * 2
def baseEnd_293493 : Nat := 100468651820083627325171

theorem tailTrace_293493 : CollatzResearch.WordTrace tailWord_293493 prefixEnd_293493 100468651820083627325171 := by
  unfold tailWord_293493
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704569125732460458885133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7136379417154973639256755 10704569125732460458885133)
  ·
    refine ⟨4014213422149672672081925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10704569125732460458885133 4014213422149672672081925)
    ·
      refine ⟨752665016653063626015361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4014213422149672672081925 752665016653063626015361)
      ·
        refine ⟨564498762489797719511521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 752665016653063626015361 564498762489797719511521)
        ·
          refine ⟨423374071867348289633641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564498762489797719511521 423374071867348289633641)
          ·
            refine ⟨317530553900511217225231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423374071867348289633641 317530553900511217225231)
            ·
              refine ⟨476295830850766825837847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317530553900511217225231 476295830850766825837847)
              ·
                refine ⟨714443746276150238756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476295830850766825837847 714443746276150238756771)
                ·
                  refine ⟨1071665619414225358135157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714443746276150238756771 1071665619414225358135157)
                  ·
                    refine ⟨100468651820083627325171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1071665619414225358135157 100468651820083627325171)
                    ·
                      rfl

theorem cell22_293493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_293493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293493 prefixEnd_293493 := by exact prefixLift 293493
  have htrace : WordTrace (prefixWord ++ tailWord_293493) baseStart_293493 baseEnd_293493 := by
    simpa [prefixWord, tailWord_293493, baseEnd_293493] using wordTrace_append hprefix tailTrace_293493
  have hstable : (prefixWord ++ tailWord_293493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293493).length < 2 ^ (prefixWord ++ tailWord_293493).sum := by decide
  have hdescent : baseEnd_293493 < baseStart_293493 := by decide
  rcases family_descends (prefixWord ++ tailWord_293493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293551 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 5]
def baseStart_293551 : Nat := 118140960795 + 293551 * 2 ^ 59
def prefixEnd_293551 : Nat := 4983230072969 + 3 ^ 40 * 293551 * 2
def baseEnd_293551 : Nat := 33496168801796936458331

theorem tailTrace_293551 : CollatzResearch.WordTrace tailWord_293551 prefixEnd_293551 33496168801796936458331 := by
  unfold tailWord_293551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706684559522336364496507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7137789706348224242997671 10706684559522336364496507)
  ·
    refine ⟨16060026839283504546744761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706684559522336364496507 16060026839283504546744761)
    ·
      refine ⟨12045020129462628410058571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16060026839283504546744761 12045020129462628410058571)
      ·
        refine ⟨18067530194193942615087857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045020129462628410058571 18067530194193942615087857)
        ·
          refine ⟨13550647645645456961315893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18067530194193942615087857 13550647645645456961315893)
          ·
            refine ⟨1270373216779261590123365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13550647645645456961315893 1270373216779261590123365)
            ·
              refine ⟨238194978146111548148131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1270373216779261590123365 238194978146111548148131)
              ·
                refine ⟨357292467219167322222197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238194978146111548148131 357292467219167322222197)
                ·
                  refine ⟨33496168801796936458331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357292467219167322222197 33496168801796936458331)
                  ·
                    rfl

theorem cell22_293551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 5].length) (baseStart_293551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293551 prefixEnd_293551 := by exact prefixLift 293551
  have htrace : WordTrace (prefixWord ++ tailWord_293551) baseStart_293551 baseEnd_293551 := by
    simpa [prefixWord, tailWord_293551, baseEnd_293551] using wordTrace_append hprefix tailTrace_293551
  have hstable : (prefixWord ++ tailWord_293551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293551).length < 2 ^ (prefixWord ++ tailWord_293551).sum := by decide
  have hdescent : baseEnd_293551 < baseStart_293551 := by decide
  rcases family_descends (prefixWord ++ tailWord_293551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293589 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_293589 : Nat := 118140960795 + 293589 * 2 ^ 59
def prefixEnd_293589 : Nat := 4983230072969 + 3 ^ 40 * 293589 * 2
def baseEnd_293589 : Nat := 100501514581971376924877

theorem tailTrace_293589 : CollatzResearch.WordTrace tailWord_293589 prefixEnd_293589 100501514581971376924877 := by
  unfold tailWord_293589
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708070533384668854379821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7138713688923112569586547 10708070533384668854379821)
  ·
    refine ⟨4015526450019250820392433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10708070533384668854379821 4015526450019250820392433)
    ·
      refine ⟨3011644837514438115294325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015526450019250820392433 3011644837514438115294325)
      ·
        refine ⟨282341703516978573308843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3011644837514438115294325 282341703516978573308843)
        ·
          refine ⟨423512555275467859963265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282341703516978573308843 423512555275467859963265)
          ·
            refine ⟨317634416456600894972449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423512555275467859963265 317634416456600894972449)
            ·
              refine ⟨238225812342450671229337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317634416456600894972449 238225812342450671229337)
              ·
                refine ⟨178669359256838003422003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238225812342450671229337 178669359256838003422003)
                ·
                  refine ⟨268004038885257005133005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178669359256838003422003 268004038885257005133005)
                  ·
                    refine ⟨100501514581971376924877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268004038885257005133005 100501514581971376924877)
                    ·
                      rfl

theorem cell22_293589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_293589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293589 prefixEnd_293589 := by exact prefixLift 293589
  have htrace : WordTrace (prefixWord ++ tailWord_293589) baseStart_293589 baseEnd_293589 := by
    simpa [prefixWord, tailWord_293589, baseEnd_293589] using wordTrace_append hprefix tailTrace_293589
  have hstable : (prefixWord ++ tailWord_293589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293589).length < 2 ^ (prefixWord ++ tailWord_293589).sum := by decide
  have hdescent : baseEnd_293589 < baseStart_293589 := by decide
  rcases family_descends (prefixWord ++ tailWord_293589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293594 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_293594 : Nat := 118140960795 + 293594 * 2 ^ 59
def prefixEnd_293594 : Nat := 4983230072969 + 3 ^ 40 * 293594 * 2
def baseEnd_293594 : Nat := 100503226184153030549861

theorem tailTrace_293594 : CollatzResearch.WordTrace tailWord_293594 prefixEnd_293594 100503226184153030549861 := by
  unfold tailWord_293594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677063224591638677077959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7138835265577703138874557 2677063224591638677077959)
  ·
    refine ⟨4015594836887458015616939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677063224591638677077959 4015594836887458015616939)
    ·
      refine ⟨6023392255331187023425409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015594836887458015616939 6023392255331187023425409)
      ·
        refine ⟨4517544191498390267569057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023392255331187023425409 4517544191498390267569057)
        ·
          refine ⟨3388158143623792700676793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4517544191498390267569057 3388158143623792700676793)
          ·
            refine ⟨2541118607717844525507595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388158143623792700676793 2541118607717844525507595)
            ·
              refine ⟨3811677911576766788261393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541118607717844525507595 3811677911576766788261393)
              ·
                refine ⟨2858758433682575091196045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811677911576766788261393 2858758433682575091196045)
                ·
                  refine ⟨1072034412630965659198517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2858758433682575091196045 1072034412630965659198517)
                  ·
                    refine ⟨100503226184153030549861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1072034412630965659198517 100503226184153030549861)
                    ·
                      rfl

theorem cell22_293594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_293594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293594 prefixEnd_293594 := by exact prefixLift 293594
  have htrace : WordTrace (prefixWord ++ tailWord_293594) baseStart_293594 baseEnd_293594 := by
    simpa [prefixWord, tailWord_293594, baseEnd_293594] using wordTrace_append hprefix tailTrace_293594
  have hstable : (prefixWord ++ tailWord_293594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293594).length < 2 ^ (prefixWord ++ tailWord_293594).sum := by decide
  have hdescent : baseEnd_293594 < baseStart_293594 := by decide
  rcases family_descends (prefixWord ++ tailWord_293594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293609 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_293609 : Nat := 118140960795 + 293609 * 2 ^ 59
def prefixEnd_293609 : Nat := 4983230072969 + 3 ^ 40 * 293609 * 2
def baseEnd_293609 : Nat := 100508360990697991424815

theorem tailTrace_293609 : CollatzResearch.WordTrace tailWord_293609 prefixEnd_293609 100508360990697991424815 := by
  unfold tailWord_293609
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708799993312212270107881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7139199995541474846738587 10708799993312212270107881)
  ·
    refine ⟨8031599994984159202580911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10708799993312212270107881 8031599994984159202580911)
    ·
      refine ⟨12047399992476238803871367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8031599994984159202580911 12047399992476238803871367)
      ·
        refine ⟨18071099988714358205807051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12047399992476238803871367 18071099988714358205807051)
        ·
          refine ⟨27106649983071537308710577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18071099988714358205807051 27106649983071537308710577)
          ·
            refine ⟨20329987487303652981532933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27106649983071537308710577 20329987487303652981532933)
            ·
              refine ⟨3811872653869434934037425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20329987487303652981532933 3811872653869434934037425)
              ·
                refine ⟨2858904490402076200528069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811872653869434934037425 2858904490402076200528069)
                ·
                  refine ⟨536044591950389287599013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2858904490402076200528069 536044591950389287599013)
                  ·
                    refine ⟨100508360990697991424815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536044591950389287599013 100508360990697991424815)
                    ·
                      rfl

theorem cell22_293609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_293609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293609 prefixEnd_293609 := by exact prefixLift 293609
  have htrace : WordTrace (prefixWord ++ tailWord_293609) baseStart_293609 baseEnd_293609 := by
    simpa [prefixWord, tailWord_293609, baseEnd_293609] using wordTrace_append hprefix tailTrace_293609
  have hstable : (prefixWord ++ tailWord_293609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293609).length < 2 ^ (prefixWord ++ tailWord_293609).sum := by decide
  have hdescent : baseEnd_293609 < baseStart_293609 := by decide
  rcases family_descends (prefixWord ++ tailWord_293609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293626 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_293626 : Nat := 118140960795 + 293626 * 2 ^ 59
def prefixEnd_293626 : Nat := 4983230072969 + 3 ^ 40 * 293626 * 2
def baseEnd_293626 : Nat := 100514180438115613749763

theorem tailTrace_293626 : CollatzResearch.WordTrace tailWord_293626 prefixEnd_293626 100514180438115613749763 := by
  unfold tailWord_293626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677355008562656043369183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7139613356167082782317821 2677355008562656043369183)
  ·
    refine ⟨4016032512843984065053775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677355008562656043369183 4016032512843984065053775)
    ·
      refine ⟨6024048769265976097580663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016032512843984065053775 6024048769265976097580663)
      ·
        refine ⟨9036073153898964146370995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024048769265976097580663 9036073153898964146370995)
        ·
          refine ⟨13554109730848446219556493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036073153898964146370995 13554109730848446219556493)
          ·
            refine ⟨5082791149068167332333685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13554109730848446219556493 5082791149068167332333685)
            ·
              refine ⟨476511670225140687406283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5082791149068167332333685 476511670225140687406283)
              ·
                refine ⟨714767505337711031109425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476511670225140687406283 714767505337711031109425)
                ·
                  refine ⟨536075629003283273332069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714767505337711031109425 536075629003283273332069)
                  ·
                    refine ⟨100514180438115613749763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536075629003283273332069 100514180438115613749763)
                    ·
                      rfl

theorem cell22_293626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_293626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293626 prefixEnd_293626 := by exact prefixLift 293626
  have htrace : WordTrace (prefixWord ++ tailWord_293626) baseStart_293626 baseEnd_293626 := by
    simpa [prefixWord, tailWord_293626, baseEnd_293626] using wordTrace_append hprefix tailTrace_293626
  have hstable : (prefixWord ++ tailWord_293626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293626).length < 2 ^ (prefixWord ++ tailWord_293626).sum := by decide
  have hdescent : baseEnd_293626 < baseStart_293626 := by decide
  rcases family_descends (prefixWord ++ tailWord_293626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293630 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_293630 : Nat := 118140960795 + 293630 * 2 ^ 59
def prefixEnd_293630 : Nat := 4983230072969 + 3 ^ 40 * 293630 * 2
def baseEnd_293630 : Nat := 33505183239953645549917

theorem tailTrace_293630 : CollatzResearch.WordTrace tailWord_293630 prefixEnd_293630 33505183239953645549917 := by
  unfold tailWord_293630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338695740779516607077793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7139710617490755237748229 1338695740779516607077793)
  ·
    refine ⟨1004021805584637455308345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1338695740779516607077793 1004021805584637455308345)
    ·
      refine ⟨753016354188478091481259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004021805584637455308345 753016354188478091481259)
      ·
        refine ⟨1129524531282717137221889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753016354188478091481259 1129524531282717137221889)
        ·
          refine ⟨847143398462037852916417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129524531282717137221889 847143398462037852916417)
          ·
            refine ⟨635357548846528389687313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847143398462037852916417 635357548846528389687313)
            ·
              refine ⟨476518161634896292265485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635357548846528389687313 476518161634896292265485)
              ·
                refine ⟨178694310613086109599557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476518161634896292265485 178694310613086109599557)
                ·
                  refine ⟨33505183239953645549917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178694310613086109599557 33505183239953645549917)
                  ·
                    rfl

theorem cell22_293630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_293630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293630 prefixEnd_293630 := by exact prefixLift 293630
  have htrace : WordTrace (prefixWord ++ tailWord_293630) baseStart_293630 baseEnd_293630 := by
    simpa [prefixWord, tailWord_293630, baseEnd_293630] using wordTrace_append hprefix tailTrace_293630
  have hstable : (prefixWord ++ tailWord_293630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293630).length < 2 ^ (prefixWord ++ tailWord_293630).sum := by decide
  have hdescent : baseEnd_293630 < baseStart_293630 := by decide
  rcases family_descends (prefixWord ++ tailWord_293630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293733 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_293733 : Nat := 118140960795 + 293733 * 2 ^ 59
def prefixEnd_293733 : Nat := 4983230072969 + 3 ^ 40 * 293733 * 2
def baseEnd_293733 : Nat := 100550808724803001324435

theorem tailTrace_293733 : CollatzResearch.WordTrace tailWord_293733 prefixEnd_293733 100550808724803001324435 := by
  unfold tailWord_293733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10713322644862981447621853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7142215096575320965081235 10713322644862981447621853)
  ·
    refine ⟨4017495991823618042858195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10713322644862981447621853 4017495991823618042858195)
    ·
      refine ⟨6026243987735427064287293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017495991823618042858195 6026243987735427064287293)
      ·
        refine ⟨2259841495400785149107735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6026243987735427064287293 2259841495400785149107735)
        ·
          refine ⟨3389762243101177723661603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259841495400785149107735 3389762243101177723661603)
          ·
            refine ⟨5084643364651766585492405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389762243101177723661603 5084643364651766585492405)
            ·
              refine ⟨476685315436103117389913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5084643364651766585492405 476685315436103117389913)
              ·
                refine ⟨357513986577077338042435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476685315436103117389913 357513986577077338042435)
                ·
                  refine ⟨536270979865616007063653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357513986577077338042435 536270979865616007063653)
                  ·
                    refine ⟨100550808724803001324435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536270979865616007063653 100550808724803001324435)
                    ·
                      rfl

theorem cell22_293733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_293733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293733 prefixEnd_293733 := by exact prefixLift 293733
  have htrace : WordTrace (prefixWord ++ tailWord_293733) baseStart_293733 baseEnd_293733 := by
    simpa [prefixWord, tailWord_293733, baseEnd_293733] using wordTrace_append hprefix tailTrace_293733
  have hstable : (prefixWord ++ tailWord_293733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293733).length < 2 ^ (prefixWord ++ tailWord_293733).sum := by decide
  have hdescent : baseEnd_293733 < baseStart_293733 := by decide
  rcases family_descends (prefixWord ++ tailWord_293733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293746 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_293746 : Nat := 118140960795 + 293746 * 2 ^ 59
def prefixEnd_293746 : Nat := 4983230072969 + 3 ^ 40 * 293746 * 2
def baseEnd_293746 : Nat := 100555258890475300749395

theorem tailTrace_293746 : CollatzResearch.WordTrace tailWord_293746 prefixEnd_293746 100555258890475300749395 := by
  unfold tailWord_293746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678449198453971166961273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7142531195877256445230061 2678449198453971166961273)
  ·
    refine ⟨2008836898840478375220955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2678449198453971166961273 2008836898840478375220955)
    ·
      refine ⟨3013255348260717562831433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008836898840478375220955 3013255348260717562831433)
      ·
        refine ⟨2259941511195538172123575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3013255348260717562831433 2259941511195538172123575)
        ·
          refine ⟨3389912266793307258185363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259941511195538172123575 3389912266793307258185363)
          ·
            refine ⟨5084868400189960887278045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389912266793307258185363 5084868400189960887278045)
            ·
              refine ⟨1906825650071235332729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5084868400189960887278045 1906825650071235332729267)
              ·
                refine ⟨2860238475106852999093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906825650071235332729267 2860238475106852999093901)
                ·
                  refine ⟨1072589428165069874660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2860238475106852999093901 1072589428165069874660213)
                  ·
                    refine ⟨100555258890475300749395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1072589428165069874660213 100555258890475300749395)
                    ·
                      rfl

theorem cell22_293746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_293746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293746 prefixEnd_293746 := by exact prefixLift 293746
  have htrace : WordTrace (prefixWord ++ tailWord_293746) baseStart_293746 baseEnd_293746 := by
    simpa [prefixWord, tailWord_293746, baseEnd_293746] using wordTrace_append hprefix tailTrace_293746
  have hstable : (prefixWord ++ tailWord_293746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293746).length < 2 ^ (prefixWord ++ tailWord_293746).sum := by decide
  have hdescent : baseEnd_293746 < baseStart_293746 := by decide
  rcases family_descends (prefixWord ++ tailWord_293746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293758 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_293758 : Nat := 118140960795 + 293758 * 2 ^ 59
def prefixEnd_293758 : Nat := 4983230072969 + 3 ^ 40 * 293758 * 2
def baseEnd_293758 : Nat := 100559366735711269449359

theorem tailTrace_293758 : CollatzResearch.WordTrace tailWord_293758 prefixEnd_293758 100559366735711269449359 := by
  unfold tailWord_293758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339279308721551339660241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7142822979848273811521285 1339279308721551339660241)
  ·
    refine ⟨1004459481541163504745181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1339279308721551339660241 1004459481541163504745181)
    ·
      refine ⟨376672305577936314279443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1004459481541163504745181 376672305577936314279443)
      ·
        refine ⟨565008458366904471419165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376672305577936314279443 565008458366904471419165)
        ·
          refine ⟨211878171887589176782187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565008458366904471419165 211878171887589176782187)
          ·
            refine ⟨317817257831383765173281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211878171887589176782187 317817257831383765173281)
            ·
              refine ⟨238362943373537823879961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317817257831383765173281 238362943373537823879961)
              ·
                refine ⟨178772207530153367909971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238362943373537823879961 178772207530153367909971)
                ·
                  refine ⟨268158311295230051864957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178772207530153367909971 268158311295230051864957)
                  ·
                    refine ⟨100559366735711269449359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268158311295230051864957 100559366735711269449359)
                    ·
                      rfl

theorem cell22_293758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_293758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293758 prefixEnd_293758 := by exact prefixLift 293758
  have htrace : WordTrace (prefixWord ++ tailWord_293758) baseStart_293758 baseEnd_293758 := by
    simpa [prefixWord, tailWord_293758, baseEnd_293758] using wordTrace_append hprefix tailTrace_293758
  have hstable : (prefixWord ++ tailWord_293758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293758).length < 2 ^ (prefixWord ++ tailWord_293758).sum := by decide
  have hdescent : baseEnd_293758 < baseStart_293758 := by decide
  rcases family_descends (prefixWord ++ tailWord_293758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293765 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 4]
def baseStart_293765 : Nat := 118140960795 + 293765 * 2 ^ 59
def prefixEnd_293765 : Nat := 4983230072969 + 3 ^ 40 * 293765 * 2
def baseEnd_293765 : Nat := 33520587659588528174779

theorem tailTrace_293765 : CollatzResearch.WordTrace tailWord_293765 prefixEnd_293765 33520587659588528174779 := by
  unfold tailWord_293765
  simp only [CollatzResearch.WordTrace]
  refine ⟨10714489780747050912786749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7142993187164700608524499 10714489780747050912786749)
  ·
    refine ⟨4017933667780144092295031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10714489780747050912786749 4017933667780144092295031)
    ·
      refine ⟨6026900501670216138442547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017933667780144092295031 6026900501670216138442547)
      ·
        refine ⟨9040350752505324207663821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026900501670216138442547 9040350752505324207663821)
        ·
          refine ⟨3390131532189496577873933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9040350752505324207663821 3390131532189496577873933)
          ·
            refine ⟨1271299324571061216702725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3390131532189496577873933 1271299324571061216702725)
            ·
              refine ⟨238368623357073978131761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1271299324571061216702725 238368623357073978131761)
              ·
                refine ⟨178776467517805483598821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238368623357073978131761 178776467517805483598821)
                ·
                  refine ⟨33520587659588528174779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178776467517805483598821 33520587659588528174779)
                  ·
                    rfl

theorem cell22_293765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_293765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293765 prefixEnd_293765 := by exact prefixLift 293765
  have htrace : WordTrace (prefixWord ++ tailWord_293765) baseStart_293765 baseEnd_293765 := by
    simpa [prefixWord, tailWord_293765, baseEnd_293765] using wordTrace_append hprefix tailTrace_293765
  have hstable : (prefixWord ++ tailWord_293765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293765).length < 2 ^ (prefixWord ++ tailWord_293765).sum := by decide
  have hdescent : baseEnd_293765 < baseStart_293765 := by decide
  rcases family_descends (prefixWord ++ tailWord_293765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293780 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_293780 : Nat := 118140960795 + 293780 * 2 ^ 59
def prefixEnd_293780 : Nat := 4983230072969 + 3 ^ 40 * 293780 * 2
def baseEnd_293780 : Nat := 100566897785310545399291

theorem tailTrace_293780 : CollatzResearch.WordTrace tailWord_293780 prefixEnd_293780 100566897785310545399291 := by
  unfold tailWord_293780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357518437846354237291397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7143357917128472316388529 5357518437846354237291397)
  ·
    refine ⟨1004534707096191419492137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5357518437846354237291397 1004534707096191419492137)
    ·
      refine ⟨753401030322143564619103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004534707096191419492137 753401030322143564619103)
      ·
        refine ⟨1130101545483215346928655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753401030322143564619103 1130101545483215346928655)
        ·
          refine ⟨1695152318224823020392983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130101545483215346928655 1695152318224823020392983)
          ·
            refine ⟨2542728477337234530589475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695152318224823020392983 2542728477337234530589475)
            ·
              refine ⟨3814092716005851795884213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542728477337234530589475 3814092716005851795884213)
              ·
                refine ⟨357571192125548605864145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3814092716005851795884213 357571192125548605864145)
                ·
                  refine ⟨268178394094161454398109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357571192125548605864145 268178394094161454398109)
                  ·
                    refine ⟨100566897785310545399291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268178394094161454398109 100566897785310545399291)
                    ·
                      rfl

theorem cell22_293780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_293780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293780 prefixEnd_293780 := by exact prefixLift 293780
  have htrace : WordTrace (prefixWord ++ tailWord_293780) baseStart_293780 baseEnd_293780 := by
    simpa [prefixWord, tailWord_293780, baseEnd_293780] using wordTrace_append hprefix tailTrace_293780
  have hstable : (prefixWord ++ tailWord_293780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293780).length < 2 ^ (prefixWord ++ tailWord_293780).sum := by decide
  have hdescent : baseEnd_293780 < baseStart_293780 := by decide
  rcases family_descends (prefixWord ++ tailWord_293780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293782 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_293782 : Nat := 118140960795 + 293782 * 2 ^ 59
def prefixEnd_293782 : Nat := 4983230072969 + 3 ^ 40 * 293782 * 2
def baseEnd_293782 : Nat := 33522527475394402283095

theorem tailTrace_293782 : CollatzResearch.WordTrace tailWord_293782 prefixEnd_293782 33522527475394402283095 := by
  unfold tailWord_293782
  simp only [CollatzResearch.WordTrace]
  refine ⟨669694363855341426009725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7143406547790308544103733 669694363855341426009725)
  ·
    refine ⟨251135386445753034753647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 669694363855341426009725 251135386445753034753647)
    ·
      refine ⟨376703079668629552130471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251135386445753034753647 376703079668629552130471)
      ·
        refine ⟨565054619502944328195707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376703079668629552130471 565054619502944328195707)
        ·
          refine ⟨847581929254416492293561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565054619502944328195707 847581929254416492293561)
          ·
            refine ⟨635686446940812369220171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847581929254416492293561 635686446940812369220171)
            ·
              refine ⟨953529670411218553830257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635686446940812369220171 953529670411218553830257)
              ·
                refine ⟨715147252808413915372693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953529670411218553830257 715147252808413915372693)
                ·
                  refine ⟨33522527475394402283095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 715147252808413915372693 33522527475394402283095)
                  ·
                    rfl

theorem cell22_293782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_293782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293782 prefixEnd_293782 := by exact prefixLift 293782
  have htrace : WordTrace (prefixWord ++ tailWord_293782) baseStart_293782 baseEnd_293782 := by
    simpa [prefixWord, tailWord_293782, baseEnd_293782] using wordTrace_append hprefix tailTrace_293782
  have hstable : (prefixWord ++ tailWord_293782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293782).length < 2 ^ (prefixWord ++ tailWord_293782).sum := by decide
  have hdescent : baseEnd_293782 < baseStart_293782 := by decide
  rcases family_descends (prefixWord ++ tailWord_293782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293902 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_293902 : Nat := 118140960795 + 293902 * 2 ^ 59
def prefixEnd_293902 : Nat := 4983230072969 + 3 ^ 40 * 293902 * 2
def baseEnd_293902 : Nat := 100608660878542893848917

theorem tailTrace_293902 : CollatzResearch.WordTrace tailWord_293902 prefixEnd_293902 100608660878542893848917 := by
  unfold tailWord_293902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339935822656340413815495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7146324387500482207015973 1339935822656340413815495)
  ·
    refine ⟨2009903733984510620723243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1339935822656340413815495 2009903733984510620723243)
    ·
      refine ⟨3014855600976765931084865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009903733984510620723243 3014855600976765931084865)
      ·
        refine ⟨2261141700732574448313649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3014855600976765931084865 2261141700732574448313649)
        ·
          refine ⟨1695856275549430836235237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261141700732574448313649 1695856275549430836235237)
          ·
            refine ⟨317973051665518281794107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1695856275549430836235237 317973051665518281794107)
            ·
              refine ⟨476959577498277422691161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317973051665518281794107 476959577498277422691161)
              ·
                refine ⟨357719683123708067018371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476959577498277422691161 357719683123708067018371)
                ·
                  refine ⟨536579524685562100527557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357719683123708067018371 536579524685562100527557)
                  ·
                    refine ⟨100608660878542893848917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536579524685562100527557 100608660878542893848917)
                    ·
                      rfl

theorem cell22_293902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_293902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293902 prefixEnd_293902 := by exact prefixLift 293902
  have htrace : WordTrace (prefixWord ++ tailWord_293902) baseStart_293902 baseEnd_293902 := by
    simpa [prefixWord, tailWord_293902, baseEnd_293902] using wordTrace_append hprefix tailTrace_293902
  have hstable : (prefixWord ++ tailWord_293902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293902).length < 2 ^ (prefixWord ++ tailWord_293902).sum := by decide
  have hdescent : baseEnd_293902 < baseStart_293902 := by decide
  rcases family_descends (prefixWord ++ tailWord_293902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293913 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_293913 : Nat := 118140960795 + 293913 * 2 ^ 59
def prefixEnd_293913 : Nat := 4983230072969 + 3 ^ 40 * 293913 * 2
def baseEnd_293913 : Nat := 100612426403342531823883

theorem tailTrace_293913 : CollatzResearch.WordTrace tailWord_293913 prefixEnd_293913 100612426403342531823883 := by
  unfold tailWord_293913
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719887784210872189174393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7146591856140581459449595 10719887784210872189174393)
  ·
    refine ⟨8039915838158154141880795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10719887784210872189174393 8039915838158154141880795)
    ·
      refine ⟨12059873757237231212821193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039915838158154141880795 12059873757237231212821193)
      ·
        refine ⟨9044905317927923409615895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12059873757237231212821193 9044905317927923409615895)
        ·
          refine ⟨13567357976891885114423843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044905317927923409615895 13567357976891885114423843)
          ·
            refine ⟨20351036965337827671635765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13567357976891885114423843 20351036965337827671635765)
            ·
              refine ⟨1907909715500421344215853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20351036965337827671635765 1907909715500421344215853)
              ·
                refine ⟨715466143312658004080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1907909715500421344215853 715466143312658004080945)
                ·
                  refine ⟨536599607484493503060709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715466143312658004080945 536599607484493503060709)
                  ·
                    refine ⟨100612426403342531823883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536599607484493503060709 100612426403342531823883)
                    ·
                      rfl

theorem cell22_293913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_293913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293913 prefixEnd_293913 := by exact prefixLift 293913
  have htrace : WordTrace (prefixWord ++ tailWord_293913) baseStart_293913 baseEnd_293913 := by
    simpa [prefixWord, tailWord_293913, baseEnd_293913] using wordTrace_append hprefix tailTrace_293913
  have hstable : (prefixWord ++ tailWord_293913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293913).length < 2 ^ (prefixWord ++ tailWord_293913).sum := by decide
  have hdescent : baseEnd_293913 < baseStart_293913 := by decide
  rcases family_descends (prefixWord ++ tailWord_293913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293945 : List Nat := [1, 2, 1, 5, 2, 3, 1, 7]
def baseStart_293945 : Nat := 118140960795 + 293945 * 2 ^ 59
def prefixEnd_293945 : Nat := 4983230072969 + 3 ^ 40 * 293945 * 2
def baseEnd_293945 : Nat := 11180375628589457224865

theorem tailTrace_293945 : CollatzResearch.WordTrace tailWord_293945 prefixEnd_293945 11180375628589457224865 := by
  unfold tailWord_293945
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721054920094941654339289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7147369946729961102892859 10721054920094941654339289)
  ·
    refine ⟨8040791190071206240754467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10721054920094941654339289 8040791190071206240754467)
    ·
      refine ⟨12061186785106809361131701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8040791190071206240754467 12061186785106809361131701)
      ·
        refine ⟨1130736261103763377606097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12061186785106809361131701 1130736261103763377606097)
        ·
          refine ⟨848052195827822533204573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130736261103763377606097 848052195827822533204573)
          ·
            refine ⟨318019573435433449951715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 848052195827822533204573 318019573435433449951715)
            ·
              refine ⟨477029360153150174927573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318019573435433449951715 477029360153150174927573)
              ·
                refine ⟨11180375628589457224865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 477029360153150174927573 11180375628589457224865)
                ·
                  rfl

theorem cell22_293945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 7].length) (baseStart_293945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293945 prefixEnd_293945 := by exact prefixLift 293945
  have htrace : WordTrace (prefixWord ++ tailWord_293945) baseStart_293945 baseEnd_293945 := by
    simpa [prefixWord, tailWord_293945, baseEnd_293945] using wordTrace_append hprefix tailTrace_293945
  have hstable : (prefixWord ++ tailWord_293945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293945).length < 2 ^ (prefixWord ++ tailWord_293945).sum := by decide
  have hdescent : baseEnd_293945 < baseStart_293945 := by decide
  rcases family_descends (prefixWord ++ tailWord_293945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293960 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_293960 : Nat := 118140960795 + 293960 * 2 ^ 59
def prefixEnd_293960 : Nat := 4983230072969 + 3 ^ 40 * 293960 * 2
def baseEnd_293960 : Nat := 100628515463850075898739

theorem tailTrace_293960 : CollatzResearch.WordTrace tailWord_293960 prefixEnd_293960 100628515463850075898739 := by
  unfold tailWord_293960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360801007520299608067667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7147734676693732810756889 5360801007520299608067667)
  ·
    refine ⟨8041201511280449412101501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5360801007520299608067667 8041201511280449412101501)
    ·
      refine ⟨3015450566730168529538063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8041201511280449412101501 3015450566730168529538063)
      ·
        refine ⟨4523175850095252794307095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015450566730168529538063 4523175850095252794307095)
        ·
          refine ⟨6784763775142879191460643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523175850095252794307095 6784763775142879191460643)
          ·
            refine ⟨10177145662714318787190965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784763775142879191460643 10177145662714318787190965)
            ·
              refine ⟨954107405879467386299153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10177145662714318787190965 954107405879467386299153)
              ·
                refine ⟨715580554409600539724365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954107405879467386299153 715580554409600539724365)
                ·
                  refine ⟨268342707903600202396637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715580554409600539724365 268342707903600202396637)
                  ·
                    refine ⟨100628515463850075898739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268342707903600202396637 100628515463850075898739)
                    ·
                      rfl

theorem cell22_293960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_293960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293960 prefixEnd_293960 := by exact prefixLift 293960
  have htrace : WordTrace (prefixWord ++ tailWord_293960) baseStart_293960 baseEnd_293960 := by
    simpa [prefixWord, tailWord_293960, baseEnd_293960] using wordTrace_append hprefix tailTrace_293960
  have hstable : (prefixWord ++ tailWord_293960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293960).length < 2 ^ (prefixWord ++ tailWord_293960).sum := by decide
  have hdescent : baseEnd_293960 < baseStart_293960 := by decide
  rcases family_descends (prefixWord ++ tailWord_293960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293973 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 7]
def baseStart_293973 : Nat := 118140960795 + 293973 * 2 ^ 59
def prefixEnd_293973 : Nat := 4983230072969 + 3 ^ 40 * 293973 * 2
def baseEnd_293973 : Nat := 33544321876507458441233

theorem tailTrace_293973 : CollatzResearch.WordTrace tailWord_293973 prefixEnd_293973 33544321876507458441233 := by
  unfold tailWord_293973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722076163993502436358573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7148050775995668290905715 10722076163993502436358573)
  ·
    refine ⟨4020778561497563413634465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10722076163993502436358573 4020778561497563413634465)
    ·
      refine ⟨3015583921123172560225849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4020778561497563413634465 3015583921123172560225849)
      ·
        refine ⟨2261687940842379420169387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3015583921123172560225849 2261687940842379420169387)
        ·
          refine ⟨3392531911263569130254081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261687940842379420169387 3392531911263569130254081)
          ·
            refine ⟨2544398933447676847690561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392531911263569130254081 2544398933447676847690561)
            ·
              refine ⟨1908299200085757635767921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544398933447676847690561 1908299200085757635767921)
              ·
                refine ⟨1431224400064318226825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908299200085757635767921 1431224400064318226825941)
                ·
                  refine ⟨33544321876507458441233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1431224400064318226825941 33544321876507458441233)
                  ·
                    rfl

theorem cell22_293973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_293973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293973 prefixEnd_293973 := by exact prefixLift 293973
  have htrace : WordTrace (prefixWord ++ tailWord_293973) baseStart_293973 baseEnd_293973 := by
    simpa [prefixWord, tailWord_293973, baseEnd_293973] using wordTrace_append hprefix tailTrace_293973
  have hstable : (prefixWord ++ tailWord_293973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293973).length < 2 ^ (prefixWord ++ tailWord_293973).sum := by decide
  have hdescent : baseEnd_293973 < baseStart_293973 := by decide
  rcases family_descends (prefixWord ++ tailWord_293973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293994 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_293994 : Nat := 118140960795 + 293994 * 2 ^ 59
def prefixEnd_293994 : Nat := 4983230072969 + 3 ^ 40 * 293994 * 2
def baseEnd_293994 : Nat := 100640154358685320548635

theorem tailTrace_293994 : CollatzResearch.WordTrace tailWord_293994 prefixEnd_293994 100640154358685320548635 := by
  unfold tailWord_293994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680710524229355755718259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7148561397944948681915357 2680710524229355755718259)
  ·
    refine ⟨4021065786344033633577389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2680710524229355755718259 4021065786344033633577389)
    ·
      refine ⟨1507899669879012612591521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4021065786344033633577389 1507899669879012612591521)
      ·
        refine ⟨1130924752409259459443641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507899669879012612591521 1130924752409259459443641)
        ·
          refine ⟨848193564306944594582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130924752409259459443641 848193564306944594582731)
          ·
            refine ⟨1272290346460416891874097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848193564306944594582731 1272290346460416891874097)
            ·
              refine ⟨954217759845312668905573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272290346460416891874097 954217759845312668905573)
              ·
                refine ⟨178915829970996125419795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 954217759845312668905573 178915829970996125419795)
                ·
                  refine ⟨268373744956494188129693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178915829970996125419795 268373744956494188129693)
                  ·
                    refine ⟨100640154358685320548635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268373744956494188129693 100640154358685320548635)
                    ·
                      rfl

theorem cell22_293994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_293994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_293994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_293994 prefixEnd_293994 := by exact prefixLift 293994
  have htrace : WordTrace (prefixWord ++ tailWord_293994) baseStart_293994 baseEnd_293994 := by
    simpa [prefixWord, tailWord_293994, baseEnd_293994] using wordTrace_append hprefix tailTrace_293994
  have hstable : (prefixWord ++ tailWord_293994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293994).length < 2 ^ (prefixWord ++ tailWord_293994).sum := by decide
  have hdescent : baseEnd_293994 < baseStart_293994 := by decide
  rcases family_descends (prefixWord ++ tailWord_293994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294052 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_294052 : Nat := 118140960795 + 294052 * 2 ^ 59
def prefixEnd_294052 : Nat := 4983230072969 + 3 ^ 40 * 294052 * 2
def baseEnd_294052 : Nat := 33553336314664167532819

theorem tailTrace_294052 : CollatzResearch.WordTrace tailWord_294052 prefixEnd_294052 33553336314664167532819 := by
  unfold tailWord_294052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5362478765353649464242205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7149971687138199285656273 5362478765353649464242205)
  ·
    refine ⟨2010929537007618549090827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5362478765353649464242205 2010929537007618549090827)
    ·
      refine ⟨3016394305511427823636241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010929537007618549090827 3016394305511427823636241)
      ·
        refine ⟨2262295729133570867727181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3016394305511427823636241 2262295729133570867727181)
        ·
          refine ⟨848360898425089075397693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2262295729133570867727181 848360898425089075397693)
          ·
            refine ⟨318135336909408403274135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 848360898425089075397693 318135336909408403274135)
            ·
              refine ⟨477203005364112604911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318135336909408403274135 477203005364112604911203)
              ·
                refine ⟨715804508046168907366805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477203005364112604911203 715804508046168907366805)
                ·
                  refine ⟨33553336314664167532819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 715804508046168907366805 33553336314664167532819)
                  ·
                    rfl

theorem cell22_294052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_294052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294052 prefixEnd_294052 := by exact prefixLift 294052
  have htrace : WordTrace (prefixWord ++ tailWord_294052) baseStart_294052 baseEnd_294052 := by
    simpa [prefixWord, tailWord_294052, baseEnd_294052] using wordTrace_append hprefix tailTrace_294052
  have hstable : (prefixWord ++ tailWord_294052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294052).length < 2 ^ (prefixWord ++ tailWord_294052).sum := by decide
  have hdescent : baseEnd_294052 < baseStart_294052 := by decide
  rcases family_descends (prefixWord ++ tailWord_294052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294063 : List Nat := [1, 1, 2, 1, 2, 3, 3, 9]
def baseStart_294063 : Nat := 118140960795 + 294063 * 2 ^ 59
def prefixEnd_294063 : Nat := 4983230072969 + 3 ^ 40 * 294063 * 2
def baseEnd_294063 : Nat := 11184863829865793397047

theorem tailTrace_294063 : CollatzResearch.WordTrace tailWord_294063 prefixEnd_294063 11184863829865793397047 := by
  unfold tailWord_294063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725358733667447807134843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7150239155778298538089895 10725358733667447807134843)
  ·
    refine ⟨16088038100501171710702265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10725358733667447807134843 16088038100501171710702265)
    ·
      refine ⟨12066028575375878783026699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16088038100501171710702265 12066028575375878783026699)
      ·
        refine ⟨18099042863063818174540049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12066028575375878783026699 18099042863063818174540049)
        ·
          refine ⟨13574282147297863630905037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18099042863063818174540049 13574282147297863630905037)
          ·
            refine ⟨5090355805236698861589389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13574282147297863630905037 5090355805236698861589389)
            ·
              refine ⟨1908883426963762073096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090355805236698861589389 1908883426963762073096021)
              ·
                refine ⟨11184863829865793397047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1908883426963762073096021 11184863829865793397047)
                ·
                  rfl

theorem cell22_294063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 9].length) (baseStart_294063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294063 prefixEnd_294063 := by exact prefixLift 294063
  have htrace : WordTrace (prefixWord ++ tailWord_294063) baseStart_294063 baseEnd_294063 := by
    simpa [prefixWord, tailWord_294063, baseEnd_294063] using wordTrace_append hprefix tailTrace_294063
  have hstable : (prefixWord ++ tailWord_294063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294063).length < 2 ^ (prefixWord ++ tailWord_294063).sum := by decide
  have hdescent : baseEnd_294063 < baseStart_294063 := by decide
  rcases family_descends (prefixWord ++ tailWord_294063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294095 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 7, 3]
def baseStart_294095 : Nat := 118140960795 + 294095 * 2 ^ 59
def prefixEnd_294095 : Nat := 4983230072969 + 3 ^ 40 * 294095 * 2
def baseEnd_294095 : Nat := 100674728722754723773325

theorem tailTrace_294095 : CollatzResearch.WordTrace tailWord_294095 prefixEnd_294095 100674728722754723773325 := by
  unfold tailWord_294095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726525869551517272299739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7151017246367678181533159 10726525869551517272299739)
  ·
    refine ⟨16089788804327275908449609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10726525869551517272299739 16089788804327275908449609)
    ·
      refine ⟨12067341603245456931337207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16089788804327275908449609 12067341603245456931337207)
      ·
        refine ⟨18101012404868185397005811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12067341603245456931337207 18101012404868185397005811)
        ·
          refine ⟨27151518607302278095508717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18101012404868185397005811 27151518607302278095508717)
          ·
            refine ⟨10181819477738354285815769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27151518607302278095508717 10181819477738354285815769)
            ·
              refine ⟨7636364608303765714361827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10181819477738354285815769 7636364608303765714361827)
              ·
                refine ⟨11454546912455648571542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7636364608303765714361827 11454546912455648571542741)
                ·
                  refine ⟨268465943260679263395533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11454546912455648571542741 268465943260679263395533)
                  ·
                    refine ⟨100674728722754723773325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268465943260679263395533 100674728722754723773325)
                    ·
                      rfl

theorem cell22_294095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_294095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294095 prefixEnd_294095 := by exact prefixLift 294095
  have htrace : WordTrace (prefixWord ++ tailWord_294095) baseStart_294095 baseEnd_294095 := by
    simpa [prefixWord, tailWord_294095, baseEnd_294095] using wordTrace_append hprefix tailTrace_294095
  have hstable : (prefixWord ++ tailWord_294095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294095).length < 2 ^ (prefixWord ++ tailWord_294095).sum := by decide
  have hdescent : baseEnd_294095 < baseStart_294095 := by decide
  rcases family_descends (prefixWord ++ tailWord_294095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294202 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_294202 : Nat := 118140960795 + 294202 * 2 ^ 59
def prefixEnd_294202 : Nat := 4983230072969 + 3 ^ 40 * 294202 * 2
def baseEnd_294202 : Nat := 100711357009442111347997

theorem tailTrace_294202 : CollatzResearch.WordTrace tailWord_294202 prefixEnd_294202 100711357009442111347997 := by
  unfold tailWord_294202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682607120040968636611215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7153618986775916364296573 2682607120040968636611215)
  ·
    refine ⟨4023910680061452954916823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2682607120040968636611215 4023910680061452954916823)
    ·
      refine ⟨6035866020092179432375235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023910680061452954916823 6035866020092179432375235)
      ·
        refine ⟨9053799030138269148562853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035866020092179432375235 9053799030138269148562853)
        ·
          refine ⟨1697587318150925465355535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9053799030138269148562853 1697587318150925465355535)
          ·
            refine ⟨2546380977226388198033303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697587318150925465355535 2546380977226388198033303)
            ·
              refine ⟨3819571465839582297049955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546380977226388198033303 3819571465839582297049955)
              ·
                refine ⟨5729357198759373445574933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819571465839582297049955 5729357198759373445574933)
                ·
                  refine ⟨268563618691845630261325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5729357198759373445574933 268563618691845630261325)
                  ·
                    refine ⟨100711357009442111347997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268563618691845630261325 100711357009442111347997)
                    ·
                      rfl

theorem cell22_294202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_294202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294202 prefixEnd_294202 := by exact prefixLift 294202
  have htrace : WordTrace (prefixWord ++ tailWord_294202) baseStart_294202 baseEnd_294202 := by
    simpa [prefixWord, tailWord_294202, baseEnd_294202] using wordTrace_append hprefix tailTrace_294202
  have hstable : (prefixWord ++ tailWord_294202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294202).length < 2 ^ (prefixWord ++ tailWord_294202).sum := by decide
  have hdescent : baseEnd_294202 < baseStart_294202 := by decide
  rcases family_descends (prefixWord ++ tailWord_294202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294204 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_294204 : Nat := 118140960795 + 294204 * 2 ^ 59
def prefixEnd_294204 : Nat := 4983230072969 + 3 ^ 40 * 294204 * 2
def baseEnd_294204 : Nat := 33570680550104924265997

theorem tailTrace_294204 : CollatzResearch.WordTrace tailWord_294204 prefixEnd_294204 33570680550104924265997 := by
  unfold tailWord_294204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365250713078314444008833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7153667617437752592011777 5365250713078314444008833)
  ·
    refine ⟨4023938034808735833006625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5365250713078314444008833 4023938034808735833006625)
    ·
      refine ⟨3017953526106551874754969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4023938034808735833006625 3017953526106551874754969)
      ·
        refine ⟨2263465144579913906066227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3017953526106551874754969 2263465144579913906066227)
        ·
          refine ⟨3395197716869870859099341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263465144579913906066227 3395197716869870859099341)
          ·
            refine ⟨1273199143826201572162253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3395197716869870859099341 1273199143826201572162253)
            ·
              refine ⟨477449678934825589560845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1273199143826201572162253 477449678934825589560845)
              ·
                refine ⟨179043629600559596085317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477449678934825589560845 179043629600559596085317)
                ·
                  refine ⟨33570680550104924265997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179043629600559596085317 33570680550104924265997)
                  ·
                    rfl

theorem cell22_294204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_294204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294204 prefixEnd_294204 := by exact prefixLift 294204
  have htrace : WordTrace (prefixWord ++ tailWord_294204) baseStart_294204 baseEnd_294204 := by
    simpa [prefixWord, tailWord_294204, baseEnd_294204] using wordTrace_append hprefix tailTrace_294204
  have hstable : (prefixWord ++ tailWord_294204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294204).length < 2 ^ (prefixWord ++ tailWord_294204).sum := by decide
  have hdescent : baseEnd_294204 < baseStart_294204 := by decide
  rcases family_descends (prefixWord ++ tailWord_294204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294215 : List Nat := [1, 1, 4, 1, 2, 3, 10]
def baseStart_294215 : Nat := 118140960795 + 294215 * 2 ^ 59
def prefixEnd_294215 : Nat := 4983230072969 + 3 ^ 40 * 294215 * 2
def baseEnd_294215 : Nat := 3730215080559792991591

theorem tailTrace_294215 : CollatzResearch.WordTrace tailWord_294215 prefixEnd_294215 3730215080559792991591 := by
  unfold tailWord_294215
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730902629116777766668099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153935086077851844445399 10730902629116777766668099)
  ·
    refine ⟨16096353943675166650002149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10730902629116777766668099 16096353943675166650002149)
    ·
      refine ⟨3018066364439093746875403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16096353943675166650002149 3018066364439093746875403)
      ·
        refine ⟨4527099546658640620313105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018066364439093746875403 4527099546658640620313105)
        ·
          refine ⟨3395324659993980465234829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527099546658640620313105 3395324659993980465234829)
          ·
            refine ⟨1273246747497742674463061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3395324659993980465234829 1273246747497742674463061)
            ·
              refine ⟨3730215080559792991591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1273246747497742674463061 3730215080559792991591)
              ·
                rfl

theorem cell22_294215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 10].length) (baseStart_294215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294215 prefixEnd_294215 := by exact prefixLift 294215
  have htrace : WordTrace (prefixWord ++ tailWord_294215) baseStart_294215 baseEnd_294215 := by
    simpa [prefixWord, tailWord_294215, baseEnd_294215] using wordTrace_append hprefix tailTrace_294215
  have hstable : (prefixWord ++ tailWord_294215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294215).length < 2 ^ (prefixWord ++ tailWord_294215).sum := by decide
  have hdescent : baseEnd_294215 < baseStart_294215 := by decide
  rcases family_descends (prefixWord ++ tailWord_294215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294270 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_294270 : Nat := 118140960795 + 294270 * 2 ^ 59
def prefixEnd_294270 : Nat := 4983230072969 + 3 ^ 40 * 294270 * 2
def baseEnd_294270 : Nat := 100734634799112600647789

theorem tailTrace_294270 : CollatzResearch.WordTrace tailWord_294270 prefixEnd_294270 100734634799112600647789 := by
  unfold tailWord_294270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341613580489690269990033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7155272429278348106613509 1341613580489690269990033)
  ·
    refine ⟨1006210185367267702492525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1341613580489690269990033 1006210185367267702492525)
    ·
      refine ⟨377328819512725388434697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1006210185367267702492525 377328819512725388434697)
      ·
        refine ⟨282996614634544041326023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377328819512725388434697 282996614634544041326023)
        ·
          refine ⟨424494921951816061989035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282996614634544041326023 424494921951816061989035)
          ·
            refine ⟨636742382927724092983553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424494921951816061989035 636742382927724092983553)
            ·
              refine ⟨477556787195793069737665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636742382927724092983553 477556787195793069737665)
              ·
                refine ⟨358167590396844802303249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477556787195793069737665 358167590396844802303249)
                ·
                  refine ⟨268625692797633601727437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358167590396844802303249 268625692797633601727437)
                  ·
                    refine ⟨100734634799112600647789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268625692797633601727437 100734634799112600647789)
                    ·
                      rfl

theorem cell22_294270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_294270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294270 prefixEnd_294270 := by exact prefixLift 294270
  have htrace : WordTrace (prefixWord ++ tailWord_294270) baseStart_294270 baseEnd_294270 := by
    simpa [prefixWord, tailWord_294270, baseEnd_294270] using wordTrace_append hprefix tailTrace_294270
  have hstable : (prefixWord ++ tailWord_294270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294270).length < 2 ^ (prefixWord ++ tailWord_294270).sum := by decide
  have hdescent : baseEnd_294270 < baseStart_294270 := by decide
  rcases family_descends (prefixWord ++ tailWord_294270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294277 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 5]
def baseStart_294277 : Nat := 118140960795 + 294277 * 2 ^ 59
def prefixEnd_294277 : Nat := 4983230072969 + 3 ^ 40 * 294277 * 2
def baseEnd_294277 : Nat := 33579010347388971907589

theorem tailTrace_294277 : CollatzResearch.WordTrace tailWord_294277 prefixEnd_294277 33579010347388971907589 := by
  unfold tailWord_294277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733163954892162355425085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7155442636594774903616723 10733163954892162355425085)
  ·
    refine ⟨4024936483084560883284407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10733163954892162355425085 4024936483084560883284407)
    ·
      refine ⟨6037404724626841324926611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024936483084560883284407 6037404724626841324926611)
      ·
        refine ⟨9056107086940261987389917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037404724626841324926611 9056107086940261987389917)
        ·
          refine ⟨3396040157602598245271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9056107086940261987389917 3396040157602598245271219)
          ·
            refine ⟨5094060236403897367906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396040157602598245271219 5094060236403897367906829)
            ·
              refine ⟨1910272588651461512965061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5094060236403897367906829 1910272588651461512965061)
              ·
                refine ⟨358176110372149033680949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1910272588651461512965061 358176110372149033680949)
                ·
                  refine ⟨33579010347388971907589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358176110372149033680949 33579010347388971907589)
                  ·
                    rfl

theorem cell22_294277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_294277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294277 prefixEnd_294277 := by exact prefixLift 294277
  have htrace : WordTrace (prefixWord ++ tailWord_294277) baseStart_294277 baseEnd_294277 := by
    simpa [prefixWord, tailWord_294277, baseEnd_294277] using wordTrace_append hprefix tailTrace_294277
  have hstable : (prefixWord ++ tailWord_294277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294277).length < 2 ^ (prefixWord ++ tailWord_294277).sum := by decide
  have hdescent : baseEnd_294277 < baseStart_294277 := by decide
  rcases family_descends (prefixWord ++ tailWord_294277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294307 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_294307 : Nat := 118140960795 + 294307 * 2 ^ 59
def prefixEnd_294307 : Nat := 4983230072969 + 3 ^ 40 * 294307 * 2
def baseEnd_294307 : Nat := 100747300655256837472675

theorem tailTrace_294307 : CollatzResearch.WordTrace tailWord_294307 prefixEnd_294307 100747300655256837472675 := by
  unfold tailWord_294307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734258144783477479017175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7156172096522318319344783 10734258144783477479017175)
  ·
    refine ⟨16101387217175216218525763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10734258144783477479017175 16101387217175216218525763)
    ·
      refine ⟨24152080825762824327788645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16101387217175216218525763 24152080825762824327788645)
      ·
        refine ⟨4528515154830529561460371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24152080825762824327788645 4528515154830529561460371)
        ·
          refine ⟨6792772732245794342190557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528515154830529561460371 6792772732245794342190557)
          ·
            refine ⟨2547289774592172878321459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6792772732245794342190557 2547289774592172878321459)
            ·
              refine ⟨3820934661888259317482189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547289774592172878321459 3820934661888259317482189)
              ·
                refine ⟨1432850498208097244055821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3820934661888259317482189 1432850498208097244055821)
                ·
                  refine ⟨537318936828036466520933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1432850498208097244055821 537318936828036466520933)
                  ·
                    refine ⟨100747300655256837472675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537318936828036466520933 100747300655256837472675)
                    ·
                      rfl

theorem cell22_294307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_294307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294307 prefixEnd_294307 := by exact prefixLift 294307
  have htrace : WordTrace (prefixWord ++ tailWord_294307) baseStart_294307 baseEnd_294307 := by
    simpa [prefixWord, tailWord_294307, baseEnd_294307] using wordTrace_append hprefix tailTrace_294307
  have hstable : (prefixWord ++ tailWord_294307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294307).length < 2 ^ (prefixWord ++ tailWord_294307).sum := by decide
  have hdescent : baseEnd_294307 < baseStart_294307 := by decide
  rcases family_descends (prefixWord ++ tailWord_294307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294339 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 4]
def baseStart_294339 : Nat := 118140960795 + 294339 * 2 ^ 59
def prefixEnd_294339 : Nat := 4983230072969 + 3 ^ 40 * 294339 * 2
def baseEnd_294339 : Nat := 33586084969739806890859

theorem tailTrace_294339 : CollatzResearch.WordTrace tailWord_294339 prefixEnd_294339 33586084969739806890859 := by
  unfold tailWord_294339
  simp only [CollatzResearch.WordTrace]
  refine ⟨10735425280667546944182071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7156950187111697962788047 10735425280667546944182071)
  ·
    refine ⟨16103137921001320416273107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10735425280667546944182071 16103137921001320416273107)
    ·
      refine ⟨24154706881501980624409661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103137921001320416273107 24154706881501980624409661)
      ·
        refine ⟨9058015080563242734153623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24154706881501980624409661 9058015080563242734153623)
        ·
          refine ⟨13587022620844864101230435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058015080563242734153623 13587022620844864101230435)
          ·
            refine ⟨20380533931267296151845653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587022620844864101230435 20380533931267296151845653)
            ·
              refine ⟨955337528028154507117765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20380533931267296151845653 955337528028154507117765)
              ·
                refine ⟨179125786505278970084581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 955337528028154507117765 179125786505278970084581)
                ·
                  refine ⟨33586084969739806890859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179125786505278970084581 33586084969739806890859)
                  ·
                    rfl

theorem cell22_294339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 4].length) (baseStart_294339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294339 prefixEnd_294339 := by exact prefixLift 294339
  have htrace : WordTrace (prefixWord ++ tailWord_294339) baseStart_294339 baseEnd_294339 := by
    simpa [prefixWord, tailWord_294339, baseEnd_294339] using wordTrace_append hprefix tailTrace_294339
  have hstable : (prefixWord ++ tailWord_294339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294339).length < 2 ^ (prefixWord ++ tailWord_294339).sum := by decide
  have hdescent : baseEnd_294339 < baseStart_294339 := by decide
  rcases family_descends (prefixWord ++ tailWord_294339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294352 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_294352 : Nat := 118140960795 + 294352 * 2 ^ 59
def prefixEnd_294352 : Nat := 4983230072969 + 3 ^ 40 * 294352 * 2
def baseEnd_294352 : Nat := 100762705074891720097537

theorem tailTrace_294352 : CollatzResearch.WordTrace tailWord_294352 prefixEnd_294352 100762705074891720097537 := by
  unfold tailWord_294352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367949714810225082202655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7157266286413633442936873 5367949714810225082202655)
  ·
    refine ⟨8051924572215337623303983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5367949714810225082202655 8051924572215337623303983)
    ·
      refine ⟨12077886858323006434955975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8051924572215337623303983 12077886858323006434955975)
      ·
        refine ⟨18116830287484509652433963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12077886858323006434955975 18116830287484509652433963)
        ·
          refine ⟨27175245431226764478650945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18116830287484509652433963 27175245431226764478650945)
          ·
            refine ⟨20381434073420073358988209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27175245431226764478650945 20381434073420073358988209)
            ·
              refine ⟨15286075555065055019241157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20381434073420073358988209 15286075555065055019241157)
              ·
                refine ⟨2866139166574697816107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15286075555065055019241157 2866139166574697816107717)
                ·
                  refine ⟨537401093732755840520197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2866139166574697816107717 537401093732755840520197)
                  ·
                    refine ⟨100762705074891720097537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537401093732755840520197 100762705074891720097537)
                    ·
                      rfl

theorem cell22_294352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_294352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294352 prefixEnd_294352 := by exact prefixLift 294352
  have htrace : WordTrace (prefixWord ++ tailWord_294352) baseStart_294352 baseEnd_294352 := by
    simpa [prefixWord, tailWord_294352, baseEnd_294352] using wordTrace_append hprefix tailTrace_294352
  have hstable : (prefixWord ++ tailWord_294352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294352).length < 2 ^ (prefixWord ++ tailWord_294352).sum := by decide
  have hdescent : baseEnd_294352 < baseStart_294352 := by decide
  rcases family_descends (prefixWord ++ tailWord_294352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294358 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_294358 : Nat := 118140960795 + 294358 * 2 ^ 59
def prefixEnd_294358 : Nat := 4983230072969 + 3 ^ 40 * 294358 * 2
def baseEnd_294358 : Nat := 100764758997509704447519

theorem tailTrace_294358 : CollatzResearch.WordTrace tailWord_294358 prefixEnd_294358 100764758997509704447519 := by
  unfold tailWord_294358
  simp only [CollatzResearch.WordTrace]
  refine ⟨671007391724919574320233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7157412178399142126082485 671007391724919574320233)
  ·
    refine ⟨503255543793689680740175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 671007391724919574320233 503255543793689680740175)
    ·
      refine ⟨754883315690534521110263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503255543793689680740175 754883315690534521110263)
      ·
        refine ⟨1132324973535801781665395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754883315690534521110263 1132324973535801781665395)
        ·
          refine ⟨1698487460303702672498093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132324973535801781665395 1698487460303702672498093)
          ·
            refine ⟨636932797613888502186785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698487460303702672498093 636932797613888502186785)
            ·
              refine ⟨477699598210416376640089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636932797613888502186785 477699598210416376640089)
              ·
                refine ⟨358274698657812282480067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477699598210416376640089 358274698657812282480067)
                ·
                  refine ⟨537412047986718423720101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358274698657812282480067 537412047986718423720101)
                  ·
                    refine ⟨100764758997509704447519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537412047986718423720101 100764758997509704447519)
                    ·
                      rfl

theorem cell22_294358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_294358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294358 prefixEnd_294358 := by exact prefixLift 294358
  have htrace : WordTrace (prefixWord ++ tailWord_294358) baseStart_294358 baseEnd_294358 := by
    simpa [prefixWord, tailWord_294358, baseEnd_294358] using wordTrace_append hprefix tailTrace_294358
  have hstable : (prefixWord ++ tailWord_294358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294358).length < 2 ^ (prefixWord ++ tailWord_294358).sum := by decide
  have hdescent : baseEnd_294358 < baseStart_294358 := by decide
  rcases family_descends (prefixWord ++ tailWord_294358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294367 : List Nat := [1, 1, 2, 3, 3, 1, 3, 8]
def baseStart_294367 : Nat := 118140960795 + 294367 * 2 ^ 59
def prefixEnd_294367 : Nat := 4983230072969 + 3 ^ 40 * 294367 * 2
def baseEnd_294367 : Nat := 11196426653492964552499

theorem tailTrace_294367 : CollatzResearch.WordTrace tailWord_294367 prefixEnd_294367 11196426653492964552499 := by
  unfold tailWord_294367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736446524566107726201355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7157631016377405150800903 10736446524566107726201355)
  ·
    refine ⟨16104669786849161589302033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10736446524566107726201355 16104669786849161589302033)
    ·
      refine ⟨12078502340136871191976525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16104669786849161589302033 12078502340136871191976525)
      ·
        refine ⟨4529438377551326696991197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12078502340136871191976525 4529438377551326696991197)
        ·
          refine ⟨1698539391581747511371699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4529438377551326696991197 1698539391581747511371699)
          ·
            refine ⟨2547809087372621267057549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698539391581747511371699 2547809087372621267057549)
            ·
              refine ⟨955428407764732975146581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2547809087372621267057549 955428407764732975146581)
              ·
                refine ⟨11196426653492964552499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 955428407764732975146581 11196426653492964552499)
                ·
                  rfl

theorem cell22_294367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 8].length) (baseStart_294367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294367 prefixEnd_294367 := by exact prefixLift 294367
  have htrace : WordTrace (prefixWord ++ tailWord_294367) baseStart_294367 baseEnd_294367 := by
    simpa [prefixWord, tailWord_294367, baseEnd_294367] using wordTrace_append hprefix tailTrace_294367
  have hstable : (prefixWord ++ tailWord_294367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294367).length < 2 ^ (prefixWord ++ tailWord_294367).sum := by decide
  have hdescent : baseEnd_294367 < baseStart_294367 := by decide
  rcases family_descends (prefixWord ++ tailWord_294367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294373 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 4]
def baseStart_294373 : Nat := 118140960795 + 294373 * 2 ^ 59
def prefixEnd_294373 : Nat := 4983230072969 + 3 ^ 40 * 294373 * 2
def baseEnd_294373 : Nat := 33589964601351555107491

theorem tailTrace_294373 : CollatzResearch.WordTrace tailWord_294373 prefixEnd_294373 33589964601351555107491 := by
  unfold tailWord_294373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736665362544370750919773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7157776908362913833946515 10736665362544370750919773)
  ·
    refine ⟨4026249510954139031594915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10736665362544370750919773 4026249510954139031594915)
    ·
      refine ⟨6039374266431208547392373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4026249510954139031594915 6039374266431208547392373)
      ·
        refine ⟨566191337477925801318035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6039374266431208547392373 566191337477925801318035)
        ·
          refine ⟨849287006216888701977053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566191337477925801318035 849287006216888701977053)
          ·
            refine ⟨318482627331333263241395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 849287006216888701977053 318482627331333263241395)
            ·
              refine ⟨477723940996999894862093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318482627331333263241395 477723940996999894862093)
              ·
                refine ⟨179146477873874960573285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477723940996999894862093 179146477873874960573285)
                ·
                  refine ⟨33589964601351555107491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179146477873874960573285 33589964601351555107491)
                  ·
                    rfl

theorem cell22_294373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_294373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294373 prefixEnd_294373 := by exact prefixLift 294373
  have htrace : WordTrace (prefixWord ++ tailWord_294373) baseStart_294373 baseEnd_294373 := by
    simpa [prefixWord, tailWord_294373, baseEnd_294373] using wordTrace_append hprefix tailTrace_294373
  have hstable : (prefixWord ++ tailWord_294373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294373).length < 2 ^ (prefixWord ++ tailWord_294373).sum := by decide
  have hdescent : baseEnd_294373 < baseStart_294373 := by decide
  rcases family_descends (prefixWord ++ tailWord_294373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294386 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_294386 : Nat := 118140960795 + 294386 * 2 ^ 59
def prefixEnd_294386 : Nat := 4983230072969 + 3 ^ 40 * 294386 * 2
def baseEnd_294386 : Nat := 100774343969726964747433

theorem tailTrace_294386 : CollatzResearch.WordTrace tailWord_294386 prefixEnd_294386 100774343969726964747433 := by
  unfold tailWord_294386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684284877874318492785753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7158093007664849314095341 2684284877874318492785753)
  ·
    refine ⟨2013213658405738869589315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684284877874318492785753 2013213658405738869589315)
    ·
      refine ⟨3019820487608608304383973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013213658405738869589315 3019820487608608304383973)
      ·
        refine ⟨566216341426614057071995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3019820487608608304383973 566216341426614057071995)
        ·
          refine ⟨849324512139921085607993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566216341426614057071995 849324512139921085607993)
          ·
            refine ⟨636993384104940814205995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849324512139921085607993 636993384104940814205995)
            ·
              refine ⟨955490076157411221308993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636993384104940814205995 955490076157411221308993)
              ·
                refine ⟨716617557118058415981745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955490076157411221308993 716617557118058415981745)
                ·
                  refine ⟨537463167838543811986309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716617557118058415981745 537463167838543811986309)
                  ·
                    refine ⟨100774343969726964747433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537463167838543811986309 100774343969726964747433)
                    ·
                      rfl

theorem cell22_294386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_294386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294386 prefixEnd_294386 := by exact prefixLift 294386
  have htrace : WordTrace (prefixWord ++ tailWord_294386) baseStart_294386 baseEnd_294386 := by
    simpa [prefixWord, tailWord_294386, baseEnd_294386] using wordTrace_append hprefix tailTrace_294386
  have hstable : (prefixWord ++ tailWord_294386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294386).length < 2 ^ (prefixWord ++ tailWord_294386).sum := by decide
  have hdescent : baseEnd_294386 < baseStart_294386 := by decide
  rcases family_descends (prefixWord ++ tailWord_294386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294399 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 3, 3]
def baseStart_294399 : Nat := 118140960795 + 294399 * 2 ^ 59
def prefixEnd_294399 : Nat := 4983230072969 + 3 ^ 40 * 294399 * 2
def baseEnd_294399 : Nat := 100778794135399264172393

theorem tailTrace_294399 : CollatzResearch.WordTrace tailWord_294399 prefixEnd_294399 100778794135399264172393 := by
  unfold tailWord_294399
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737613660450177191366251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7158409106966784794244167 10737613660450177191366251)
  ·
    refine ⟨16106420490675265787049377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10737613660450177191366251 16106420490675265787049377)
    ·
      refine ⟨12079815368006449340287033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16106420490675265787049377 12079815368006449340287033)
      ·
        refine ⟨9059861526004837005215275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12079815368006449340287033 9059861526004837005215275)
        ·
          refine ⟨13589792289007255507822913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9059861526004837005215275 13589792289007255507822913)
          ·
            refine ⟨10192344216755441630867185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13589792289007255507822913 10192344216755441630867185)
            ·
              refine ⟨7644258162566581223150389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10192344216755441630867185 7644258162566581223150389)
              ·
                refine ⟨716649202740616989670349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7644258162566581223150389 716649202740616989670349)
                ·
                  refine ⟨268743451027731371126381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716649202740616989670349 268743451027731371126381)
                  ·
                    refine ⟨100778794135399264172393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268743451027731371126381 100778794135399264172393)
                    ·
                      rfl

theorem cell22_294399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_294399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294399 prefixEnd_294399 := by exact prefixLift 294399
  have htrace : WordTrace (prefixWord ++ tailWord_294399) baseStart_294399 baseEnd_294399 := by
    simpa [prefixWord, tailWord_294399, baseEnd_294399] using wordTrace_append hprefix tailTrace_294399
  have hstable : (prefixWord ++ tailWord_294399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294399).length < 2 ^ (prefixWord ++ tailWord_294399).sum := by decide
  have hdescent : baseEnd_294399 < baseStart_294399 := by decide
  rcases family_descends (prefixWord ++ tailWord_294399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294446 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_294446 : Nat := 118140960795 + 294446 * 2 ^ 59
def prefixEnd_294446 : Nat := 4983230072969 + 3 ^ 40 * 294446 * 2
def baseEnd_294446 : Nat := 33598294398635602749083

theorem tailTrace_294446 : CollatzResearch.WordTrace tailWord_294446 prefixEnd_294446 33598294398635602749083 := by
  unfold tailWord_294446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342415986409988027290899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7159551927519936145551461 1342415986409988027290899)
  ·
    refine ⟨2013623979614982040936349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342415986409988027290899 2013623979614982040936349)
    ·
      refine ⟨755108992355618265351131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2013623979614982040936349 755108992355618265351131)
      ·
        refine ⟨1132663488533427398026697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755108992355618265351131 1132663488533427398026697)
        ·
          refine ⟨849497616400070548520023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132663488533427398026697 849497616400070548520023)
          ·
            refine ⟨1274246424600105822780035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849497616400070548520023 1274246424600105822780035)
            ·
              refine ⟨1911369636900158734170053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274246424600105822780035 1911369636900158734170053)
              ·
                refine ⟨358381806918779762656885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1911369636900158734170053 358381806918779762656885)
                ·
                  refine ⟨33598294398635602749083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358381806918779762656885 33598294398635602749083)
                  ·
                    rfl

theorem cell22_294446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_294446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294446 prefixEnd_294446 := by exact prefixLift 294446
  have htrace : WordTrace (prefixWord ++ tailWord_294446) baseStart_294446 baseEnd_294446 := by
    simpa [prefixWord, tailWord_294446, baseEnd_294446] using wordTrace_append hprefix tailTrace_294446
  have hstable : (prefixWord ++ tailWord_294446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294446).length < 2 ^ (prefixWord ++ tailWord_294446).sum := by decide
  have hdescent : baseEnd_294446 < baseStart_294446 := by decide
  rcases family_descends (prefixWord ++ tailWord_294446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294461 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_294461 : Nat := 118140960795 + 294461 * 2 ^ 59
def prefixEnd_294461 : Nat := 4983230072969 + 3 ^ 40 * 294461 * 2
def baseEnd_294461 : Nat := 100800018002451769122203

theorem tailTrace_294461 : CollatzResearch.WordTrace tailWord_294461 prefixEnd_294461 100800018002451769122203 := by
  unfold tailWord_294461
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739874986225561780123237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7159916657483707853415491 10739874986225561780123237)
  ·
    refine ⟨2013726559917292833773107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10739874986225561780123237 2013726559917292833773107)
    ·
      refine ⟨3020589839875939250659661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013726559917292833773107 3020589839875939250659661)
      ·
        refine ⟨1132721189953477218997373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3020589839875939250659661 1132721189953477218997373)
        ·
          refine ⟨424770446232553957124015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1132721189953477218997373 424770446232553957124015)
          ·
            refine ⟨637155669348830935686023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424770446232553957124015 637155669348830935686023)
            ·
              refine ⟨955733504023246403529035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637155669348830935686023 955733504023246403529035)
              ·
                refine ⟨1433600256034869605293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955733504023246403529035 1433600256034869605293553)
                ·
                  refine ⟨1075200192026152203970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433600256034869605293553 1075200192026152203970165)
                  ·
                    refine ⟨100800018002451769122203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1075200192026152203970165 100800018002451769122203)
                    ·
                      rfl

theorem cell22_294461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_294461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294461 prefixEnd_294461 := by exact prefixLift 294461
  have htrace : WordTrace (prefixWord ++ tailWord_294461) baseStart_294461 baseEnd_294461 := by
    simpa [prefixWord, tailWord_294461, baseEnd_294461] using wordTrace_append hprefix tailTrace_294461
  have hstable : (prefixWord ++ tailWord_294461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294461).length < 2 ^ (prefixWord ++ tailWord_294461).sum := by decide
  have hdescent : baseEnd_294461 < baseStart_294461 := by decide
  rcases family_descends (prefixWord ++ tailWord_294461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294474 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_294474 : Nat := 118140960795 + 294474 * 2 ^ 59
def prefixEnd_294474 : Nat := 4983230072969 + 3 ^ 40 * 294474 * 2
def baseEnd_294474 : Nat := 33601489389374689515721

theorem tailTrace_294474 : CollatzResearch.WordTrace tailWord_294474 prefixEnd_294474 33601489389374689515721 := by
  unfold tailWord_294474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685087283794616250086619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7160232756785643333564317 2685087283794616250086619)
  ·
    refine ⟨4027630925691924375129929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2685087283794616250086619 4027630925691924375129929)
    ·
      refine ⟨3020723194268943281347447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4027630925691924375129929 3020723194268943281347447)
      ·
        refine ⟨4531084791403414922021171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020723194268943281347447 4531084791403414922021171)
        ·
          refine ⟨6796627187105122383031757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531084791403414922021171 6796627187105122383031757)
          ·
            refine ⟨2548735195164420893636909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6796627187105122383031757 2548735195164420893636909)
            ·
              refine ⟨955775698186657835113841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548735195164420893636909 955775698186657835113841)
              ·
                refine ⟨716831773639993376335381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955775698186657835113841 716831773639993376335381)
                ·
                  refine ⟨33601489389374689515721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 716831773639993376335381 33601489389374689515721)
                  ·
                    rfl

theorem cell22_294474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_294474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294474 prefixEnd_294474 := by exact prefixLift 294474
  have htrace : WordTrace (prefixWord ++ tailWord_294474) baseStart_294474 baseEnd_294474 := by
    simpa [prefixWord, tailWord_294474, baseEnd_294474] using wordTrace_append hprefix tailTrace_294474
  have hstable : (prefixWord ++ tailWord_294474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294474).length < 2 ^ (prefixWord ++ tailWord_294474).sum := by decide
  have hdescent : baseEnd_294474 < baseStart_294474 := by decide
  rcases family_descends (prefixWord ++ tailWord_294474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294523 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 2, 3]
def baseStart_294523 : Nat := 118140960795 + 294523 * 2 ^ 59
def prefixEnd_294523 : Nat := 4983230072969 + 3 ^ 40 * 294523 * 2
def baseEnd_294523 : Nat := 100821241869504274072013

theorem tailTrace_294523 : CollatzResearch.WordTrace tailWord_294523 prefixEnd_294523 100821241869504274072013 := by
  unfold tailWord_294523
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742136312000946368880223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7161424208000630912586815 10742136312000946368880223)
  ·
    refine ⟨16113204468001419553320335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742136312000946368880223 16113204468001419553320335)
    ·
      refine ⟨24169806702002129329980503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16113204468001419553320335 24169806702002129329980503)
      ·
        refine ⟨36254710053003193994970755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24169806702002129329980503 36254710053003193994970755)
        ·
          refine ⟨54382065079504790992456133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36254710053003193994970755 54382065079504790992456133)
          ·
            refine ⟨10196637202407148311085525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54382065079504790992456133 10196637202407148311085525)
            ·
              refine ⟨238983684431417538541067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10196637202407148311085525 238983684431417538541067)
              ·
                refine ⟨358475526647126307811601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238983684431417538541067 358475526647126307811601)
                ·
                  refine ⟨268856644985344730858701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358475526647126307811601 268856644985344730858701)
                  ·
                    refine ⟨100821241869504274072013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268856644985344730858701 100821241869504274072013)
                    ·
                      rfl

theorem cell22_294523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 3].length) (baseStart_294523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294523 prefixEnd_294523 := by exact prefixLift 294523
  have htrace : WordTrace (prefixWord ++ tailWord_294523) baseStart_294523 baseEnd_294523 := by
    simpa [prefixWord, tailWord_294523, baseEnd_294523] using wordTrace_append hprefix tailTrace_294523
  have hstable : (prefixWord ++ tailWord_294523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294523).length < 2 ^ (prefixWord ++ tailWord_294523).sum := by decide
  have hdescent : baseEnd_294523 < baseStart_294523 := by decide
  rcases family_descends (prefixWord ++ tailWord_294523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294574 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_294574 : Nat := 118140960795 + 294574 * 2 ^ 59
def prefixEnd_294574 : Nat := 4983230072969 + 3 ^ 40 * 294574 * 2
def baseEnd_294574 : Nat := 100838700211757141046857

theorem tailTrace_294574 : CollatzResearch.WordTrace tailWord_294574 prefixEnd_294574 100838700211757141046857 := by
  unfold tailWord_294574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342999554352022759873347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7162664289877454719324517 1342999554352022759873347)
  ·
    refine ⟨2014499331528034139810021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342999554352022759873347 2014499331528034139810021)
    ·
      refine ⟨377718624661506401214379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2014499331528034139810021 377718624661506401214379)
      ·
        refine ⟨566577936992259601821569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377718624661506401214379 566577936992259601821569)
        ·
          refine ⟨424933452744194701366177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566577936992259601821569 424933452744194701366177)
          ·
            refine ⟨318700089558146026024633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424933452744194701366177 318700089558146026024633)
            ·
              refine ⟨239025067168609519518475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318700089558146026024633 239025067168609519518475)
              ·
                refine ⟨358537600752914279277713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239025067168609519518475 358537600752914279277713)
                ·
                  refine ⟨268903200564685709458285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358537600752914279277713 268903200564685709458285)
                  ·
                    refine ⟨100838700211757141046857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268903200564685709458285 100838700211757141046857)
                    ·
                      rfl

theorem cell22_294574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_294574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294574 prefixEnd_294574 := by exact prefixLift 294574
  have htrace : WordTrace (prefixWord ++ tailWord_294574) baseStart_294574 baseEnd_294574 := by
    simpa [prefixWord, tailWord_294574, baseEnd_294574] using wordTrace_append hprefix tailTrace_294574
  have hstable : (prefixWord ++ tailWord_294574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294574).length < 2 ^ (prefixWord ++ tailWord_294574).sum := by decide
  have hdescent : baseEnd_294574 < baseStart_294574 := by decide
  rcases family_descends (prefixWord ++ tailWord_294574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294579 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_294579 : Nat := 118140960795 + 294579 * 2 ^ 59
def prefixEnd_294579 : Nat := 4983230072969 + 3 ^ 40 * 294579 * 2
def baseEnd_294579 : Nat := 100840411813938794671841

theorem tailTrace_294579 : CollatzResearch.WordTrace tailWord_294579 prefixEnd_294579 100840411813938794671841 := by
  unfold tailWord_294579
  simp only [CollatzResearch.WordTrace]
  refine ⟨10744178799798067932918791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7162785866532045288612527 10744178799798067932918791)
  ·
    refine ⟨16116268199697101899378187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10744178799798067932918791 16116268199697101899378187)
    ·
      refine ⟨24174402299545652849067281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16116268199697101899378187 24174402299545652849067281)
      ·
        refine ⟨18130801724659239636800461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24174402299545652849067281 18130801724659239636800461)
        ·
          refine ⟨6799050646747214863800173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18130801724659239636800461 6799050646747214863800173)
          ·
            refine ⟨2549643992530205573925065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6799050646747214863800173 2549643992530205573925065)
            ·
              refine ⟨1912232994397654180443799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549643992530205573925065 1912232994397654180443799)
              ·
                refine ⟨2868349491596481270665699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912232994397654180443799 2868349491596481270665699)
                ·
                  refine ⟨4302524237394721905998549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868349491596481270665699 4302524237394721905998549)
                  ·
                    refine ⟨100840411813938794671841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4302524237394721905998549 100840411813938794671841)
                    ·
                      rfl

theorem cell22_294579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_294579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294579 prefixEnd_294579 := by exact prefixLift 294579
  have htrace : WordTrace (prefixWord ++ tailWord_294579) baseStart_294579 baseEnd_294579 := by
    simpa [prefixWord, tailWord_294579, baseEnd_294579] using wordTrace_append hprefix tailTrace_294579
  have hstable : (prefixWord ++ tailWord_294579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294579).length < 2 ^ (prefixWord ++ tailWord_294579).sum := by decide
  have hdescent : baseEnd_294579 < baseStart_294579 := by decide
  rcases family_descends (prefixWord ++ tailWord_294579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294641 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_294641 : Nat := 118140960795 + 294641 * 2 ^ 59
def prefixEnd_294641 : Nat := 4983230072969 + 3 ^ 40 * 294641 * 2
def baseEnd_294641 : Nat := 100861635680991299621651

theorem tailTrace_294641 : CollatzResearch.WordTrace tailWord_294641 prefixEnd_294641 100861635680991299621651 := by
  unfold tailWord_294641
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746440125573452521675777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7164293417048968347783851 10746440125573452521675777)
  ·
    refine ⟨8059830094180089391256833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10746440125573452521675777 8059830094180089391256833)
    ·
      refine ⟨6044872570635067043442625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8059830094180089391256833 6044872570635067043442625)
      ·
        refine ⟨4533654427976300282581969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6044872570635067043442625 4533654427976300282581969)
        ·
          refine ⟨3400240820982225211936477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4533654427976300282581969 3400240820982225211936477)
          ·
            refine ⟨1275090307868334454476179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3400240820982225211936477 1275090307868334454476179)
            ·
              refine ⟨1912635461802501681714269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275090307868334454476179 1912635461802501681714269)
              ·
                refine ⟨717238298175938130642851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1912635461802501681714269 717238298175938130642851)
                ·
                  refine ⟨1075857447263907195964277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717238298175938130642851 1075857447263907195964277)
                  ·
                    refine ⟨100861635680991299621651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1075857447263907195964277 100861635680991299621651)
                    ·
                      rfl

theorem cell22_294641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_294641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294641 prefixEnd_294641 := by exact prefixLift 294641
  have htrace : WordTrace (prefixWord ++ tailWord_294641) baseStart_294641 baseEnd_294641 := by
    simpa [prefixWord, tailWord_294641, baseEnd_294641] using wordTrace_append hprefix tailTrace_294641
  have hstable : (prefixWord ++ tailWord_294641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294641).length < 2 ^ (prefixWord ++ tailWord_294641).sum := by decide
  have hdescent : baseEnd_294641 < baseStart_294641 := by decide
  rcases family_descends (prefixWord ++ tailWord_294641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294658 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_294658 : Nat := 118140960795 + 294658 * 2 ^ 59
def prefixEnd_294658 : Nat := 4983230072969 + 3 ^ 40 * 294658 * 2
def baseEnd_294658 : Nat := 100867455128408921946599

theorem tailTrace_294658 : CollatzResearch.WordTrace tailWord_294658 prefixEnd_294658 100867455128408921946599 := by
  unfold tailWord_294658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686765041627966106261157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7164706777674576283363085 2686765041627966106261157)
  ·
    refine ⟨503768445305243644923967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2686765041627966106261157 503768445305243644923967)
    ·
      refine ⟨755652667957865467385951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503768445305243644923967 755652667957865467385951)
      ·
        refine ⟨1133479001936798201078927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755652667957865467385951 1133479001936798201078927)
        ·
          refine ⟨1700218502905197301618391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133479001936798201078927 1700218502905197301618391)
          ·
            refine ⟨2550327754357795952427587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700218502905197301618391 2550327754357795952427587)
            ·
              refine ⟨3825491631536693928641381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550327754357795952427587 3825491631536693928641381)
              ·
                refine ⟨717279680913130111620259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3825491631536693928641381 717279680913130111620259)
                ·
                  refine ⟨1075919521369695167430389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717279680913130111620259 1075919521369695167430389)
                  ·
                    refine ⟨100867455128408921946599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1075919521369695167430389 100867455128408921946599)
                    ·
                      rfl

theorem cell22_294658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_294658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294658 prefixEnd_294658 := by exact prefixLift 294658
  have htrace : WordTrace (prefixWord ++ tailWord_294658) baseStart_294658 baseEnd_294658 := by
    simpa [prefixWord, tailWord_294658, baseEnd_294658] using wordTrace_append hprefix tailTrace_294658
  have hstable : (prefixWord ++ tailWord_294658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294658).length < 2 ^ (prefixWord ++ tailWord_294658).sum := by decide
  have hdescent : baseEnd_294658 < baseStart_294658 := by decide
  rcases family_descends (prefixWord ++ tailWord_294658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294660 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_294660 : Nat := 118140960795 + 294660 * 2 ^ 59
def prefixEnd_294660 : Nat := 4983230072969 + 3 ^ 40 * 294660 * 2
def baseEnd_294660 : Nat := 33622713256427194465531

theorem tailTrace_294660 : CollatzResearch.WordTrace tailWord_294660 prefixEnd_294660 33622713256427194465531 := by
  unfold tailWord_294660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373566556252309383308717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7164755408336412511078289 5373566556252309383308717)
  ·
    refine ⟨2015087458594616018740769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5373566556252309383308717 2015087458594616018740769)
    ·
      refine ⟨1511315593945962014055577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015087458594616018740769 1511315593945962014055577)
      ·
        refine ⟨1133486695459471510541683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1511315593945962014055577 1133486695459471510541683)
        ·
          refine ⟨1700230043189207265812525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133486695459471510541683 1700230043189207265812525)
          ·
            refine ⟨637586266195952724679697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1700230043189207265812525 637586266195952724679697)
            ·
              refine ⟨478189699646964543509773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637586266195952724679697 478189699646964543509773)
              ·
                refine ⟨179321137367611703816165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478189699646964543509773 179321137367611703816165)
                ·
                  refine ⟨33622713256427194465531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179321137367611703816165 33622713256427194465531)
                  ·
                    rfl

theorem cell22_294660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_294660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294660 prefixEnd_294660 := by exact prefixLift 294660
  have htrace : WordTrace (prefixWord ++ tailWord_294660) baseStart_294660 baseEnd_294660 := by
    simpa [prefixWord, tailWord_294660, baseEnd_294660] using wordTrace_append hprefix tailTrace_294660
  have hstable : (prefixWord ++ tailWord_294660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294660).length < 2 ^ (prefixWord ++ tailWord_294660).sum := by decide
  have hdescent : baseEnd_294660 < baseStart_294660 := by decide
  rcases family_descends (prefixWord ++ tailWord_294660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294692 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_294692 : Nat := 118140960795 + 294692 * 2 ^ 59
def prefixEnd_294692 : Nat := 4983230072969 + 3 ^ 40 * 294692 * 2
def baseEnd_294692 : Nat := 100879094023244166596495

theorem tailTrace_294692 : CollatzResearch.WordTrace tailWord_294692 prefixEnd_294692 100879094023244166596495 := by
  unfold tailWord_294692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374150124194344115891165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7165533498925792154521553 5374150124194344115891165)
  ·
    refine ⟨2015306296572879043459187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5374150124194344115891165 2015306296572879043459187)
    ·
      refine ⟨3022959444859318565188781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015306296572879043459187 3022959444859318565188781)
      ·
        refine ⟨1133609791822244461945793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3022959444859318565188781 1133609791822244461945793)
        ·
          refine ⟨850207343866683346459345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133609791822244461945793 850207343866683346459345)
          ·
            refine ⟨637655507900012509844509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850207343866683346459345 637655507900012509844509)
            ·
              refine ⟨239120815462504691191691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 637655507900012509844509 239120815462504691191691)
              ·
                refine ⟨358681223193757036787537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239120815462504691191691 358681223193757036787537)
                ·
                  refine ⟨269010917395317777590653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358681223193757036787537 269010917395317777590653)
                  ·
                    refine ⟨100879094023244166596495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269010917395317777590653 100879094023244166596495)
                    ·
                      rfl

theorem cell22_294692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_294692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294692 prefixEnd_294692 := by exact prefixLift 294692
  have htrace : WordTrace (prefixWord ++ tailWord_294692) baseStart_294692 baseEnd_294692 := by
    simpa [prefixWord, tailWord_294692, baseEnd_294692] using wordTrace_append hprefix tailTrace_294692
  have hstable : (prefixWord ++ tailWord_294692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294692).length < 2 ^ (prefixWord ++ tailWord_294692).sum := by decide
  have hdescent : baseEnd_294692 < baseStart_294692 := by decide
  rcases family_descends (prefixWord ++ tailWord_294692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294716 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_294716 : Nat := 118140960795 + 294716 * 2 ^ 59
def prefixEnd_294716 : Nat := 4983230072969 + 3 ^ 40 * 294716 * 2
def baseEnd_294716 : Nat := 33629103237905367998807

theorem tailTrace_294716 : CollatzResearch.WordTrace tailWord_294716 prefixEnd_294716 33629103237905367998807 := by
  unfold tailWord_294716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374587800150870165328001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7166117066867826887104001 5374587800150870165328001)
  ·
    refine ⟨4030940850113152623996001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5374587800150870165328001 4030940850113152623996001)
    ·
      refine ⟨3023205637584864467997001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4030940850113152623996001 3023205637584864467997001)
      ·
        refine ⟨2267404228188648350997751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023205637584864467997001 2267404228188648350997751)
        ·
          refine ⟨3401106342282972526496627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267404228188648350997751 3401106342282972526496627)
          ·
            refine ⟨5101659513424458789744941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401106342282972526496627 5101659513424458789744941)
            ·
              refine ⟨1913122317534172046154353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5101659513424458789744941 1913122317534172046154353)
              ·
                refine ⟨1434841738150629034615765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913122317534172046154353 1434841738150629034615765)
                ·
                  refine ⟨33629103237905367998807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1434841738150629034615765 33629103237905367998807)
                  ·
                    rfl

theorem cell22_294716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_294716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294716 prefixEnd_294716 := by exact prefixLift 294716
  have htrace : WordTrace (prefixWord ++ tailWord_294716) baseStart_294716 baseEnd_294716 := by
    simpa [prefixWord, tailWord_294716, baseEnd_294716] using wordTrace_append hprefix tailTrace_294716
  have hstable : (prefixWord ++ tailWord_294716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294716).length < 2 ^ (prefixWord ++ tailWord_294716).sum := by decide
  have hdescent : baseEnd_294716 < baseStart_294716 := by decide
  rcases family_descends (prefixWord ++ tailWord_294716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294761 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 6]
def baseStart_294761 : Nat := 118140960795 + 294761 * 2 ^ 59
def prefixEnd_294761 : Nat := 4983230072969 + 3 ^ 40 * 294761 * 2
def baseEnd_294761 : Nat := 33634238044450328873761

theorem tailTrace_294761 : CollatzResearch.WordTrace tailWord_294761 prefixEnd_294761 33634238044450328873761 := by
  unfold tailWord_294761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750816885138713016044137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7167211256759142010696091 10750816885138713016044137)
  ·
    refine ⟨8063112663854034762033103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10750816885138713016044137 8063112663854034762033103)
    ·
      refine ⟨12094668995781052143049655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8063112663854034762033103 12094668995781052143049655)
      ·
        refine ⟨18142003493671578214574483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12094668995781052143049655 18142003493671578214574483)
        ·
          refine ⟨27213005240507367321861725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18142003493671578214574483 27213005240507367321861725)
          ·
            refine ⟨10204876965190262745698147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27213005240507367321861725 10204876965190262745698147)
            ·
              refine ⟨15307315447785394118547221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10204876965190262745698147 15307315447785394118547221)
              ·
                refine ⟨717530411614940349306901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15307315447785394118547221 717530411614940349306901)
                ·
                  refine ⟨33634238044450328873761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 717530411614940349306901 33634238044450328873761)
                  ·
                    rfl

theorem cell22_294761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_294761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294761 prefixEnd_294761 := by exact prefixLift 294761
  have htrace : WordTrace (prefixWord ++ tailWord_294761) baseStart_294761 baseEnd_294761 := by
    simpa [prefixWord, tailWord_294761, baseEnd_294761] using wordTrace_append hprefix tailTrace_294761
  have hstable : (prefixWord ++ tailWord_294761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294761).length < 2 ^ (prefixWord ++ tailWord_294761).sum := by decide
  have hdescent : baseEnd_294761 < baseStart_294761 := by decide
  rcases family_descends (prefixWord ++ tailWord_294761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294810 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_294810 : Nat := 118140960795 + 294810 * 2 ^ 59
def prefixEnd_294810 : Nat := 4983230072969 + 3 ^ 40 * 294810 * 2
def baseEnd_294810 : Nat := 100919487834731192146133

theorem tailTrace_294810 : CollatzResearch.WordTrace tailWord_294810 prefixEnd_294810 100919487834731192146133 := by
  unfold tailWord_294810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688151015490298596144471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7168402707974129589718589 2688151015490298596144471)
  ·
    refine ⟨4032226523235447894216707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688151015490298596144471 4032226523235447894216707)
    ·
      refine ⟨6048339784853171841325061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032226523235447894216707 6048339784853171841325061)
      ·
        refine ⟨1134063709659969720248449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6048339784853171841325061 1134063709659969720248449)
        ·
          refine ⟨850547782244977290186337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134063709659969720248449 850547782244977290186337)
          ·
            refine ⟨637910836683732967639753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850547782244977290186337 637910836683732967639753)
            ·
              refine ⟨478433127512799725729815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637910836683732967639753 478433127512799725729815)
              ·
                refine ⟨717649691269199588594723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478433127512799725729815 717649691269199588594723)
                ·
                  refine ⟨1076474536903799382892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717649691269199588594723 1076474536903799382892085)
                  ·
                    refine ⟨100919487834731192146133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1076474536903799382892085 100919487834731192146133)
                    ·
                      rfl

theorem cell22_294810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_294810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294810 prefixEnd_294810 := by exact prefixLift 294810
  have htrace : WordTrace (prefixWord ++ tailWord_294810) baseStart_294810 baseEnd_294810 := by
    simpa [prefixWord, tailWord_294810, baseEnd_294810] using wordTrace_append hprefix tailTrace_294810
  have hstable : (prefixWord ++ tailWord_294810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294810).length < 2 ^ (prefixWord ++ tailWord_294810).sum := by decide
  have hdescent : baseEnd_294810 < baseStart_294810 := by decide
  rcases family_descends (prefixWord ++ tailWord_294810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294960 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_294960 : Nat := 118140960795 + 294960 * 2 ^ 59
def prefixEnd_294960 : Nat := 4983230072969 + 3 ^ 40 * 294960 * 2
def baseEnd_294960 : Nat := 100970835900180800895673

theorem tailTrace_294960 : CollatzResearch.WordTrace tailWord_294960 prefixEnd_294960 100970835900180800895673 := by
  unfold tailWord_294960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379037505708885001269167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7172050007611846668358889 5379037505708885001269167)
  ·
    refine ⟨8068556258563327501903751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5379037505708885001269167 8068556258563327501903751)
    ·
      refine ⟨12102834387844991252855627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068556258563327501903751 12102834387844991252855627)
      ·
        refine ⟨18154251581767486879283441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12102834387844991252855627 18154251581767486879283441)
        ·
          refine ⟨13615688686325615159462581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18154251581767486879283441 13615688686325615159462581)
          ·
            refine ⟨1276470814343026421199617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13615688686325615159462581 1276470814343026421199617)
            ·
              refine ⟨957353110757269815899713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276470814343026421199617 957353110757269815899713)
              ·
                refine ⟨718014833067952361924785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957353110757269815899713 718014833067952361924785)
                ·
                  refine ⟨538511124800964271443589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718014833067952361924785 538511124800964271443589)
                  ·
                    refine ⟨100970835900180800895673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538511124800964271443589 100970835900180800895673)
                    ·
                      rfl

theorem cell22_294960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_294960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294960 prefixEnd_294960 := by exact prefixLift 294960
  have htrace : WordTrace (prefixWord ++ tailWord_294960) baseStart_294960 baseEnd_294960 := by
    simpa [prefixWord, tailWord_294960, baseEnd_294960] using wordTrace_append hprefix tailTrace_294960
  have hstable : (prefixWord ++ tailWord_294960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294960).length < 2 ^ (prefixWord ++ tailWord_294960).sum := by decide
  have hdescent : baseEnd_294960 < baseStart_294960 := by decide
  rcases family_descends (prefixWord ++ tailWord_294960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294962 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_294962 : Nat := 118140960795 + 294962 * 2 ^ 59
def prefixEnd_294962 : Nat := 4983230072969 + 3 ^ 40 * 294962 * 2
def baseEnd_294962 : Nat := 100971520541053462345667

theorem tailTrace_294962 : CollatzResearch.WordTrace tailWord_294962 prefixEnd_294962 100971520541053462345667 := by
  unfold tailWord_294962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689536989352631086027785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7172098638273682896074093 2689536989352631086027785)
  ·
    refine ⟨2017152742014473314520839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2689536989352631086027785 2017152742014473314520839)
    ·
      refine ⟨3025729113021709971781259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017152742014473314520839 3025729113021709971781259)
      ·
        refine ⟨4538593669532564957671889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025729113021709971781259 4538593669532564957671889)
        ·
          refine ⟨3403945252149423718253917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4538593669532564957671889 3403945252149423718253917)
          ·
            refine ⟨1276479469556033894345219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3403945252149423718253917 1276479469556033894345219)
            ·
              refine ⟨1914719204334050841517829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276479469556033894345219 1914719204334050841517829)
              ·
                refine ⟨359009850812634532784593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1914719204334050841517829 359009850812634532784593)
                ·
                  refine ⟨269257388109475899588445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359009850812634532784593 269257388109475899588445)
                  ·
                    refine ⟨100971520541053462345667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269257388109475899588445 100971520541053462345667)
                    ·
                      rfl

theorem cell22_294962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_294962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294962 prefixEnd_294962 := by exact prefixLift 294962
  have htrace : WordTrace (prefixWord ++ tailWord_294962) baseStart_294962 baseEnd_294962 := by
    simpa [prefixWord, tailWord_294962, baseEnd_294962] using wordTrace_append hprefix tailTrace_294962
  have hstable : (prefixWord ++ tailWord_294962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294962).length < 2 ^ (prefixWord ++ tailWord_294962).sum := by decide
  have hdescent : baseEnd_294962 < baseStart_294962 := by decide
  rcases family_descends (prefixWord ++ tailWord_294962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294994 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_294994 : Nat := 118140960795 + 294994 * 2 ^ 59
def prefixEnd_294994 : Nat := 4983230072969 + 3 ^ 40 * 294994 * 2
def baseEnd_294994 : Nat := 100982474795016045545569

theorem tailTrace_294994 : CollatzResearch.WordTrace tailWord_294994 prefixEnd_294994 100982474795016045545569 := by
  unfold tailWord_294994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689828773323648452319009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7172876728863062539517357 2689828773323648452319009)
  ·
    refine ⟨2017371579992736339239257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2689828773323648452319009 2017371579992736339239257)
    ·
      refine ⟨1513028684994552254429443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2017371579992736339239257 1513028684994552254429443)
      ·
        refine ⟨2269543027491828381644165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513028684994552254429443 2269543027491828381644165)
        ·
          refine ⟨425539317654717821558281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2269543027491828381644165 425539317654717821558281)
          ·
            refine ⟨319154488241038366168711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425539317654717821558281 319154488241038366168711)
            ·
              refine ⟨478731732361557549253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319154488241038366168711 478731732361557549253067)
              ·
                refine ⟨718097598542336323879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478731732361557549253067 718097598542336323879601)
                ·
                  refine ⟨538573198906752242909701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718097598542336323879601 538573198906752242909701)
                  ·
                    refine ⟨100982474795016045545569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538573198906752242909701 100982474795016045545569)
                    ·
                      rfl

theorem cell22_294994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_294994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_294994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_294994 prefixEnd_294994 := by exact prefixLift 294994
  have htrace : WordTrace (prefixWord ++ tailWord_294994) baseStart_294994 baseEnd_294994 := by
    simpa [prefixWord, tailWord_294994, baseEnd_294994] using wordTrace_append hprefix tailTrace_294994
  have hstable : (prefixWord ++ tailWord_294994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294994).length < 2 ^ (prefixWord ++ tailWord_294994).sum := by decide
  have hdescent : baseEnd_294994 < baseStart_294994 := by decide
  rcases family_descends (prefixWord ++ tailWord_294994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295020 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_295020 : Nat := 118140960795 + 295020 * 2 ^ 59
def prefixEnd_295020 : Nat := 4983230072969 + 3 ^ 40 * 295020 * 2
def baseEnd_295020 : Nat := 33663791708786881465163

theorem tailTrace_295020 : CollatzResearch.WordTrace tailWord_295020 prefixEnd_295020 33663791708786881465163 := by
  unfold tailWord_295020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380131695600200124861257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7173508927466933499815009 5380131695600200124861257)
  ·
    refine ⟨4035098771700150093645943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5380131695600200124861257 4035098771700150093645943)
    ·
      refine ⟨6052648157550225140468915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035098771700150093645943 6052648157550225140468915)
      ·
        refine ⟨9078972236325337710703373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052648157550225140468915 9078972236325337710703373)
        ·
          refine ⟨3404614588622001641513765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9078972236325337710703373 3404614588622001641513765)
          ·
            refine ⟨638365235366625307783831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3404614588622001641513765 638365235366625307783831)
            ·
              refine ⟨957547853049937961675747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638365235366625307783831 957547853049937961675747)
              ·
                refine ⟨1436321779574906942513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957547853049937961675747 1436321779574906942513621)
                ·
                  refine ⟨33663791708786881465163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1436321779574906942513621 33663791708786881465163)
                  ·
                    rfl

theorem cell22_295020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_295020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295020 prefixEnd_295020 := by exact prefixLift 295020
  have htrace : WordTrace (prefixWord ++ tailWord_295020) baseStart_295020 baseEnd_295020 := by
    simpa [prefixWord, tailWord_295020, baseEnd_295020] using wordTrace_append hprefix tailTrace_295020
  have hstable : (prefixWord ++ tailWord_295020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295020).length < 2 ^ (prefixWord ++ tailWord_295020).sum := by decide
  have hdescent : baseEnd_295020 < baseStart_295020 := by decide
  rcases family_descends (prefixWord ++ tailWord_295020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295024 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_295024 : Nat := 118140960795 + 295024 * 2 ^ 59
def prefixEnd_295024 : Nat := 4983230072969 + 3 ^ 40 * 295024 * 2
def baseEnd_295024 : Nat := 100992744408105967295477

theorem tailTrace_295024 : CollatzResearch.WordTrace tailWord_295024 prefixEnd_295024 100992744408105967295477 := by
  unfold tailWord_295024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380204641592954466434063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7173606188790605955245417 5380204641592954466434063)
  ·
    refine ⟨8070306962389431699651095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5380204641592954466434063 8070306962389431699651095)
    ·
      refine ⟨12105460443584147549476643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070306962389431699651095 12105460443584147549476643)
      ·
        refine ⟨18158190665376221324214965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105460443584147549476643 18158190665376221324214965)
        ·
          refine ⟨1702330374879020749145153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18158190665376221324214965 1702330374879020749145153)
          ·
            refine ⟨1276747781159265561858865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702330374879020749145153 1276747781159265561858865)
            ·
              refine ⟨957560835869449171394149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276747781159265561858865 957560835869449171394149)
              ·
                refine ⟨179542656725521719636403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 957560835869449171394149 179542656725521719636403)
                ·
                  refine ⟨269313985088282579454605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179542656725521719636403 269313985088282579454605)
                  ·
                    refine ⟨100992744408105967295477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269313985088282579454605 100992744408105967295477)
                    ·
                      rfl

theorem cell22_295024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_295024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295024 prefixEnd_295024 := by exact prefixLift 295024
  have htrace : WordTrace (prefixWord ++ tailWord_295024) baseStart_295024 baseEnd_295024 := by
    simpa [prefixWord, tailWord_295024, baseEnd_295024] using wordTrace_append hprefix tailTrace_295024
  have hstable : (prefixWord ++ tailWord_295024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295024).length < 2 ^ (prefixWord ++ tailWord_295024).sum := by decide
  have hdescent : baseEnd_295024 < baseStart_295024 := by decide
  rcases family_descends (prefixWord ++ tailWord_295024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295133 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 4]
def baseStart_295133 : Nat := 118140960795 + 295133 * 2 ^ 59
def prefixEnd_295133 : Nat := 4983230072969 + 3 ^ 40 * 295133 * 2
def baseEnd_295133 : Nat := 33676685778555338773381

theorem tailTrace_295133 : CollatzResearch.WordTrace tailWord_295133 prefixEnd_295133 33676685778555338773381 := by
  unfold tailWord_295133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764384839791020548586053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7176256559860680365724035 10764384839791020548586053)
  ·
    refine ⟨2018322157460816352859885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10764384839791020548586053 2018322157460816352859885)
    ·
      refine ⟨756870809047806132322457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2018322157460816352859885 756870809047806132322457)
      ·
        refine ⟨567653106785854599241843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756870809047806132322457 567653106785854599241843)
        ·
          refine ⟨851479660178781898862765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567653106785854599241843 851479660178781898862765)
          ·
            refine ⟨319304872567043212073537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 851479660178781898862765 319304872567043212073537)
            ·
              refine ⟨239478654425282409055153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319304872567043212073537 239478654425282409055153)
              ·
                refine ⟨179608990818961806791365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239478654425282409055153 179608990818961806791365)
                ·
                  refine ⟨33676685778555338773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179608990818961806791365 33676685778555338773381)
                  ·
                    rfl

theorem cell22_295133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_295133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295133 prefixEnd_295133 := by exact prefixLift 295133
  have htrace : WordTrace (prefixWord ++ tailWord_295133) baseStart_295133 baseEnd_295133 := by
    simpa [prefixWord, tailWord_295133, baseEnd_295133] using wordTrace_append hprefix tailTrace_295133
  have hstable : (prefixWord ++ tailWord_295133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295133).length < 2 ^ (prefixWord ++ tailWord_295133).sum := by decide
  have hdescent : baseEnd_295133 < baseStart_295133 := by decide
  rcases family_descends (prefixWord ++ tailWord_295133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295176 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_295176 : Nat := 118140960795 + 295176 * 2 ^ 59
def prefixEnd_295176 : Nat := 4983230072969 + 3 ^ 40 * 295176 * 2
def baseEnd_295176 : Nat := 101044777114428237495011

theorem tailTrace_295176 : CollatzResearch.WordTrace tailWord_295176 prefixEnd_295176 101044777114428237495011 := by
  unfold tailWord_295176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382976589317619446200691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7177302119090159261600921 5382976589317619446200691)
  ·
    refine ⟨8074464883976429169301037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5382976589317619446200691 8074464883976429169301037)
    ·
      refine ⟨3027924331491160938487889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8074464883976429169301037 3027924331491160938487889)
      ·
        refine ⟨2270943248618370703865917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027924331491160938487889 2270943248618370703865917)
        ·
          refine ⟨851603718231889013949719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2270943248618370703865917 851603718231889013949719)
          ·
            refine ⟨1277405577347833520924579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851603718231889013949719 1277405577347833520924579)
            ·
              refine ⟨1916108366021750281386869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277405577347833520924579 1916108366021750281386869)
              ·
                refine ⟨179635159314539088880019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1916108366021750281386869 179635159314539088880019)
                ·
                  refine ⟨269452738971808633320029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179635159314539088880019 269452738971808633320029)
                  ·
                    refine ⟨101044777114428237495011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269452738971808633320029 101044777114428237495011)
                    ·
                      rfl

theorem cell22_295176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_295176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295176 prefixEnd_295176 := by exact prefixLift 295176
  have htrace : WordTrace (prefixWord ++ tailWord_295176) baseStart_295176 baseEnd_295176 := by
    simpa [prefixWord, tailWord_295176, baseEnd_295176] using wordTrace_append hprefix tailTrace_295176
  have hstable : (prefixWord ++ tailWord_295176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295176).length < 2 ^ (prefixWord ++ tailWord_295176).sum := by decide
  have hdescent : baseEnd_295176 < baseStart_295176 := by decide
  rcases family_descends (prefixWord ++ tailWord_295176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295219 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 1, 4]
def baseStart_295219 : Nat := 118140960795 + 295219 * 2 ^ 59
def prefixEnd_295219 : Nat := 4983230072969 + 3 ^ 40 * 295219 * 2
def baseEnd_295219 : Nat := 101059496893190458669879

theorem tailTrace_295219 : CollatzResearch.WordTrace tailWord_295219 prefixEnd_295219 101059496893190458669879 := by
  unfold tailWord_295219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767521517479457236216711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7178347678319638157477807 10767521517479457236216711)
  ·
    refine ⟨16151282276219185854325067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10767521517479457236216711 16151282276219185854325067)
    ·
      refine ⟨24226923414328778781487601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16151282276219185854325067 24226923414328778781487601)
      ·
        refine ⟨18170192560746584086115701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24226923414328778781487601 18170192560746584086115701)
        ·
          refine ⟨1703455552569992258073347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18170192560746584086115701 1703455552569992258073347)
          ·
            refine ⟨2555183328854988387110021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703455552569992258073347 2555183328854988387110021)
            ·
              refine ⟨479096874160310322583129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2555183328854988387110021 479096874160310322583129)
              ·
                refine ⟨359322655620232741937347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479096874160310322583129 359322655620232741937347)
                ·
                  refine ⟨538983983430349112906021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359322655620232741937347 538983983430349112906021)
                  ·
                    refine ⟨101059496893190458669879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538983983430349112906021 101059496893190458669879)
                    ·
                      rfl

theorem cell22_295219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_295219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295219 prefixEnd_295219 := by exact prefixLift 295219
  have htrace : WordTrace (prefixWord ++ tailWord_295219) baseStart_295219 baseEnd_295219 := by
    simpa [prefixWord, tailWord_295219, baseEnd_295219] using wordTrace_append hprefix tailTrace_295219
  have hstable : (prefixWord ++ tailWord_295219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295219).length < 2 ^ (prefixWord ++ tailWord_295219).sum := by decide
  have hdescent : baseEnd_295219 < baseStart_295219 := by decide
  rcases family_descends (prefixWord ++ tailWord_295219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295249 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_295249 : Nat := 118140960795 + 295249 * 2 ^ 59
def prefixEnd_295249 : Nat := 4983230072969 + 3 ^ 40 * 295249 * 2
def baseEnd_295249 : Nat := 101069766506280380419787

theorem tailTrace_295249 : CollatzResearch.WordTrace tailWord_295249 prefixEnd_295249 101069766506280380419787 := by
  unfold tailWord_295249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10768615707370772359808801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7179077138247181573205867 10768615707370772359808801)
  ·
    refine ⟨8076461780528079269856601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10768615707370772359808801 8076461780528079269856601)
    ·
      refine ⟨6057346335396059452392451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8076461780528079269856601 6057346335396059452392451)
      ·
        refine ⟨9086019503094089178588677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057346335396059452392451 9086019503094089178588677)
        ·
          refine ⟨1703628656830141720985377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9086019503094089178588677 1703628656830141720985377)
          ·
            refine ⟨1277721492622606290739033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703628656830141720985377 1277721492622606290739033)
            ·
              refine ⟨958291119466954718054275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277721492622606290739033 958291119466954718054275)
              ·
                refine ⟨1437436679200432077081413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958291119466954718054275 1437436679200432077081413)
                ·
                  refine ⟨269519377350081014452765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437436679200432077081413 269519377350081014452765)
                  ·
                    refine ⟨101069766506280380419787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269519377350081014452765 101069766506280380419787)
                    ·
                      rfl

theorem cell22_295249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_295249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295249 prefixEnd_295249 := by exact prefixLift 295249
  have htrace : WordTrace (prefixWord ++ tailWord_295249) baseStart_295249 baseEnd_295249 := by
    simpa [prefixWord, tailWord_295249, baseEnd_295249] using wordTrace_append hprefix tailTrace_295249
  have hstable : (prefixWord ++ tailWord_295249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295249).length < 2 ^ (prefixWord ++ tailWord_295249).sum := by decide
  have hdescent : baseEnd_295249 < baseStart_295249 := by decide
  rcases family_descends (prefixWord ++ tailWord_295249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295352 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_295352 : Nat := 118140960795 + 295352 * 2 ^ 59
def prefixEnd_295352 : Nat := 4983230072969 + 3 ^ 40 * 295352 * 2
def baseEnd_295352 : Nat := 33701675170407481698157

theorem tailTrace_295352 : CollatzResearch.WordTrace tailWord_295352 prefixEnd_295352 33701675170407481698157 := by
  unfold tailWord_295352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5386186212998810475404155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7181581617331747300538873 5386186212998810475404155)
  ·
    refine ⟨8079279319498215713106233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5386186212998810475404155 8079279319498215713106233)
    ·
      refine ⟨6059459489623661784829675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079279319498215713106233 6059459489623661784829675)
      ·
        refine ⟨9089189234435492677244513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059459489623661784829675 9089189234435492677244513)
        ·
          refine ⟨6816891925826619507933385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9089189234435492677244513 6816891925826619507933385)
          ·
            refine ⟨5112668944369964630950039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816891925826619507933385 5112668944369964630950039)
            ·
              refine ⟨7669003416554946946425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112668944369964630950039 7669003416554946946425059)
              ·
                refine ⟨11503505124832420419637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669003416554946946425059 11503505124832420419637589)
                ·
                  refine ⟨33701675170407481698157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 11503505124832420419637589 33701675170407481698157)
                  ·
                    rfl

theorem cell22_295352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_295352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295352 prefixEnd_295352 := by exact prefixLift 295352
  have htrace : WordTrace (prefixWord ++ tailWord_295352) baseStart_295352 baseEnd_295352 := by
    simpa [prefixWord, tailWord_295352, baseEnd_295352] using wordTrace_append hprefix tailTrace_295352
  have hstable : (prefixWord ++ tailWord_295352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295352).length < 2 ^ (prefixWord ++ tailWord_295352).sum := by decide
  have hdescent : baseEnd_295352 < baseStart_295352 := by decide
  rcases family_descends (prefixWord ++ tailWord_295352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295399 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_295399 : Nat := 118140960795 + 295399 * 2 ^ 59
def prefixEnd_295399 : Nat := 4983230072969 + 3 ^ 40 * 295399 * 2
def baseEnd_295399 : Nat := 101121114571729989169327

theorem tailTrace_295399 : CollatzResearch.WordTrace tailWord_295399 prefixEnd_295399 101121114571729989169327 := by
  unfold tailWord_295399
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774086656827347977769251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7182724437884898651846167 10774086656827347977769251)
  ·
    refine ⟨16161129985241021966653877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10774086656827347977769251 16161129985241021966653877)
    ·
      refine ⟨1515105936116345809373801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16161129985241021966653877 1515105936116345809373801)
      ·
        refine ⟨1136329452087259357030351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1515105936116345809373801 1136329452087259357030351)
        ·
          refine ⟨1704494178130889035545527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136329452087259357030351 1704494178130889035545527)
          ·
            refine ⟨2556741267196333553318291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704494178130889035545527 2556741267196333553318291)
            ·
              refine ⟨3835111900794500329977437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556741267196333553318291 3835111900794500329977437)
              ·
                refine ⟨1438166962797937623741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3835111900794500329977437 1438166962797937623741539)
                ·
                  refine ⟨2157250444196906435612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438166962797937623741539 2157250444196906435612309)
                  ·
                    refine ⟨101121114571729989169327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2157250444196906435612309 101121114571729989169327)
                    ·
                      rfl

theorem cell22_295399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_295399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295399 prefixEnd_295399 := by exact prefixLift 295399
  have htrace : WordTrace (prefixWord ++ tailWord_295399) baseStart_295399 baseEnd_295399 := by
    simpa [prefixWord, tailWord_295399, baseEnd_295399] using wordTrace_append hprefix tailTrace_295399
  have hstable : (prefixWord ++ tailWord_295399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295399).length < 2 ^ (prefixWord ++ tailWord_295399).sum := by decide
  have hdescent : baseEnd_295399 < baseStart_295399 := by decide
  rcases family_descends (prefixWord ++ tailWord_295399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295431 : List Nat := [1, 1, 4, 3, 3, 1, 2, 7]
def baseStart_295431 : Nat := 118140960795 + 295431 * 2 ^ 59
def prefixEnd_295431 : Nat := 4983230072969 + 3 ^ 40 * 295431 * 2
def baseEnd_295431 : Nat := 11236896536188063596581

theorem tailTrace_295431 : CollatzResearch.WordTrace tailWord_295431 prefixEnd_295431 11236896536188063596581 := by
  unfold tailWord_295431
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775253792711417442934147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7183502528474278295289431 10775253792711417442934147)
  ·
    refine ⟨16162880689067126164401221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10775253792711417442934147 16162880689067126164401221)
    ·
      refine ⟨3030540129200086155825229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16162880689067126164401221 3030540129200086155825229)
      ·
        refine ⟨1136452548450032308434461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3030540129200086155825229 1136452548450032308434461)
        ·
          refine ⟨426169705668762115662923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136452548450032308434461 426169705668762115662923)
          ·
            refine ⟨639254558503143173494385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426169705668762115662923 639254558503143173494385)
            ·
              refine ⟨479440918877357380120789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639254558503143173494385 479440918877357380120789)
              ·
                refine ⟨11236896536188063596581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 479440918877357380120789 11236896536188063596581)
                ·
                  rfl

theorem cell22_295431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 7].length) (baseStart_295431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295431 prefixEnd_295431 := by exact prefixLift 295431
  have htrace : WordTrace (prefixWord ++ tailWord_295431) baseStart_295431 baseEnd_295431 := by
    simpa [prefixWord, tailWord_295431, baseEnd_295431] using wordTrace_append hprefix tailTrace_295431
  have hstable : (prefixWord ++ tailWord_295431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295431).length < 2 ^ (prefixWord ++ tailWord_295431).sum := by decide
  have hdescent : baseEnd_295431 < baseStart_295431 := by decide
  rcases family_descends (prefixWord ++ tailWord_295431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295435 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 2, 3]
def baseStart_295435 : Nat := 118140960795 + 295435 * 2 ^ 59
def prefixEnd_295435 : Nat := 4983230072969 + 3 ^ 40 * 295435 * 2
def baseEnd_295435 : Nat := 101133438107437895269217

theorem tailTrace_295435 : CollatzResearch.WordTrace tailWord_295435 prefixEnd_295435 101133438107437895269217 := by
  unfold tailWord_295435
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775399684696926126079759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7183599789797950750719839 10775399684696926126079759)
  ·
    refine ⟨16163099527045389189119639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10775399684696926126079759 16163099527045389189119639)
    ·
      refine ⟨24244649290568083783679459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16163099527045389189119639 24244649290568083783679459)
      ·
        refine ⟨36366973935852125675519189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24244649290568083783679459 36366973935852125675519189)
        ·
          refine ⟨852350951621534195519981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36366973935852125675519189 852350951621534195519981)
          ·
            refine ⟨319631606858075323319993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852350951621534195519981 319631606858075323319993)
            ·
              refine ⟨239723705143556492489995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319631606858075323319993 239723705143556492489995)
              ·
                refine ⟨359585557715334738734993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239723705143556492489995 359585557715334738734993)
                ·
                  refine ⟨269689168286501054051245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359585557715334738734993 269689168286501054051245)
                  ·
                    refine ⟨101133438107437895269217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269689168286501054051245 101133438107437895269217)
                    ·
                      rfl

theorem cell22_295435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 3].length) (baseStart_295435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295435 prefixEnd_295435 := by exact prefixLift 295435
  have htrace : WordTrace (prefixWord ++ tailWord_295435) baseStart_295435 baseEnd_295435 := by
    simpa [prefixWord, tailWord_295435, baseEnd_295435] using wordTrace_append hprefix tailTrace_295435
  have hstable : (prefixWord ++ tailWord_295435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295435).length < 2 ^ (prefixWord ++ tailWord_295435).sum := by decide
  have hdescent : baseEnd_295435 < baseStart_295435 := by decide
  rcases family_descends (prefixWord ++ tailWord_295435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295469 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_295469 : Nat := 118140960795 + 295469 * 2 ^ 59
def prefixEnd_295469 : Nat := 4983230072969 + 3 ^ 40 * 295469 * 2
def baseEnd_295469 : Nat := 101145077002273139919113

theorem tailTrace_295469 : CollatzResearch.WordTrace tailWord_295469 prefixEnd_295469 101145077002273139919113 := by
  unfold tailWord_295469
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776639766573749932817461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7184426511049166621878307 10776639766573749932817461)
  ·
    refine ⟨1010309978116289056201637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10776639766573749932817461 1010309978116289056201637)
    ·
      refine ⟨189433120896804198037807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1010309978116289056201637 189433120896804198037807)
      ·
        refine ⟨284149681345206297056711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189433120896804198037807 284149681345206297056711)
        ·
          refine ⟨426224522017809445585067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284149681345206297056711 426224522017809445585067)
          ·
            refine ⟨639336783026714168377601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426224522017809445585067 639336783026714168377601)
            ·
              refine ⟨479502587270035626283201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639336783026714168377601 479502587270035626283201)
              ·
                refine ⟨359626940452526719712401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479502587270035626283201 359626940452526719712401)
                ·
                  refine ⟨269720205339395039784301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359626940452526719712401 269720205339395039784301)
                  ·
                    refine ⟨101145077002273139919113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269720205339395039784301 101145077002273139919113)
                    ·
                      rfl

theorem cell22_295469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_295469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295469 prefixEnd_295469 := by exact prefixLift 295469
  have htrace : WordTrace (prefixWord ++ tailWord_295469) baseStart_295469 baseEnd_295469 := by
    simpa [prefixWord, tailWord_295469, baseEnd_295469] using wordTrace_append hprefix tailTrace_295469
  have hstable : (prefixWord ++ tailWord_295469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295469).length < 2 ^ (prefixWord ++ tailWord_295469).sum := by decide
  have hdescent : baseEnd_295469 < baseStart_295469 := by decide
  rcases family_descends (prefixWord ++ tailWord_295469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295506 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_295506 : Nat := 118140960795 + 295506 * 2 ^ 59
def prefixEnd_295506 : Nat := 4983230072969 + 3 ^ 40 * 295506 * 2
def baseEnd_295506 : Nat := 101157742858417376743999

theorem tailTrace_295506 : CollatzResearch.WordTrace tailWord_295506 prefixEnd_295506 101157742858417376743999 := by
  unfold tailWord_295506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694497316859926312978593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7185326178293136834609581 2694497316859926312978593)
  ·
    refine ⟨2020872987644944734733945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2694497316859926312978593 2020872987644944734733945)
    ·
      refine ⟨1515654740733708551050459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2020872987644944734733945 1515654740733708551050459)
      ·
        refine ⟨2273482111100562826575689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515654740733708551050459 2273482111100562826575689)
        ·
          refine ⟨1705111583325422119931767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273482111100562826575689 1705111583325422119931767)
          ·
            refine ⟨2557667374988133179897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705111583325422119931767 2557667374988133179897651)
            ·
              refine ⟨3836501062482199769846477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557667374988133179897651 3836501062482199769846477)
              ·
                refine ⟨1438687898430824913692429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3836501062482199769846477 1438687898430824913692429)
                ·
                  refine ⟨539507961911559342634661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1438687898430824913692429 539507961911559342634661)
                  ·
                    refine ⟨101157742858417376743999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 539507961911559342634661 101157742858417376743999)
                    ·
                      rfl

theorem cell22_295506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_295506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295506 prefixEnd_295506 := by exact prefixLift 295506
  have htrace : WordTrace (prefixWord ++ tailWord_295506) baseStart_295506 baseEnd_295506 := by
    simpa [prefixWord, tailWord_295506, baseEnd_295506] using wordTrace_append hprefix tailTrace_295506
  have hstable : (prefixWord ++ tailWord_295506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295506).length < 2 ^ (prefixWord ++ tailWord_295506).sum := by decide
  have hdescent : baseEnd_295506 < baseStart_295506 := by decide
  rcases family_descends (prefixWord ++ tailWord_295506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295538 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_295538 : Nat := 118140960795 + 295538 * 2 ^ 59
def prefixEnd_295538 : Nat := 4983230072969 + 3 ^ 40 * 295538 * 2
def baseEnd_295538 : Nat := 33722899037459986647967

theorem tailTrace_295538 : CollatzResearch.WordTrace tailWord_295538 prefixEnd_295538 33722899037459986647967 := by
  unfold tailWord_295538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694789100830943679269817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7186104268882516478052845 2694789100830943679269817)
  ·
    refine ⟨2021091825623207759452363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2694789100830943679269817 2021091825623207759452363)
    ·
      refine ⟨3031637738434811639178545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021091825623207759452363 3031637738434811639178545)
      ·
        refine ⟨2273728303826108729383909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3031637738434811639178545 2273728303826108729383909)
        ·
          refine ⟨426324056967395386759483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2273728303826108729383909 426324056967395386759483)
          ·
            refine ⟨639486085451093080139225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426324056967395386759483 639486085451093080139225)
            ·
              refine ⟨479614564088319810104419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639486085451093080139225 479614564088319810104419)
              ·
                refine ⟨719421846132479715156629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479614564088319810104419 719421846132479715156629)
                ·
                  refine ⟨33722899037459986647967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 719421846132479715156629 33722899037459986647967)
                  ·
                    rfl

theorem cell22_295538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_295538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295538 prefixEnd_295538 := by exact prefixLift 295538
  have htrace : WordTrace (prefixWord ++ tailWord_295538) baseStart_295538 baseEnd_295538 := by
    simpa [prefixWord, tailWord_295538, baseEnd_295538] using wordTrace_append hprefix tailTrace_295538
  have hstable : (prefixWord ++ tailWord_295538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295538).length < 2 ^ (prefixWord ++ tailWord_295538).sum := by decide
  have hdescent : baseEnd_295538 < baseStart_295538 := by decide
  rcases family_descends (prefixWord ++ tailWord_295538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295566 : List Nat := [4, 1, 1, 3, 1, 1, 3, 8]
def baseStart_295566 : Nat := 118140960795 + 295566 * 2 ^ 59
def prefixEnd_295566 : Nat := 4983230072969 + 3 ^ 40 * 295566 * 2
def baseEnd_295566 : Nat := 11242031342733024471535

theorem tailTrace_295566 : CollatzResearch.WordTrace tailWord_295566 prefixEnd_295566 11242031342733024471535 := by
  unfold tailWord_295566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347522205902791937387319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7186785098148223666065701 1347522205902791937387319)
  ·
    refine ⟨2021283308854187906080979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347522205902791937387319 2021283308854187906080979)
    ·
      refine ⟨3031924963281281859121469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021283308854187906080979 3031924963281281859121469)
      ·
        refine ⟨1136971861230480697170551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3031924963281281859121469 1136971861230480697170551)
        ·
          refine ⟨1705457791845721045755827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136971861230480697170551 1705457791845721045755827)
          ·
            refine ⟨2558186687768581568633741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705457791845721045755827 2558186687768581568633741)
            ·
              refine ⟨959320007913218088237653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2558186687768581568633741 959320007913218088237653)
              ·
                refine ⟨11242031342733024471535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 959320007913218088237653 11242031342733024471535)
                ·
                  rfl

theorem cell22_295566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_295566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295566 prefixEnd_295566 := by exact prefixLift 295566
  have htrace : WordTrace (prefixWord ++ tailWord_295566) baseStart_295566 baseEnd_295566 := by
    simpa [prefixWord, tailWord_295566, baseEnd_295566] using wordTrace_append hprefix tailTrace_295566
  have hstable : (prefixWord ++ tailWord_295566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295566).length < 2 ^ (prefixWord ++ tailWord_295566).sum := by decide
  have hdescent : baseEnd_295566 < baseStart_295566 := by decide
  rcases family_descends (prefixWord ++ tailWord_295566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295572 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_295572 : Nat := 118140960795 + 295572 * 2 ^ 59
def prefixEnd_295572 : Nat := 4983230072969 + 3 ^ 40 * 295572 * 2
def baseEnd_295572 : Nat := 33726778669071734864599

theorem tailTrace_295572 : CollatzResearch.WordTrace tailWord_295572 prefixEnd_295572 33726778669071734864599 := by
  unfold tailWord_295572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5390198242600299261908485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7186930990133732349211313 5390198242600299261908485)
  ·
    refine ⟨1010662170487556111607841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5390198242600299261908485 1010662170487556111607841)
    ·
      refine ⟨757996627865667083705881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010662170487556111607841 757996627865667083705881)
      ·
        refine ⟨568497470899250312779411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 757996627865667083705881 568497470899250312779411)
        ·
          refine ⟨852746206348875469169117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568497470899250312779411 852746206348875469169117)
          ·
            refine ⟨319779827380828300938419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852746206348875469169117 319779827380828300938419)
            ·
              refine ⟨479669741071242451407629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319779827380828300938419 479669741071242451407629)
              ·
                refine ⟨179876152901715919277861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479669741071242451407629 179876152901715919277861)
                ·
                  refine ⟨33726778669071734864599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179876152901715919277861 33726778669071734864599)
                  ·
                    rfl

theorem cell22_295572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_295572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295572 prefixEnd_295572 := by exact prefixLift 295572
  have htrace : WordTrace (prefixWord ++ tailWord_295572) baseStart_295572 baseEnd_295572 := by
    simpa [prefixWord, tailWord_295572, baseEnd_295572] using wordTrace_append hprefix tailTrace_295572
  have hstable : (prefixWord ++ tailWord_295572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295572).length < 2 ^ (prefixWord ++ tailWord_295572).sum := by decide
  have hdescent : baseEnd_295572 < baseStart_295572 := by decide
  rcases family_descends (prefixWord ++ tailWord_295572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295649 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_295649 : Nat := 118140960795 + 295649 * 2 ^ 59
def prefixEnd_295649 : Nat := 4983230072969 + 3 ^ 40 * 295649 * 2
def baseEnd_295649 : Nat := 101206694680812670418561

theorem tailTrace_295649 : CollatzResearch.WordTrace tailWord_295649 prefixEnd_295649 101206694680812670418561 := by
  unfold tailWord_295649
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783204905921640674370001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7188803270614427116246667 10783204905921640674370001)
  ·
    refine ⟨8087403679441230505777501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10783204905921640674370001 8087403679441230505777501)
    ·
      refine ⟨3032776379790461439666563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8087403679441230505777501 3032776379790461439666563)
      ·
        refine ⟨4549164569685692159499845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032776379790461439666563 4549164569685692159499845)
        ·
          refine ⟨852968356816067279906221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4549164569685692159499845 852968356816067279906221)
          ·
            refine ⟨319863133806025229964833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852968356816067279906221 319863133806025229964833)
            ·
              refine ⟨239897350354518922473625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319863133806025229964833 239897350354518922473625)
              ·
                refine ⟨179923012765889191855219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239897350354518922473625 179923012765889191855219)
                ·
                  refine ⟨269884519148833787782829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179923012765889191855219 269884519148833787782829)
                  ·
                    refine ⟨101206694680812670418561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269884519148833787782829 101206694680812670418561)
                    ·
                      rfl

theorem cell22_295649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_295649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295649 prefixEnd_295649 := by exact prefixLift 295649
  have htrace : WordTrace (prefixWord ++ tailWord_295649) baseStart_295649 baseEnd_295649 := by
    simpa [prefixWord, tailWord_295649, baseEnd_295649] using wordTrace_append hprefix tailTrace_295649
  have hstable : (prefixWord ++ tailWord_295649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295649).length < 2 ^ (prefixWord ++ tailWord_295649).sum := by decide
  have hdescent : baseEnd_295649 < baseStart_295649 := by decide
  rcases family_descends (prefixWord ++ tailWord_295649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295688 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_295688 : Nat := 118140960795 + 295688 * 2 ^ 59
def prefixEnd_295688 : Nat := 4983230072969 + 3 ^ 40 * 295688 * 2
def baseEnd_295688 : Nat := 101220045177829568693441

theorem tailTrace_295688 : CollatzResearch.WordTrace tailWord_295688 prefixEnd_295688 101220045177829568693441 := by
  unfold tailWord_295688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392313676390175167519859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7189751568520233556693145 5392313676390175167519859)
  ·
    refine ⟨8088470514585262751279789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5392313676390175167519859 8088470514585262751279789)
    ·
      refine ⟨3033176442969473531729921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8088470514585262751279789 3033176442969473531729921)
      ·
        refine ⟨2274882332227105148797441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3033176442969473531729921 2274882332227105148797441)
        ·
          refine ⟨1706161749170328861598081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274882332227105148797441 1706161749170328861598081)
          ·
            refine ⟨1279621311877746646198561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706161749170328861598081 1279621311877746646198561)
            ·
              refine ⟨959715983908309984648921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279621311877746646198561 959715983908309984648921)
              ·
                refine ⟨719786987931232488486691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959715983908309984648921 719786987931232488486691)
                ·
                  refine ⟨1079680481896848732730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719786987931232488486691 1079680481896848732730037)
                  ·
                    refine ⟨101220045177829568693441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1079680481896848732730037 101220045177829568693441)
                    ·
                      rfl

theorem cell22_295688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_295688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295688 prefixEnd_295688 := by exact prefixLift 295688
  have htrace : WordTrace (prefixWord ++ tailWord_295688) baseStart_295688 baseEnd_295688 := by
    simpa [prefixWord, tailWord_295688, baseEnd_295688] using wordTrace_append hprefix tailTrace_295688
  have hstable : (prefixWord ++ tailWord_295688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295688).length < 2 ^ (prefixWord ++ tailWord_295688).sum := by decide
  have hdescent : baseEnd_295688 < baseStart_295688 := by decide
  rcases family_descends (prefixWord ++ tailWord_295688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295690 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_295690 : Nat := 118140960795 + 295690 * 2 ^ 59
def prefixEnd_295690 : Nat := 4983230072969 + 3 ^ 40 * 295690 * 2
def baseEnd_295690 : Nat := 33740243272900743381145

theorem tailTrace_295690 : CollatzResearch.WordTrace tailWord_295690 prefixEnd_295690 33740243272900743381145 := by
  unfold tailWord_295690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696175074693276169153131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7189800199182069784408349 2696175074693276169153131)
  ·
    refine ⟨4044262612039914253729697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696175074693276169153131 4044262612039914253729697)
    ·
      refine ⟨3033196959029935690297273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4044262612039914253729697 3033196959029935690297273)
      ·
        refine ⟨2274897719272451767722955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3033196959029935690297273 2274897719272451767722955)
        ·
          refine ⟨3412346578908677651584433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274897719272451767722955 3412346578908677651584433)
          ·
            refine ⟨2559259934181508238688325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412346578908677651584433 2559259934181508238688325)
            ·
              refine ⟨479861237659032794754061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2559259934181508238688325 479861237659032794754061)
              ·
                refine ⟨179947964122137298032773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479861237659032794754061 179947964122137298032773)
                ·
                  refine ⟨33740243272900743381145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179947964122137298032773 33740243272900743381145)
                  ·
                    rfl

theorem cell22_295690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_295690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295690 prefixEnd_295690 := by exact prefixLift 295690
  have htrace : WordTrace (prefixWord ++ tailWord_295690) baseStart_295690 baseEnd_295690 := by
    simpa [prefixWord, tailWord_295690, baseEnd_295690] using wordTrace_append hprefix tailTrace_295690
  have hstable : (prefixWord ++ tailWord_295690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295690).length < 2 ^ (prefixWord ++ tailWord_295690).sum := by decide
  have hdescent : baseEnd_295690 < baseStart_295690 := by decide
  rcases family_descends (prefixWord ++ tailWord_295690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295701 : List Nat := [1, 3, 2, 1, 2, 2, 11]
def baseStart_295701 : Nat := 118140960795 + 295701 * 2 ^ 59
def prefixEnd_295701 : Nat := 4983230072969 + 3 ^ 40 * 295701 * 2
def baseEnd_295701 : Nat := 3749055383092661782163

theorem tailTrace_295701 : CollatzResearch.WordTrace tailWord_295701 prefixEnd_295701 3749055383092661782163 := by
  unfold tailWord_295701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10785101501733253555262957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7190067667822169036841971 10785101501733253555262957)
  ·
    refine ⟨4044413063149970083223609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10785101501733253555262957 4044413063149970083223609)
    ·
      refine ⟨3033309797362477562417707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4044413063149970083223609 3033309797362477562417707)
      ·
        refine ⟨4549964696043716343626561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033309797362477562417707 4549964696043716343626561)
        ·
          refine ⟨3412473522032787257719921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4549964696043716343626561 3412473522032787257719921)
          ·
            refine ⟨2559355141524590443289941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412473522032787257719921 2559355141524590443289941)
            ·
              refine ⟨3749055383092661782163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2559355141524590443289941 3749055383092661782163)
              ·
                rfl

theorem cell22_295701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 11].length) (baseStart_295701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295701 prefixEnd_295701 := by exact prefixLift 295701
  have htrace : WordTrace (prefixWord ++ tailWord_295701) baseStart_295701 baseEnd_295701 := by
    simpa [prefixWord, tailWord_295701, baseEnd_295701] using wordTrace_append hprefix tailTrace_295701
  have hstable : (prefixWord ++ tailWord_295701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295701).length < 2 ^ (prefixWord ++ tailWord_295701).sum := by decide
  have hdescent : baseEnd_295701 < baseStart_295701 := by decide
  rcases family_descends (prefixWord ++ tailWord_295701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295767 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 3, 3]
def baseStart_295767 : Nat := 118140960795 + 295767 * 2 ^ 59
def prefixEnd_295767 : Nat := 4983230072969 + 3 ^ 40 * 295767 * 2
def baseEnd_295767 : Nat := 101247088492299695968199

theorem tailTrace_295767 : CollatzResearch.WordTrace tailWord_295767 prefixEnd_295767 101247088492299695968199 := by
  unfold tailWord_295767
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787508719494146827165555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7191672479662764551443703 10787508719494146827165555)
  ·
    refine ⟨16181263079241220240748333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10787508719494146827165555 16181263079241220240748333)
    ·
      refine ⟨6067973654715457590280625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16181263079241220240748333 6067973654715457590280625)
      ·
        refine ⟨4550980241036593192710469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067973654715457590280625 4550980241036593192710469)
        ·
          refine ⟨853308795194361223633213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4550980241036593192710469 853308795194361223633213)
          ·
            refine ⟨319990798197885458862455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853308795194361223633213 319990798197885458862455)
            ·
              refine ⟨479986197296828188293683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319990798197885458862455 479986197296828188293683)
              ·
                refine ⟨719979295945242282440525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479986197296828188293683 719979295945242282440525)
                ·
                  refine ⟨269992235979465855915197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719979295945242282440525 269992235979465855915197)
                  ·
                    refine ⟨101247088492299695968199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269992235979465855915197 101247088492299695968199)
                    ·
                      rfl

theorem cell22_295767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_295767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295767 prefixEnd_295767 := by exact prefixLift 295767
  have htrace : WordTrace (prefixWord ++ tailWord_295767) baseStart_295767 baseEnd_295767 := by
    simpa [prefixWord, tailWord_295767, baseEnd_295767] using wordTrace_append hprefix tailTrace_295767
  have hstable : (prefixWord ++ tailWord_295767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295767).length < 2 ^ (prefixWord ++ tailWord_295767).sum := by decide
  have hdescent : baseEnd_295767 < baseStart_295767 := by decide
  rcases family_descends (prefixWord ++ tailWord_295767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295780 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_295780 : Nat := 118140960795 + 295780 * 2 ^ 59
def prefixEnd_295780 : Nat := 4983230072969 + 3 ^ 40 * 295780 * 2
def baseEnd_295780 : Nat := 33750512885990665131053

theorem tailTrace_295780 : CollatzResearch.WordTrace tailWord_295780 prefixEnd_295780 33750512885990665131053 := by
  unfold tailWord_295780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393991434223525023694397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7191988578964700031592529 5393991434223525023694397)
  ·
    refine ⟨2022746787833821883885399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5393991434223525023694397 2022746787833821883885399)
    ·
      refine ⟨3034120181750732825828099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022746787833821883885399 3034120181750732825828099)
      ·
        refine ⟨4551180272626099238742149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034120181750732825828099 4551180272626099238742149)
        ·
          refine ⟨853346301117393607264153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4551180272626099238742149 853346301117393607264153)
          ·
            refine ⟨640009725838045205448115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853346301117393607264153 640009725838045205448115)
            ·
              refine ⟨960014588757067808172173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640009725838045205448115 960014588757067808172173)
              ·
                refine ⟨360005470783900428064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960014588757067808172173 360005470783900428064565)
                ·
                  refine ⟨33750512885990665131053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360005470783900428064565 33750512885990665131053)
                  ·
                    rfl

theorem cell22_295780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_295780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295780 prefixEnd_295780 := by exact prefixLift 295780
  have htrace : WordTrace (prefixWord ++ tailWord_295780) baseStart_295780 baseEnd_295780 := by
    simpa [prefixWord, tailWord_295780, baseEnd_295780] using wordTrace_append hprefix tailTrace_295780
  have hstable : (prefixWord ++ tailWord_295780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295780).length < 2 ^ (prefixWord ++ tailWord_295780).sum := by decide
  have hdescent : baseEnd_295780 < baseStart_295780 := by decide
  rcases family_descends (prefixWord ++ tailWord_295780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295919 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 1, 3]
def baseStart_295919 : Nat := 118140960795 + 295919 * 2 ^ 59
def prefixEnd_295919 : Nat := 4983230072969 + 3 ^ 40 * 295919 * 2
def baseEnd_295919 : Nat := 101299121198621966167733

theorem tailTrace_295919 : CollatzResearch.WordTrace tailWord_295919 prefixEnd_295919 101299121198621966167733 := by
  unfold tailWord_295919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10793052614943476786698811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7195368409962317857799207 10793052614943476786698811)
  ·
    refine ⟨16189578922415215180048217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10793052614943476786698811 16189578922415215180048217)
    ·
      refine ⟨12142184191811411385036163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16189578922415215180048217 12142184191811411385036163)
      ·
        refine ⟨18213276287717117077554245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12142184191811411385036163 18213276287717117077554245)
        ·
          refine ⟨3414989303946959452041421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18213276287717117077554245 3414989303946959452041421)
          ·
            refine ⟨1280620988980109794515533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3414989303946959452041421 1280620988980109794515533)
            ·
              refine ⟨480232870867541172943325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1280620988980109794515533 480232870867541172943325)
              ·
                refine ⟨180087326575327939853747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480232870867541172943325 180087326575327939853747)
                ·
                  refine ⟨270130989862991909780621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180087326575327939853747 270130989862991909780621)
                  ·
                    refine ⟨101299121198621966167733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270130989862991909780621 101299121198621966167733)
                    ·
                      rfl

theorem cell22_295919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_295919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295919 prefixEnd_295919 := by exact prefixLift 295919
  have htrace : WordTrace (prefixWord ++ tailWord_295919) baseStart_295919 baseEnd_295919 := by
    simpa [prefixWord, tailWord_295919, baseEnd_295919] using wordTrace_append hprefix tailTrace_295919
  have hstable : (prefixWord ++ tailWord_295919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295919).length < 2 ^ (prefixWord ++ tailWord_295919).sum := by decide
  have hdescent : baseEnd_295919 < baseStart_295919 := by decide
  rcases family_descends (prefixWord ++ tailWord_295919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295994 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_295994 : Nat := 118140960795 + 295994 * 2 ^ 59
def prefixEnd_295994 : Nat := 4983230072969 + 3 ^ 40 * 295994 * 2
def baseEnd_295994 : Nat := 33774931743782256847501

theorem tailTrace_295994 : CollatzResearch.WordTrace tailWord_295994 prefixEnd_295994 33774931743782256847501 := by
  unfold tailWord_295994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698947022417941148919759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7197192059781176397119357 2698947022417941148919759)
  ·
    refine ⟨4048420533626911723379639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2698947022417941148919759 4048420533626911723379639)
    ·
      refine ⟨6072630800440367585069459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048420533626911723379639 6072630800440367585069459)
      ·
        refine ⟨9108946200660551377604189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072630800440367585069459 9108946200660551377604189)
        ·
          refine ⟨3415854825247706766601571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9108946200660551377604189 3415854825247706766601571)
          ·
            refine ⟨5123782237871560149902357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415854825247706766601571 5123782237871560149902357)
            ·
              refine ⟨240177292400229382026673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5123782237871560149902357 240177292400229382026673)
              ·
                refine ⟨180132969300172036520005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240177292400229382026673 180132969300172036520005)
                ·
                  refine ⟨33774931743782256847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180132969300172036520005 33774931743782256847501)
                  ·
                    rfl

theorem cell22_295994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_295994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_295994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_295994 prefixEnd_295994 := by exact prefixLift 295994
  have htrace : WordTrace (prefixWord ++ tailWord_295994) baseStart_295994 baseEnd_295994 := by
    simpa [prefixWord, tailWord_295994, baseEnd_295994] using wordTrace_append hprefix tailTrace_295994
  have hstable : (prefixWord ++ tailWord_295994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295994).length < 2 ^ (prefixWord ++ tailWord_295994).sum := by decide
  have hdescent : baseEnd_295994 < baseStart_295994 := by decide
  rcases family_descends (prefixWord ++ tailWord_295994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296005 : List Nat := [1, 3, 1, 1, 1, 3, 5, 7]
def baseStart_296005 : Nat := 118140960795 + 296005 * 2 ^ 59
def prefixEnd_296005 : Nat := 4983230072969 + 3 ^ 40 * 296005 * 2
def baseEnd_296005 : Nat := 11258728972905156501941

theorem tailTrace_296005 : CollatzResearch.WordTrace tailWord_296005 prefixEnd_296005 11258728972905156501941 := by
  unfold tailWord_296005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796189292631913474329469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7197459528421275649552979 10796189292631913474329469)
  ·
    refine ⟨4048570984736967552873551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10796189292631913474329469 4048570984736967552873551)
    ·
      refine ⟨6072856477105451329310327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048570984736967552873551 6072856477105451329310327)
      ·
        refine ⟨9109284715658176993965491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072856477105451329310327 9109284715658176993965491)
        ·
          refine ⟨13663927073487265490948237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109284715658176993965491 13663927073487265490948237)
          ·
            refine ⟨5123972652557724559105589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13663927073487265490948237 5123972652557724559105589)
            ·
              refine ⟨480372436177286677416149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5123972652557724559105589 480372436177286677416149)
              ·
                refine ⟨11258728972905156501941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 480372436177286677416149 11258728972905156501941)
                ·
                  rfl

theorem cell22_296005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 7].length) (baseStart_296005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296005 prefixEnd_296005 := by exact prefixLift 296005
  have htrace : WordTrace (prefixWord ++ tailWord_296005) baseStart_296005 baseEnd_296005 := by
    simpa [prefixWord, tailWord_296005, baseEnd_296005] using wordTrace_append hprefix tailTrace_296005
  have hstable : (prefixWord ++ tailWord_296005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296005).length < 2 ^ (prefixWord ++ tailWord_296005).sum := by decide
  have hdescent : baseEnd_296005 < baseStart_296005 := by decide
  rcases family_descends (prefixWord ++ tailWord_296005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296030 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_296030 : Nat := 118140960795 + 296030 * 2 ^ 59
def prefixEnd_296030 : Nat := 4983230072969 + 3 ^ 40 * 296030 * 2
def baseEnd_296030 : Nat := 101337118767054676642393

theorem tailTrace_296030 : CollatzResearch.WordTrace tailWord_296030 prefixEnd_296030 101337118767054676642393 := by
  unfold tailWord_296030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349637639692667842998693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7198067411694228495993029 1349637639692667842998693)
  ·
    refine ⟨253057057442375220562255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1349637639692667842998693 253057057442375220562255)
    ·
      refine ⟨379585586163562830843383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253057057442375220562255 379585586163562830843383)
      ·
        refine ⟨569378379245344246265075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379585586163562830843383 569378379245344246265075)
        ·
          refine ⟨854067568868016369397613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569378379245344246265075 854067568868016369397613)
          ·
            refine ⟨320275338325506138524105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 854067568868016369397613 320275338325506138524105)
            ·
              refine ⟨240206503744129603893079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320275338325506138524105 240206503744129603893079)
              ·
                refine ⟨360309755616194405839619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240206503744129603893079 360309755616194405839619)
                ·
                  refine ⟨540464633424291608759429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360309755616194405839619 540464633424291608759429)
                  ·
                    refine ⟨101337118767054676642393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540464633424291608759429 101337118767054676642393)
                    ·
                      rfl

theorem cell22_296030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_296030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296030 prefixEnd_296030 := by exact prefixLift 296030
  have htrace : WordTrace (prefixWord ++ tailWord_296030) baseStart_296030 baseEnd_296030 := by
    simpa [prefixWord, tailWord_296030, baseEnd_296030] using wordTrace_append hprefix tailTrace_296030
  have hstable : (prefixWord ++ tailWord_296030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296030).length < 2 ^ (prefixWord ++ tailWord_296030).sum := by decide
  have hdescent : baseEnd_296030 < baseStart_296030 := by decide
  rcases family_descends (prefixWord ++ tailWord_296030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296037 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_296037 : Nat := 118140960795 + 296037 * 2 ^ 59
def prefixEnd_296037 : Nat := 4983230072969 + 3 ^ 40 * 296037 * 2
def baseEnd_296037 : Nat := 101339515010108991717371

theorem tailTrace_296037 : CollatzResearch.WordTrace tailWord_296037 prefixEnd_296037 101339515010108991717371 := by
  unfold tailWord_296037
  simp only [CollatzResearch.WordTrace]
  refine ⟨10797356428515982939494365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7198237619010655292996243 10797356428515982939494365)
  ·
    refine ⟨4049008660693493602310387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10797356428515982939494365 4049008660693493602310387)
    ·
      refine ⟨6073512991040240403465581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049008660693493602310387 6073512991040240403465581)
      ·
        refine ⟨2277567371640090151299593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6073512991040240403465581 2277567371640090151299593)
        ·
          refine ⟨1708175528730067613474695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2277567371640090151299593 1708175528730067613474695)
          ·
            refine ⟨2562263293095101420212043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708175528730067613474695 2562263293095101420212043)
            ·
              refine ⟨3843394939642652130318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562263293095101420212043 3843394939642652130318065)
              ·
                refine ⟨2882546204731989097738549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3843394939642652130318065 2882546204731989097738549)
                ·
                  refine ⟨270238706693623977912989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882546204731989097738549 270238706693623977912989)
                  ·
                    refine ⟨101339515010108991717371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270238706693623977912989 101339515010108991717371)
                    ·
                      rfl

theorem cell22_296037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_296037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296037 prefixEnd_296037 := by exact prefixLift 296037
  have htrace : WordTrace (prefixWord ++ tailWord_296037) baseStart_296037 baseEnd_296037 := by
    simpa [prefixWord, tailWord_296037, baseEnd_296037] using wordTrace_append hprefix tailTrace_296037
  have hstable : (prefixWord ++ tailWord_296037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296037).length < 2 ^ (prefixWord ++ tailWord_296037).sum := by decide
  have hdescent : baseEnd_296037 < baseStart_296037 := by decide
  rcases family_descends (prefixWord ++ tailWord_296037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296088 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_296088 : Nat := 118140960795 + 296088 * 2 ^ 59
def prefixEnd_296088 : Nat := 4983230072969 + 3 ^ 40 * 296088 * 2
def baseEnd_296088 : Nat := 101356973352361858692215

theorem tailTrace_296088 : CollatzResearch.WordTrace tailWord_296088 prefixEnd_296088 101356973352361858692215 := by
  unfold tailWord_296088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399608275665609324800459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7199477700887479099733945 5399608275665609324800459)
  ·
    refine ⟨8099412413498413987200689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399608275665609324800459 8099412413498413987200689)
    ·
      refine ⟨6074559310123810490400517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8099412413498413987200689 6074559310123810490400517)
      ·
        refine ⟨1138979870648214466950097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6074559310123810490400517 1138979870648214466950097)
        ·
          refine ⟨854234902986160850212573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138979870648214466950097 854234902986160850212573)
          ·
            refine ⟨320338088619810318829715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 854234902986160850212573 320338088619810318829715)
            ·
              refine ⟨480507132929715478244573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320338088619810318829715 480507132929715478244573)
              ·
                refine ⟨180190174848643304341715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480507132929715478244573 180190174848643304341715)
                ·
                  refine ⟨270285262272964956512573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180190174848643304341715 270285262272964956512573)
                  ·
                    refine ⟨101356973352361858692215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270285262272964956512573 101356973352361858692215)
                    ·
                      rfl

theorem cell22_296088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_296088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296088 prefixEnd_296088 := by exact prefixLift 296088
  have htrace : WordTrace (prefixWord ++ tailWord_296088) baseStart_296088 baseEnd_296088 := by
    simpa [prefixWord, tailWord_296088, baseEnd_296088] using wordTrace_append hprefix tailTrace_296088
  have hstable : (prefixWord ++ tailWord_296088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296088).length < 2 ^ (prefixWord ++ tailWord_296088).sum := by decide
  have hdescent : baseEnd_296088 < baseStart_296088 := by decide
  rcases family_descends (prefixWord ++ tailWord_296088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296118 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_296118 : Nat := 118140960795 + 296118 * 2 ^ 59
def prefixEnd_296118 : Nat := 4983230072969 + 3 ^ 40 * 296118 * 2
def baseEnd_296118 : Nat := 33789080988483926814041

theorem tailTrace_296118 : CollatzResearch.WordTrace tailWord_296118 prefixEnd_296118 33789080988483926814041 := by
  unfold tailWord_296118
  simp only [CollatzResearch.WordTrace]
  refine ⟨675019421326408360824563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7200207160815022515462005 675019421326408360824563)
  ·
    refine ⟨1012529131989612541236845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675019421326408360824563 1012529131989612541236845)
    ·
      refine ⟨379698424496104702963817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1012529131989612541236845 379698424496104702963817)
      ·
        refine ⟨284773818372078527222863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379698424496104702963817 284773818372078527222863)
        ·
          refine ⟨427160727558117790834295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284773818372078527222863 427160727558117790834295)
          ·
            refine ⟨640741091337176686251443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427160727558117790834295 640741091337176686251443)
            ·
              refine ⟨961111637005765029377165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640741091337176686251443 961111637005765029377165)
              ·
                refine ⟨360416863877161886016437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961111637005765029377165 360416863877161886016437)
                ·
                  refine ⟨33789080988483926814041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360416863877161886016437 33789080988483926814041)
                  ·
                    rfl

theorem cell22_296118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_296118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296118 prefixEnd_296118 := by exact prefixLift 296118
  have htrace : WordTrace (prefixWord ++ tailWord_296118) baseStart_296118 baseEnd_296118 := by
    simpa [prefixWord, tailWord_296118, baseEnd_296118] using wordTrace_append hprefix tailTrace_296118
  have hstable : (prefixWord ++ tailWord_296118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296118).length < 2 ^ (prefixWord ++ tailWord_296118).sum := by decide
  have hdescent : baseEnd_296118 < baseStart_296118 := by decide
  rcases family_descends (prefixWord ++ tailWord_296118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296157 : List Nat := [1, 4, 3, 2, 12]
def baseStart_296157 : Nat := 118140960795 + 296157 * 2 ^ 59
def prefixEnd_296157 : Nat := 4983230072969 + 3 ^ 40 * 296157 * 2
def baseEnd_296157 : Nat := 417204088322916373321

theorem tailTrace_296157 : CollatzResearch.WordTrace tailWord_296157 prefixEnd_296157 417204088322916373321 := by
  unfold tailWord_296157
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801733188081243433862725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7201155458720828955908483 10801733188081243433862725)
  ·
    refine ⟨2025324972765233143849261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10801733188081243433862725 2025324972765233143849261)
    ·
      refine ⟨759496864786962428943473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2025324972765233143849261 759496864786962428943473)
      ·
        refine ⟨569622648590221821707605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 759496864786962428943473 569622648590221821707605)
        ·
          refine ⟨417204088322916373321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 569622648590221821707605 417204088322916373321)
          ·
            rfl

theorem cell22_296157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 12].length) (baseStart_296157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296157 prefixEnd_296157 := by exact prefixLift 296157
  have htrace : WordTrace (prefixWord ++ tailWord_296157) baseStart_296157 baseEnd_296157 := by
    simpa [prefixWord, tailWord_296157, baseEnd_296157] using wordTrace_append hprefix tailTrace_296157
  have hstable : (prefixWord ++ tailWord_296157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296157).length < 2 ^ (prefixWord ++ tailWord_296157).sum := by decide
  have hdescent : baseEnd_296157 < baseStart_296157 := by decide
  rcases family_descends (prefixWord ++ tailWord_296157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
