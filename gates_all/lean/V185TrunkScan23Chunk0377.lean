import V185TrunkScan23Chunk0376

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2228543 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_2228543 : Nat := 118140960795 + 2228543 * 2 ^ 59
def prefixEnd_2228543 : Nat := 4983230072969 + 3 ^ 40 * 2228543 * 2
def baseEnd_2228543 : Nat := 1144313718212779548963623

theorem tailTrace_2228543 : CollatzResearch.WordTrace tailWord_2228543 prefixEnd_2228543 1144313718212779548963623 := by
  unfold tailWord_2228543
  simp only [CollatzResearch.WordTrace]
  refine ⟨81281640765376790688010283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54187760510251193792006855 81281640765376790688010283)
  ·
    refine ⟨121922461148065186032015425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81281640765376790688010283 121922461148065186032015425)
    ·
      refine ⟨91441845861048889524011569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121922461148065186032015425 91441845861048889524011569)
      ·
        refine ⟨68581384395786667143008677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91441845861048889524011569 68581384395786667143008677)
        ·
          refine ⟨12859009574210000089314127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68581384395786667143008677 12859009574210000089314127)
          ·
            refine ⟨19288514361315000133971191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859009574210000089314127 19288514361315000133971191)
            ·
              refine ⟨28932771541972500200956787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19288514361315000133971191 28932771541972500200956787)
              ·
                refine ⟨43399157312958750301435181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28932771541972500200956787 43399157312958750301435181)
                ·
                  refine ⟨16274683992359531363038193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43399157312958750301435181 16274683992359531363038193)
                  ·
                    refine ⟨12206012994269648522278645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16274683992359531363038193 12206012994269648522278645)
                    ·
                      refine ⟨1144313718212779548963623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12206012994269648522278645 1144313718212779548963623)
                      ·
                        rfl

theorem cell23_2228543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_2228543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228543 prefixEnd_2228543 := by exact prefixLift 2228543
  have htrace : WordTrace (prefixWord ++ tailWord_2228543) baseStart_2228543 baseEnd_2228543 := by
    simpa [prefixWord, tailWord_2228543, baseEnd_2228543] using wordTrace_append hprefix tailTrace_2228543
  have hstable : (prefixWord ++ tailWord_2228543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228543).length < 2 ^ (prefixWord ++ tailWord_2228543).sum := by decide
  have hdescent : baseEnd_2228543 < baseStart_2228543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228548 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2228548 : Nat := 118140960795 + 2228548 * 2 ^ 59
def prefixEnd_2228548 : Nat := 4983230072969 + 3 ^ 40 * 2228548 * 2
def baseEnd_2228548 : Nat := 1144316285616052029401101

theorem tailTrace_2228548 : CollatzResearch.WordTrace tailWord_2228548 prefixEnd_2228548 1144316285616052029401101 := by
  unfold tailWord_2228548
  simp only [CollatzResearch.WordTrace]
  refine ⟨40640911565179338270971149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54187882086905784361294865 40640911565179338270971149)
  ·
    refine ⟨15240341836942251851614181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40640911565179338270971149 15240341836942251851614181)
    ·
      refine ⟨2857564094426672222177659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15240341836942251851614181 2857564094426672222177659)
      ·
        refine ⟨4286346141640008333266489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857564094426672222177659 4286346141640008333266489)
        ·
          refine ⟨3214759606230006249949867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286346141640008333266489 3214759606230006249949867)
          ·
            refine ⟨4822139409345009374924801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214759606230006249949867 4822139409345009374924801)
            ·
              refine ⟨3616604557008757031193601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822139409345009374924801 3616604557008757031193601)
              ·
                refine ⟨2712453417756567773395201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616604557008757031193601 2712453417756567773395201)
                ·
                  refine ⟨2034340063317425830046401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712453417756567773395201 2034340063317425830046401)
                  ·
                    refine ⟨1525755047488069372534801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2034340063317425830046401 1525755047488069372534801)
                    ·
                      refine ⟨1144316285616052029401101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525755047488069372534801 1144316285616052029401101)
                      ·
                        rfl

theorem cell23_2228548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2228548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228548 prefixEnd_2228548 := by exact prefixLift 2228548
  have htrace : WordTrace (prefixWord ++ tailWord_2228548) baseStart_2228548 baseEnd_2228548 := by
    simpa [prefixWord, tailWord_2228548, baseEnd_2228548] using wordTrace_append hprefix tailTrace_2228548
  have hstable : (prefixWord ++ tailWord_2228548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228548).length < 2 ^ (prefixWord ++ tailWord_2228548).sum := by decide
  have hdescent : baseEnd_2228548 < baseStart_2228548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228553 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_2228553 : Nat := 118140960795 + 2228553 * 2 ^ 59
def prefixEnd_2228553 : Nat := 4983230072969 + 3 ^ 40 * 2228553 * 2
def baseEnd_2228553 : Nat := 1144318853019324509838577

theorem tailTrace_2228553 : CollatzResearch.WordTrace tailWord_2228553 prefixEnd_2228553 1144318853019324509838577 := by
  unfold tailWord_2228553
  simp only [CollatzResearch.WordTrace]
  refine ⟨81282005495340562395874313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54188003663560374930582875 81282005495340562395874313)
  ·
    refine ⟨60961504121505421796905735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81282005495340562395874313 60961504121505421796905735)
    ·
      refine ⟨91442256182258132695358603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60961504121505421796905735 91442256182258132695358603)
      ·
        refine ⟨137163384273387199043037905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91442256182258132695358603 137163384273387199043037905)
        ·
          refine ⟨102872538205040399282278429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137163384273387199043037905 102872538205040399282278429)
          ·
            refine ⟨38577201826890149730854411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102872538205040399282278429 38577201826890149730854411)
            ·
              refine ⟨57865802740335224596281617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38577201826890149730854411 57865802740335224596281617)
              ·
                refine ⟨43399352055251418447211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57865802740335224596281617 43399352055251418447211213)
                ·
                  refine ⟨16274757020719281917704205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43399352055251418447211213 16274757020719281917704205)
                  ·
                    refine ⟨6103033882769730719139077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16274757020719281917704205 6103033882769730719139077)
                    ·
                      refine ⟨1144318853019324509838577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6103033882769730719139077 1144318853019324509838577)
                      ·
                        rfl

theorem cell23_2228553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_2228553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228553 prefixEnd_2228553 := by exact prefixLift 2228553
  have htrace : WordTrace (prefixWord ++ tailWord_2228553) baseStart_2228553 baseEnd_2228553 := by
    simpa [prefixWord, tailWord_2228553, baseEnd_2228553] using wordTrace_append hprefix tailTrace_2228553
  have hstable : (prefixWord ++ tailWord_2228553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228553).length < 2 ^ (prefixWord ++ tailWord_2228553).sum := by decide
  have hdescent : baseEnd_2228553 < baseStart_2228553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228593 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 8]
def baseStart_2228593 : Nat := 118140960795 + 2228593 * 2 ^ 59
def prefixEnd_2228593 : Nat := 4983230072969 + 3 ^ 40 * 2228593 * 2
def baseEnd_2228593 : Nat := 127148821360611594815377

theorem tailTrace_2228593 : CollatzResearch.WordTrace tailWord_2228593 prefixEnd_2228593 127148821360611594815377 := by
  unfold tailWord_2228593
  simp only [CollatzResearch.WordTrace]
  refine ⟨81283464415195649227330433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54188976276797099484886955 81283464415195649227330433)
  ·
    refine ⟨60962598311396736920497825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81283464415195649227330433 60962598311396736920497825)
    ·
      refine ⟨45721948733547552690373369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60962598311396736920497825 45721948733547552690373369)
      ·
        refine ⟨34291461550160664517780027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45721948733547552690373369 34291461550160664517780027)
        ·
          refine ⟨51437192325240996776670041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34291461550160664517780027 51437192325240996776670041)
          ·
            refine ⟨38577894243930747582502531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51437192325240996776670041 38577894243930747582502531)
            ·
              refine ⟨57866841365896121373753797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38577894243930747582502531 57866841365896121373753797)
              ·
                refine ⟨10850032756105522757578837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57866841365896121373753797 10850032756105522757578837)
                ·
                  refine ⟨127148821360611594815377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10850032756105522757578837 127148821360611594815377)
                  ·
                    rfl

theorem cell23_2228593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_2228593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228593 prefixEnd_2228593 := by exact prefixLift 2228593
  have htrace : WordTrace (prefixWord ++ tailWord_2228593) baseStart_2228593 baseEnd_2228593 := by
    simpa [prefixWord, tailWord_2228593, baseEnd_2228593] using wordTrace_append hprefix tailTrace_2228593
  have hstable : (prefixWord ++ tailWord_2228593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228593).length < 2 ^ (prefixWord ++ tailWord_2228593).sum := by decide
  have hdescent : baseEnd_2228593 < baseStart_2228593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228648 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2228648 : Nat := 118140960795 + 2228648 * 2 ^ 59
def prefixEnd_2228648 : Nat := 4983230072969 + 3 ^ 40 * 2228648 * 2
def baseEnd_2228648 : Nat := 381455877893833879383547

theorem tailTrace_2228648 : CollatzResearch.WordTrace tailWord_2228648 prefixEnd_2228648 381455877893833879383547 := by
  unfold tailWord_2228648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40642735214998196810291299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54190313619997595747055065 40642735214998196810291299)
  ·
    refine ⟨60964102822497295215436949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40642735214998196810291299 60964102822497295215436949)
    ·
      refine ⟨2857692319804560713223607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60964102822497295215436949 2857692319804560713223607)
      ·
        refine ⟨4286538479706841069835411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857692319804560713223607 4286538479706841069835411)
        ·
          refine ⟨6429807719560261604753117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286538479706841069835411 6429807719560261604753117)
          ·
            refine ⟨2411177894835098101782419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6429807719560261604753117 2411177894835098101782419)
            ·
              refine ⟨3616766842252647152673629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411177894835098101782419 3616766842252647152673629)
              ·
                refine ⟨1356287565844742682252611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616766842252647152673629 1356287565844742682252611)
                ·
                  refine ⟨2034431348767114023378917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356287565844742682252611 2034431348767114023378917)
                  ·
                    refine ⟨381455877893833879383547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034431348767114023378917 381455877893833879383547)
                    ·
                      rfl

theorem cell23_2228648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2228648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228648 prefixEnd_2228648 := by exact prefixLift 2228648
  have htrace : WordTrace (prefixWord ++ tailWord_2228648) baseStart_2228648 baseEnd_2228648 := by
    simpa [prefixWord, tailWord_2228648, baseEnd_2228648] using wordTrace_append hprefix tailTrace_2228648
  have hstable : (prefixWord ++ tailWord_2228648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228648).length < 2 ^ (prefixWord ++ tailWord_2228648).sum := by decide
  have hdescent : baseEnd_2228648 < baseStart_2228648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228657 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_2228657 : Nat := 118140960795 + 2228657 * 2 ^ 59
def prefixEnd_2228657 : Nat := 4983230072969 + 3 ^ 40 * 2228657 * 2
def baseEnd_2228657 : Nat := 381457418335797367646033

theorem tailTrace_2228657 : CollatzResearch.WordTrace tailWord_2228657 prefixEnd_2228657 381457418335797367646033 := by
  unfold tailWord_2228657
  simp only [CollatzResearch.WordTrace]
  refine ⟨81285798686963788157660225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54190532457975858771773483 81285798686963788157660225)
  ·
    refine ⟨60964349015222841118245169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81285798686963788157660225 60964349015222841118245169)
    ·
      refine ⟨45723261761417130838683877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60964349015222841118245169 45723261761417130838683877)
      ·
        refine ⟨8573111580265712032253227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45723261761417130838683877 8573111580265712032253227)
        ·
          refine ⟨12859667370398568048379841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573111580265712032253227 12859667370398568048379841)
          ·
            refine ⟨9644750527798926036284881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12859667370398568048379841 9644750527798926036284881)
            ·
              refine ⟨7233562895849194527213661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9644750527798926036284881 7233562895849194527213661)
              ·
                refine ⟨2712586085943447947705123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7233562895849194527213661 2712586085943447947705123)
                ·
                  refine ⟨4068879128915171921557685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712586085943447947705123 4068879128915171921557685)
                  ·
                    refine ⟨381457418335797367646033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4068879128915171921557685 381457418335797367646033)
                    ·
                      rfl

theorem cell23_2228657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_2228657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228657 prefixEnd_2228657 := by exact prefixLift 2228657
  have htrace : WordTrace (prefixWord ++ tailWord_2228657) baseStart_2228657 baseEnd_2228657 := by
    simpa [prefixWord, tailWord_2228657, baseEnd_2228657] using wordTrace_append hprefix tailTrace_2228657
  have hstable : (prefixWord ++ tailWord_2228657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228657).length < 2 ^ (prefixWord ++ tailWord_2228657).sum := by decide
  have hdescent : baseEnd_2228657 < baseStart_2228657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228694 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2228694 : Nat := 118140960795 + 2228694 * 2 ^ 59
def prefixEnd_2228694 : Nat := 4983230072969 + 3 ^ 40 * 2228694 * 2
def baseEnd_2228694 : Nat := 1144391253791608458175429

theorem tailTrace_2228694 : CollatzResearch.WordTrace tailWord_2228694 prefixEnd_2228694 1144391253791608458175429 := by
  unfold tailWord_2228694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080446761739358967297321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54191432125219828984504757 5080446761739358967297321)
  ·
    refine ⟨3810335071304519225472991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5080446761739358967297321 3810335071304519225472991)
    ·
      refine ⟨5715502606956778838209487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810335071304519225472991 5715502606956778838209487)
      ·
        refine ⟨8573253910435168257314231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715502606956778838209487 8573253910435168257314231)
        ·
          refine ⟨12859880865652752385971347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573253910435168257314231 12859880865652752385971347)
          ·
            refine ⟨19289821298479128578957021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859880865652752385971347 19289821298479128578957021)
            ·
              refine ⟨7233682986929673217108883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19289821298479128578957021 7233682986929673217108883)
              ·
                refine ⟨10850524480394509825663325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233682986929673217108883 10850524480394509825663325)
                ·
                  refine ⟨4068946680147941184623747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10850524480394509825663325 4068946680147941184623747)
                  ·
                    refine ⟨6103420020221911776935621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4068946680147941184623747 6103420020221911776935621)
                    ·
                      refine ⟨1144391253791608458175429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6103420020221911776935621 1144391253791608458175429)
                      ·
                        rfl

theorem cell23_2228694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2228694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228694 prefixEnd_2228694 := by exact prefixLift 2228694
  have htrace : WordTrace (prefixWord ++ tailWord_2228694) baseStart_2228694 baseEnd_2228694 := by
    simpa [prefixWord, tailWord_2228694, baseEnd_2228694] using wordTrace_append hprefix tailTrace_2228694
  have hstable : (prefixWord ++ tailWord_2228694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228694).length < 2 ^ (prefixWord ++ tailWord_2228694).sum := by decide
  have hdescent : baseEnd_2228694 < baseStart_2228694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228697 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_2228697 : Nat := 118140960795 + 2228697 * 2 ^ 59
def prefixEnd_2228697 : Nat := 4983230072969 + 3 ^ 40 * 2228697 * 2
def baseEnd_2228697 : Nat := 1144392794233571946437915

theorem tailTrace_2228697 : CollatzResearch.WordTrace tailWord_2228697 prefixEnd_2228697 1144392794233571946437915 := by
  unfold tailWord_2228697
  simp only [CollatzResearch.WordTrace]
  refine ⟨81287257606818874989116345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54191505071212583326077563 81287257606818874989116345)
  ·
    refine ⟨60965443205114156241837259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81287257606818874989116345 60965443205114156241837259)
    ·
      refine ⟨91448164807671234362755889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60965443205114156241837259 91448164807671234362755889)
      ·
        refine ⟨68586123605753425772066917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91448164807671234362755889 68586123605753425772066917)
        ·
          refine ⟨12859898176078767332262547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68586123605753425772066917 12859898176078767332262547)
          ·
            refine ⟨19289847264118150998393821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859898176078767332262547 19289847264118150998393821)
            ·
              refine ⟨7233692724044306624397683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19289847264118150998393821 7233692724044306624397683)
              ·
                refine ⟨10850539086066459936596525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233692724044306624397683 10850539086066459936596525)
                ·
                  refine ⟨4068952157274922476223697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10850539086066459936596525 4068952157274922476223697)
                  ·
                    refine ⟨3051714117956191857167773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4068952157274922476223697 3051714117956191857167773)
                    ·
                      refine ⟨1144392794233571946437915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051714117956191857167773 1144392794233571946437915)
                      ·
                        rfl

theorem cell23_2228697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_2228697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228697 prefixEnd_2228697 := by exact prefixLift 2228697
  have htrace : WordTrace (prefixWord ++ tailWord_2228697) baseStart_2228697 baseEnd_2228697 := by
    simpa [prefixWord, tailWord_2228697, baseEnd_2228697] using wordTrace_append hprefix tailTrace_2228697
  have hstable : (prefixWord ++ tailWord_2228697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228697).length < 2 ^ (prefixWord ++ tailWord_2228697).sum := by decide
  have hdescent : baseEnd_2228697 < baseStart_2228697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228714 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2228714 : Nat := 118140960795 + 2228714 * 2 ^ 59
def prefixEnd_2228714 : Nat := 4983230072969 + 3 ^ 40 * 2228714 * 2
def baseEnd_2228714 : Nat := 1144401523404698379925337

theorem tailTrace_2228714 : CollatzResearch.WordTrace tailWord_2228714 prefixEnd_2228714 1144401523404698379925337 := by
  unfold tailWord_2228714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20321969411939321723121299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54191918431838191261656797 20321969411939321723121299)
  ·
    refine ⟨30482954117908982584681949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20321969411939321723121299 30482954117908982584681949)
    ·
      refine ⟨11431107794215868469255731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30482954117908982584681949 11431107794215868469255731)
      ·
        refine ⟨17146661691323802703883597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11431107794215868469255731 17146661691323802703883597)
        ·
          refine ⟨6429998134246426013956349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17146661691323802703883597 6429998134246426013956349)
          ·
            refine ⟨2411249300342409755233631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6429998134246426013956349 2411249300342409755233631)
            ·
              refine ⟨3616873950513614632850447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411249300342409755233631 3616873950513614632850447)
              ·
                refine ⟨5425310925770421949275671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616873950513614632850447 5425310925770421949275671)
                ·
                  refine ⟨8137966388655632923913507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425310925770421949275671 8137966388655632923913507)
                  ·
                    refine ⟨12206949582983449385870261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8137966388655632923913507 12206949582983449385870261)
                    ·
                      refine ⟨1144401523404698379925337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12206949582983449385870261 1144401523404698379925337)
                      ·
                        rfl

theorem cell23_2228714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2228714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228714 prefixEnd_2228714 := by exact prefixLift 2228714
  have htrace : WordTrace (prefixWord ++ tailWord_2228714) baseStart_2228714 baseEnd_2228714 := by
    simpa [prefixWord, tailWord_2228714, baseEnd_2228714] using wordTrace_append hprefix tailTrace_2228714
  have hstable : (prefixWord ++ tailWord_2228714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228714).length < 2 ^ (prefixWord ++ tailWord_2228714).sum := by decide
  have hdescent : baseEnd_2228714 < baseStart_2228714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228722 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2228722 : Nat := 118140960795 + 2228722 * 2 ^ 59
def prefixEnd_2228722 : Nat := 4983230072969 + 3 ^ 40 * 2228722 * 2
def baseEnd_2228722 : Nat := 1144405631249934348625301

theorem tailTrace_2228722 : CollatzResearch.WordTrace tailWord_2228722 prefixEnd_2228722 1144405631249934348625301 := by
  unfold tailWord_2228722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322042357932076064694105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54192112954485536172517613 20322042357932076064694105)
  ·
    refine ⟨15241531768449057048520579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20322042357932076064694105 15241531768449057048520579)
    ·
      refine ⟨22862297652673585572780869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15241531768449057048520579 22862297652673585572780869)
      ·
        refine ⟨4286680809876297294896413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22862297652673585572780869 4286680809876297294896413)
        ·
          refine ⟨1607505303703611485586155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4286680809876297294896413 1607505303703611485586155)
          ·
            refine ⟨2411257955555417228379233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607505303703611485586155 2411257955555417228379233)
            ·
              refine ⟨1808443466666562921284425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411257955555417228379233 1808443466666562921284425)
              ·
                refine ⟨1356332599999922190963319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808443466666562921284425 1356332599999922190963319)
                ·
                  refine ⟨2034498899999883286444979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356332599999922190963319 2034498899999883286444979)
                  ·
                    refine ⟨3051748349999824929667469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034498899999883286444979 3051748349999824929667469)
                    ·
                      refine ⟨1144405631249934348625301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051748349999824929667469 1144405631249934348625301)
                      ·
                        rfl

theorem cell23_2228722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2228722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228722 prefixEnd_2228722 := by exact prefixLift 2228722
  have htrace : WordTrace (prefixWord ++ tailWord_2228722) baseStart_2228722 baseEnd_2228722 := by
    simpa [prefixWord, tailWord_2228722, baseEnd_2228722] using wordTrace_append hprefix tailTrace_2228722
  have hstable : (prefixWord ++ tailWord_2228722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228722).length < 2 ^ (prefixWord ++ tailWord_2228722).sum := by decide
  have hdescent : baseEnd_2228722 < baseStart_2228722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228727 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_2228727 : Nat := 118140960795 + 2228727 * 2 ^ 59
def prefixEnd_2228727 : Nat := 4983230072969 + 3 ^ 40 * 2228727 * 2
def baseEnd_2228727 : Nat := 1144408198653206829062777

theorem tailTrace_2228727 : CollatzResearch.WordTrace tailWord_2228727 prefixEnd_2228727 1144408198653206829062777 := by
  unfold tailWord_2228727
  simp only [CollatzResearch.WordTrace]
  refine ⟨81288351796710190112708435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54192234531140126741805623 81288351796710190112708435)
  ·
    refine ⟨121932527695065285169062653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81288351796710190112708435 121932527695065285169062653)
    ·
      refine ⟨45724697885649481938398495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121932527695065285169062653 45724697885649481938398495)
      ·
        refine ⟨68587046828474222907597743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45724697885649481938398495 68587046828474222907597743)
        ·
          refine ⟨102880570242711334361396615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68587046828474222907597743 102880570242711334361396615)
          ·
            refine ⟨154320855364067001542094923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102880570242711334361396615 154320855364067001542094923)
            ·
              refine ⟨231481283046100502313142385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154320855364067001542094923 231481283046100502313142385)
              ·
                refine ⟨173610962284575376734856789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231481283046100502313142385 173610962284575376734856789)
                ·
                  refine ⟨2034503464272367696111603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 173610962284575376734856789 2034503464272367696111603)
                  ·
                    refine ⟨3051755196408551544167405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034503464272367696111603 3051755196408551544167405)
                    ·
                      refine ⟨1144408198653206829062777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051755196408551544167405 1144408198653206829062777)
                      ·
                        rfl

theorem cell23_2228727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_2228727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228727 prefixEnd_2228727 := by exact prefixLift 2228727
  have htrace : WordTrace (prefixWord ++ tailWord_2228727) baseStart_2228727 baseEnd_2228727 := by
    simpa [prefixWord, tailWord_2228727, baseEnd_2228727] using wordTrace_append hprefix tailTrace_2228727
  have hstable : (prefixWord ++ tailWord_2228727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228727).length < 2 ^ (prefixWord ++ tailWord_2228727).sum := by decide
  have hdescent : baseEnd_2228727 < baseStart_2228727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228771 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 1, 3, 2]
def baseStart_2228771 : Nat := 118140960795 + 2228771 * 2 ^ 59
def prefixEnd_2228771 : Nat := 4983230072969 + 3 ^ 40 * 2228771 * 2
def baseEnd_2228771 : Nat := 1144430791802004656912575

theorem tailTrace_2228771 : CollatzResearch.WordTrace tailWord_2228771 prefixEnd_2228771 1144430791802004656912575 := by
  unfold tailWord_2228771
  simp only [CollatzResearch.WordTrace]
  refine ⟨81289956608550785627310167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54193304405700523751540111 81289956608550785627310167)
  ·
    refine ⟨121934934912826178440965251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81289956608550785627310167 121934934912826178440965251)
    ·
      refine ⟨182902402369239267661447877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121934934912826178440965251 182902402369239267661447877)
      ·
        refine ⟨34294200444232362686521477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182902402369239267661447877 34294200444232362686521477)
        ·
          refine ⟨6430162583293568003722777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34294200444232362686521477 6430162583293568003722777)
          ·
            refine ⟨4822621937470176002792083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6430162583293568003722777 4822621937470176002792083)
            ·
              refine ⟨7233932906205264004188125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822621937470176002792083 7233932906205264004188125)
              ·
                refine ⟨2712724839826974001570547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7233932906205264004188125 2712724839826974001570547)
                ·
                  refine ⟨4069087259740461002355821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712724839826974001570547 4069087259740461002355821)
                  ·
                    refine ⟨1525907722402672875883433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4069087259740461002355821 1525907722402672875883433)
                    ·
                      refine ⟨1144430791802004656912575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525907722402672875883433 1144430791802004656912575)
                      ·
                        rfl

theorem cell23_2228771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_2228771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228771 prefixEnd_2228771 := by exact prefixLift 2228771
  have htrace : WordTrace (prefixWord ++ tailWord_2228771) baseStart_2228771 baseEnd_2228771 := by
    simpa [prefixWord, tailWord_2228771, baseEnd_2228771] using wordTrace_append hprefix tailTrace_2228771
  have hstable : (prefixWord ++ tailWord_2228771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228771).length < 2 ^ (prefixWord ++ tailWord_2228771).sum := by decide
  have hdescent : baseEnd_2228771 < baseStart_2228771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228778 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2228778 : Nat := 118140960795 + 2228778 * 2 ^ 59
def prefixEnd_2228778 : Nat := 4983230072969 + 3 ^ 40 * 2228778 * 2
def baseEnd_2228778 : Nat := 1144434386166586129525043

theorem tailTrace_2228778 : CollatzResearch.WordTrace tailWord_2228778 prefixEnd_2228778 1144434386166586129525043 := by
  unfold tailWord_2228778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322552979881356455703747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54193474613016950548543325 20322552979881356455703747)
  ·
    refine ⟨30483829469822034683555621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20322552979881356455703747 30483829469822034683555621)
    ·
      refine ⟨5715718025591631503166679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30483829469822034683555621 5715718025591631503166679)
      ·
        refine ⟨8573577038387447254750019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715718025591631503166679 8573577038387447254750019)
        ·
          refine ⟨12860365557581170882125029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573577038387447254750019 12860365557581170882125029)
          ·
            refine ⟨2411318542046469540398443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12860365557581170882125029 2411318542046469540398443)
            ·
              refine ⟨3616977813069704310597665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411318542046469540398443 3616977813069704310597665)
              ·
                refine ⟨2712733359802278232948249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616977813069704310597665 2712733359802278232948249)
                ·
                  refine ⟨2034550019851708674711187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712733359802278232948249 2034550019851708674711187)
                  ·
                    refine ⟨3051825029777563012066781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034550019851708674711187 3051825029777563012066781)
                    ·
                      refine ⟨1144434386166586129525043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051825029777563012066781 1144434386166586129525043)
                      ·
                        rfl

theorem cell23_2228778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2228778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228778 prefixEnd_2228778 := by exact prefixLift 2228778
  have htrace : WordTrace (prefixWord ++ tailWord_2228778) baseStart_2228778 baseEnd_2228778 := by
    simpa [prefixWord, tailWord_2228778, baseEnd_2228778] using wordTrace_append hprefix tailTrace_2228778
  have hstable : (prefixWord ++ tailWord_2228778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228778).length < 2 ^ (prefixWord ++ tailWord_2228778).sum := by decide
  have hdescent : baseEnd_2228778 < baseStart_2228778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228801 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2228801 : Nat := 118140960795 + 2228801 * 2 ^ 59
def prefixEnd_2228801 : Nat := 4983230072969 + 3 ^ 40 * 2228801 * 2
def baseEnd_2228801 : Nat := 1144446196221639539537437

theorem tailTrace_2228801 : CollatzResearch.WordTrace tailWord_2228801 prefixEnd_2228801 1144446196221639539537437 := by
  unfold tailWord_2228801
  simp only [CollatzResearch.WordTrace]
  refine ⟨81291050798442100750902257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54194033865628067167268171 81291050798442100750902257)
  ·
    refine ⟨60968288098831575563176693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81291050798442100750902257 60968288098831575563176693)
    ·
      refine ⟨5715777009265460209047815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60968288098831575563176693 5715777009265460209047815)
      ·
        refine ⟨8573665513898190313571723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715777009265460209047815 8573665513898190313571723)
        ·
          refine ⟨12860498270847285470357585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573665513898190313571723 12860498270847285470357585)
          ·
            refine ⟨9645373703135464102768189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12860498270847285470357585 9645373703135464102768189)
            ·
              refine ⟨3617015138675799038538071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9645373703135464102768189 3617015138675799038538071)
              ·
                refine ⟨5425522708013698557807107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617015138675799038538071 5425522708013698557807107)
                ·
                  refine ⟨8138284062020547836710661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5425522708013698557807107 8138284062020547836710661)
                  ·
                    refine ⟨1525928261628852719383249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8138284062020547836710661 1525928261628852719383249)
                    ·
                      refine ⟨1144446196221639539537437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525928261628852719383249 1144446196221639539537437)
                      ·
                        rfl

theorem cell23_2228801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2228801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228801 prefixEnd_2228801 := by exact prefixLift 2228801
  have htrace : WordTrace (prefixWord ++ tailWord_2228801) baseStart_2228801 baseEnd_2228801 := by
    simpa [prefixWord, tailWord_2228801, baseEnd_2228801] using wordTrace_append hprefix tailTrace_2228801
  have hstable : (prefixWord ++ tailWord_2228801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228801).length < 2 ^ (prefixWord ++ tailWord_2228801).sum := by decide
  have hdescent : baseEnd_2228801 < baseStart_2228801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228807 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 7]
def baseStart_2228807 : Nat := 118140960795 + 2228807 * 2 ^ 59
def prefixEnd_2228807 : Nat := 4983230072969 + 3 ^ 40 * 2228807 * 2
def baseEnd_2228807 : Nat := 127161030789507390673601

theorem tailTrace_2228807 : CollatzResearch.WordTrace tailWord_2228807 prefixEnd_2228807 127161030789507390673601 := by
  unfold tailWord_2228807
  simp only [CollatzResearch.WordTrace]
  refine ⟨81291269636420363775620675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54194179757613575850413783 81291269636420363775620675)
  ·
    refine ⟨121936904454630545663431013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81291269636420363775620675 121936904454630545663431013)
    ·
      refine ⟨22863169585243227311893315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121936904454630545663431013 22863169585243227311893315)
      ·
        refine ⟨34294754377864840967839973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22863169585243227311893315 34294754377864840967839973)
        ·
          refine ⟨6430266445849657681469995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34294754377864840967839973 6430266445849657681469995)
          ·
            refine ⟨9645399668774486522204993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6430266445849657681469995 9645399668774486522204993)
            ·
              refine ⟨7234049751580864891653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9645399668774486522204993 7234049751580864891653745)
              ·
                refine ⟨5425537313685648668740309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234049751580864891653745 5425537313685648668740309)
                ·
                  refine ⟨127161030789507390673601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5425537313685648668740309 127161030789507390673601)
                  ·
                    rfl

theorem cell23_2228807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 7].length) (baseStart_2228807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228807 prefixEnd_2228807 := by exact prefixLift 2228807
  have htrace : WordTrace (prefixWord ++ tailWord_2228807) baseStart_2228807 baseEnd_2228807 := by
    simpa [prefixWord, tailWord_2228807, baseEnd_2228807] using wordTrace_append hprefix tailTrace_2228807
  have hstable : (prefixWord ++ tailWord_2228807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228807).length < 2 ^ (prefixWord ++ tailWord_2228807).sum := by decide
  have hdescent : baseEnd_2228807 < baseStart_2228807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228824 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 5]
def baseStart_2228824 : Nat := 118140960795 + 2228824 * 2 ^ 59
def prefixEnd_2228824 : Nat := 4983230072969 + 3 ^ 40 * 2228824 * 2
def baseEnd_2228824 : Nat := 127162000697410327727759

theorem tailTrace_2228824 : CollatzResearch.WordTrace tailWord_2228824 prefixEnd_2228824 127162000697410327727759 := by
  unfold tailWord_2228824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40645944838679387839494763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54194593118239183785993017 40645944838679387839494763)
  ·
    refine ⟨60968917258019081759242145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40645944838679387839494763 60968917258019081759242145)
    ·
      refine ⟨45726687943514311319431609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60968917258019081759242145 45726687943514311319431609)
      ·
        refine ⟨34295015957635733489573707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45726687943514311319431609 34295015957635733489573707)
        ·
          refine ⟨51442523936453600234360561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34295015957635733489573707 51442523936453600234360561)
          ·
            refine ⟨38581892952340200175770421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51442523936453600234360561 38581892952340200175770421)
            ·
              refine ⟨3617052464281893766478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38581892952340200175770421 3617052464281893766478477)
              ·
                refine ⟨1356394674105710162429429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3617052464281893766478477 1356394674105710162429429)
                ·
                  refine ⟨127162000697410327727759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356394674105710162429429 127162000697410327727759)
                  ·
                    rfl

theorem cell23_2228824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 5].length) (baseStart_2228824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228824 prefixEnd_2228824 := by exact prefixLift 2228824
  have htrace : WordTrace (prefixWord ++ tailWord_2228824) baseStart_2228824 baseEnd_2228824 := by
    simpa [prefixWord, tailWord_2228824, baseEnd_2228824] using wordTrace_append hprefix tailTrace_2228824
  have hstable : (prefixWord ++ tailWord_2228824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228824).length < 2 ^ (prefixWord ++ tailWord_2228824).sum := by decide
  have hdescent : baseEnd_2228824 < baseStart_2228824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228887 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2228887 : Nat := 118140960795 + 2228887 * 2 ^ 59
def prefixEnd_2228887 : Nat := 4983230072969 + 3 ^ 40 * 2228887 * 2
def baseEnd_2228887 : Nat := 1144490355557926203062041

theorem tailTrace_2228887 : CollatzResearch.WordTrace tailWord_2228887 prefixEnd_2228887 1144490355557926203062041 := by
  unfold tailWord_2228887
  simp only [CollatzResearch.WordTrace]
  refine ⟨81294187476130537438532915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54196124984087024959021943 81294187476130537438532915)
  ·
    refine ⟨121941281214195806157799373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81294187476130537438532915 121941281214195806157799373)
    ·
      refine ⟨45727980455323427309174765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121941281214195806157799373 45727980455323427309174765)
      ·
        refine ⟨17147992670746285240940537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45727980455323427309174765 17147992670746285240940537)
        ·
          refine ⟨12860994503059713930705403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17147992670746285240940537 12860994503059713930705403)
          ·
            refine ⟨19291491754589570896058105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12860994503059713930705403 19291491754589570896058105)
            ·
              refine ⟨14468618815942178172043579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19291491754589570896058105 14468618815942178172043579)
              ·
                refine ⟨21702928223913267258065369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14468618815942178172043579 21702928223913267258065369)
                ·
                  refine ⟨16277196167934950443549027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21702928223913267258065369 16277196167934950443549027)
                  ·
                    refine ⟨24415794251902425665323541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16277196167934950443549027 24415794251902425665323541)
                    ·
                      refine ⟨1144490355557926203062041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24415794251902425665323541 1144490355557926203062041)
                      ·
                        rfl

theorem cell23_2228887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2228887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228887 prefixEnd_2228887 := by exact prefixLift 2228887
  have htrace : WordTrace (prefixWord ++ tailWord_2228887) baseStart_2228887 baseEnd_2228887 := by
    simpa [prefixWord, tailWord_2228887, baseEnd_2228887] using wordTrace_append hprefix tailTrace_2228887
  have hstable : (prefixWord ++ tailWord_2228887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228887).length < 2 ^ (prefixWord ++ tailWord_2228887).sum := by decide
  have hdescent : baseEnd_2228887 < baseStart_2228887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228894 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2228894 : Nat := 118140960795 + 2228894 * 2 ^ 59
def prefixEnd_2228894 : Nat := 4983230072969 + 3 ^ 40 * 2228894 * 2
def baseEnd_2228894 : Nat := 1144493949922507675674509

theorem tailTrace_2228894 : CollatzResearch.WordTrace tailWord_2228894 prefixEnd_2228894 1144493949922507675674509 := by
  unfold tailWord_2228894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10161805348388147204254717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54196295191403451756025157 10161805348388147204254717)
  ·
    refine ⟨3810677005645555201595519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10161805348388147204254717 3810677005645555201595519)
    ·
      refine ⟨5716015508468332802393279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810677005645555201595519 5716015508468332802393279)
      ·
        refine ⟨8574023262702499203589919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716015508468332802393279 8574023262702499203589919)
        ·
          refine ⟨12861034894053748805384879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8574023262702499203589919 12861034894053748805384879)
          ·
            refine ⟨19291552341080623208077319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12861034894053748805384879 19291552341080623208077319)
            ·
              refine ⟨28937328511620934812115979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19291552341080623208077319 28937328511620934812115979)
              ·
                refine ⟨43405992767431402218173969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28937328511620934812115979 43405992767431402218173969)
                ·
                  refine ⟨32554494575573551663630477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43405992767431402218173969 32554494575573551663630477)
                  ·
                    refine ⟨12207935465840081873861429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32554494575573551663630477 12207935465840081873861429)
                    ·
                      refine ⟨1144493949922507675674509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12207935465840081873861429 1144493949922507675674509)
                      ·
                        rfl

theorem cell23_2228894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2228894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228894 prefixEnd_2228894 := by exact prefixLift 2228894
  have htrace : WordTrace (prefixWord ++ tailWord_2228894) baseStart_2228894 baseEnd_2228894 := by
    simpa [prefixWord, tailWord_2228894, baseEnd_2228894] using wordTrace_append hprefix tailTrace_2228894
  have hstable : (prefixWord ++ tailWord_2228894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228894).length < 2 ^ (prefixWord ++ tailWord_2228894).sum := by decide
  have hdescent : baseEnd_2228894 < baseStart_2228894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228948 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2228948 : Nat := 118140960795 + 2228948 * 2 ^ 59
def prefixEnd_2228948 : Nat := 4983230072969 + 3 ^ 40 * 2228948 * 2
def baseEnd_2228948 : Nat := 127169075319761162711029

theorem tailTrace_2228948 : CollatzResearch.WordTrace tailWord_2228948 prefixEnd_2228948 127169075319761162711029 := by
  unfold tailWord_2228948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40648206164454772428251749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54197608219273029904335665 40648206164454772428251749)
  ·
    refine ⟨7621538655835269830297203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40648206164454772428251749 7621538655835269830297203)
    ·
      refine ⟨11432307983752904745445805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7621538655835269830297203 11432307983752904745445805)
      ·
        refine ⟨4287115493907339279542177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11432307983752904745445805 4287115493907339279542177)
        ·
          refine ⟨3215336620430504459656633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287115493907339279542177 3215336620430504459656633)
          ·
            refine ⟨2411502465322878344742475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215336620430504459656633 2411502465322878344742475)
            ·
              refine ⟨3617253697984317517113713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411502465322878344742475 3617253697984317517113713)
              ·
                refine ⟨2712940273488238137835285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617253697984317517113713 2712940273488238137835285)
                ·
                  refine ⟨127169075319761162711029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2712940273488238137835285 127169075319761162711029)
                  ·
                    rfl

theorem cell23_2228948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2228948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228948 prefixEnd_2228948 := by exact prefixLift 2228948
  have htrace : WordTrace (prefixWord ++ tailWord_2228948) baseStart_2228948 baseEnd_2228948 := by
    simpa [prefixWord, tailWord_2228948, baseEnd_2228948] using wordTrace_append hprefix tailTrace_2228948
  have hstable : (prefixWord ++ tailWord_2228948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228948).length < 2 ^ (prefixWord ++ tailWord_2228948).sum := by decide
  have hdescent : baseEnd_2228948 < baseStart_2228948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229001 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_2229001 : Nat := 118140960795 + 2229001 * 2 ^ 59
def prefixEnd_2229001 : Nat := 4983230072969 + 3 ^ 40 * 2229001 * 2
def baseEnd_2229001 : Nat := 1144548892352538757036517

theorem tailTrace_2229001 : CollatzResearch.WordTrace tailWord_2229001 prefixEnd_2229001 1144548892352538757036517 := by
  unfold tailWord_2229001
  simp only [CollatzResearch.WordTrace]
  refine ⟨81298345397717534908182857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54198896931811689938788571 81298345397717534908182857)
  ·
    refine ⟨60973759048288151181137143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81298345397717534908182857 60973759048288151181137143)
    ·
      refine ⟨91460638572432226771705715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60973759048288151181137143 91460638572432226771705715)
      ·
        refine ⟨137190957858648340157558573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91460638572432226771705715 137190957858648340157558573)
        ·
          refine ⟨51446609196993127559084465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137190957858648340157558573 51446609196993127559084465)
          ·
            refine ⟨38584956897744845669313349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51446609196993127559084465 38584956897744845669313349)
            ·
              refine ⟨7234679418327158562996253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38584956897744845669313349 7234679418327158562996253)
              ·
                refine ⟨2713004781872684461123595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7234679418327158562996253 2713004781872684461123595)
                ·
                  refine ⟨4069507172809026691685393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713004781872684461123595 4069507172809026691685393)
                  ·
                    refine ⟨3052130379606770018764045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069507172809026691685393 3052130379606770018764045)
                    ·
                      refine ⟨1144548892352538757036517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052130379606770018764045 1144548892352538757036517)
                      ·
                        rfl

theorem cell23_2229001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_2229001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229001 prefixEnd_2229001 := by exact prefixLift 2229001
  have htrace : WordTrace (prefixWord ++ tailWord_2229001) baseStart_2229001 baseEnd_2229001 := by
    simpa [prefixWord, tailWord_2229001, baseEnd_2229001] using wordTrace_append hprefix tailTrace_2229001
  have hstable : (prefixWord ++ tailWord_2229001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229001).length < 2 ^ (prefixWord ++ tailWord_2229001).sum := by decide
  have hdescent : baseEnd_2229001 < baseStart_2229001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229064 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2229064 : Nat := 118140960795 + 2229064 * 2 ^ 59
def prefixEnd_2229064 : Nat := 4983230072969 + 3 ^ 40 * 2229064 * 2
def baseEnd_2229064 : Nat := 381527080544590670182909

theorem tailTrace_2229064 : CollatzResearch.WordTrace tailWord_2229064 prefixEnd_2229064 381527080544590670182909 := by
  unfold tailWord_2229064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40650321598244648333863123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54200428797659531111817497 40650321598244648333863123)
  ·
    refine ⟨60975482397366972500794685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40650321598244648333863123 60975482397366972500794685)
    ·
      refine ⟨22865805899012614687798007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60975482397366972500794685 22865805899012614687798007)
      ·
        refine ⟨34298708848518922031697011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22865805899012614687798007 34298708848518922031697011)
        ·
          refine ⟨51448063272778383047545517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34298708848518922031697011 51448063272778383047545517)
          ·
            refine ⟨19293023727291893642829569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51448063272778383047545517 19293023727291893642829569)
            ·
              refine ⟨14469767795468920232122177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19293023727291893642829569 14469767795468920232122177)
              ·
                refine ⟨10852325846601690174091633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14469767795468920232122177 10852325846601690174091633)
                ·
                  refine ⟨8139244384951267630568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10852325846601690174091633 8139244384951267630568725)
                  ·
                    refine ⟨381527080544590670182909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8139244384951267630568725 381527080544590670182909)
                    ·
                      rfl

theorem cell23_2229064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2229064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229064 prefixEnd_2229064 := by exact prefixLift 2229064
  have htrace : WordTrace (prefixWord ++ tailWord_2229064) baseStart_2229064 baseEnd_2229064 := by
    simpa [prefixWord, tailWord_2229064, baseEnd_2229064] using wordTrace_append hprefix tailTrace_2229064
  have hstable : (prefixWord ++ tailWord_2229064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229064).length < 2 ^ (prefixWord ++ tailWord_2229064).sum := by decide
  have hdescent : baseEnd_2229064 < baseStart_2229064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229088 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2]
def baseStart_2229088 : Nat := 118140960795 + 2229088 * 2 ^ 59
def prefixEnd_2229088 : Nat := 4983230072969 + 3 ^ 40 * 2229088 * 2
def baseEnd_2229088 : Nat := 1144593565169479916648617

theorem tailTrace_2229088 : CollatzResearch.WordTrace tailWord_2229088 prefixEnd_2229088 1144593565169479916648617 := by
  unfold tailWord_2229088
  simp only [CollatzResearch.WordTrace]
  refine ⟨40650759274201174383299959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54201012365601565844399945 40650759274201174383299959)
  ·
    refine ⟨60976138911301761574949939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40650759274201174383299959 60976138911301761574949939)
    ·
      refine ⟨91464208366952642362424909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60976138911301761574949939 91464208366952642362424909)
      ·
        refine ⟨34299078137607240885909341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91464208366952642362424909 34299078137607240885909341)
        ·
          refine ⟨12862154301602715332216003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34299078137607240885909341 12862154301602715332216003)
          ·
            refine ⟨19293231452404072998324005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12862154301602715332216003 19293231452404072998324005)
            ·
              refine ⟨3617480897325763687185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19293231452404072998324005 3617480897325763687185751)
              ·
                refine ⟨5426221345988645530778627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617480897325763687185751 5426221345988645530778627)
                ·
                  refine ⟨8139332018982968296167941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5426221345988645530778627 8139332018982968296167941)
                  ·
                    refine ⟨1526124753559306555531489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8139332018982968296167941 1526124753559306555531489)
                    ·
                      refine ⟨1144593565169479916648617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526124753559306555531489 1144593565169479916648617)
                      ·
                        rfl

theorem cell23_2229088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_2229088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229088 prefixEnd_2229088 := by exact prefixLift 2229088
  have htrace : WordTrace (prefixWord ++ tailWord_2229088) baseStart_2229088 baseEnd_2229088 := by
    simpa [prefixWord, tailWord_2229088, baseEnd_2229088] using wordTrace_append hprefix tailTrace_2229088
  have hstable : (prefixWord ++ tailWord_2229088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229088).length < 2 ^ (prefixWord ++ tailWord_2229088).sum := by decide
  have hdescent : baseEnd_2229088 < baseStart_2229088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229128 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 5]
def baseStart_2229128 : Nat := 118140960795 + 2229128 * 2 ^ 59
def prefixEnd_2229128 : Nat := 4983230072969 + 3 ^ 40 * 2229128 * 2
def baseEnd_2229128 : Nat := 127179344932851084460937

theorem tailTrace_2229128 : CollatzResearch.WordTrace tailWord_2229128 prefixEnd_2229128 127179344932851084460937 := by
  unfold tailWord_2229128
  simp only [CollatzResearch.WordTrace]
  refine ⟨40651488734128717799028019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54201984978838290398704025 40651488734128717799028019)
  ·
    refine ⟨60977233101193076698542029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40651488734128717799028019 60977233101193076698542029)
    ·
      refine ⟨22866462412947403761953261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60977233101193076698542029 22866462412947403761953261)
      ·
        refine ⟨8574923404855276410732473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22866462412947403761953261 8574923404855276410732473)
        ·
          refine ⟨6431192553641457308049355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8574923404855276410732473 6431192553641457308049355)
          ·
            refine ⟨9646788830462185962074033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431192553641457308049355 9646788830462185962074033)
            ·
              refine ⟨7235091622846639471555525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646788830462185962074033 7235091622846639471555525)
              ·
                refine ⟨1356579679283744900916661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7235091622846639471555525 1356579679283744900916661)
                ·
                  refine ⟨127179344932851084460937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356579679283744900916661 127179344932851084460937)
                  ·
                    rfl

theorem cell23_2229128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 5].length) (baseStart_2229128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229128 prefixEnd_2229128 := by exact prefixLift 2229128
  have htrace : WordTrace (prefixWord ++ tailWord_2229128) baseStart_2229128 baseEnd_2229128 := by
    simpa [prefixWord, tailWord_2229128, baseEnd_2229128] using wordTrace_append hprefix tailTrace_2229128
  have hstable : (prefixWord ++ tailWord_2229128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229128).length < 2 ^ (prefixWord ++ tailWord_2229128).sum := by decide
  have hdescent : baseEnd_2229128 < baseStart_2229128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229131 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 7, 2]
def baseStart_2229131 : Nat := 118140960795 + 2229131 * 2 ^ 59
def prefixEnd_2229131 : Nat := 4983230072969 + 3 ^ 40 * 2229131 * 2
def baseEnd_2229131 : Nat := 1144615644837623248410919

theorem tailTrace_2229131 : CollatzResearch.WordTrace tailWord_2229131 prefixEnd_2229131 1144615644837623248410919 := by
  unfold tailWord_2229131
  simp only [CollatzResearch.WordTrace]
  refine ⟨81303086887246567110415247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54202057924831044740276831 81303086887246567110415247)
  ·
    refine ⟨121954630330869850665622871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81303086887246567110415247 121954630330869850665622871)
    ·
      refine ⟨182931945496304775998434307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121954630330869850665622871 182931945496304775998434307)
      ·
        refine ⟨274397918244457163997651461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182931945496304775998434307 274397918244457163997651461)
        ·
          refine ⟨51449609670835718249559649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274397918244457163997651461 51449609670835718249559649)
          ·
            refine ⟨38587207253126788687169737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51449609670835718249559649 38587207253126788687169737)
            ·
              refine ⟨28940405439845091515377303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38587207253126788687169737 28940405439845091515377303)
              ·
                refine ⟨43410608159767637273065955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28940405439845091515377303 43410608159767637273065955)
                ·
                  refine ⟨65115912239651455909598933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43410608159767637273065955 65115912239651455909598933)
                  ·
                    refine ⟨1526154193116830997881225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65115912239651455909598933 1526154193116830997881225)
                    ·
                      refine ⟨1144615644837623248410919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526154193116830997881225 1144615644837623248410919)
                      ·
                        rfl

theorem cell23_2229131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7, 2].length) (baseStart_2229131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229131 prefixEnd_2229131 := by exact prefixLift 2229131
  have htrace : WordTrace (prefixWord ++ tailWord_2229131) baseStart_2229131 baseEnd_2229131 := by
    simpa [prefixWord, tailWord_2229131, baseEnd_2229131] using wordTrace_append hprefix tailTrace_2229131
  have hstable : (prefixWord ++ tailWord_2229131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229131).length < 2 ^ (prefixWord ++ tailWord_2229131).sum := by decide
  have hdescent : baseEnd_2229131 < baseStart_2229131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229161 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_2229161 : Nat := 118140960795 + 2229161 * 2 ^ 59
def prefixEnd_2229161 : Nat := 4983230072969 + 3 ^ 40 * 2229161 * 2
def baseEnd_2229161 : Nat := 1144631049257258131035781

theorem tailTrace_2229161 : CollatzResearch.WordTrace tailWord_2229161 prefixEnd_2229161 1144631049257258131035781 := by
  unfold tailWord_2229161
  simp only [CollatzResearch.WordTrace]
  refine ⟨81304181077137882234007337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54202787384758588156004891 81304181077137882234007337)
  ·
    refine ⟨60978135807853411675505503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81304181077137882234007337 60978135807853411675505503)
    ·
      refine ⟨91467203711780117513258255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60978135807853411675505503 91467203711780117513258255)
      ·
        refine ⟨137200805567670176269887383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91467203711780117513258255 137200805567670176269887383)
        ·
          refine ⟨205801208351505264404831075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137200805567670176269887383 205801208351505264404831075)
          ·
            refine ⟨308701812527257896607246613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205801208351505264404831075 308701812527257896607246613)
            ·
              refine ⟨14470397462215213903464685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 308701812527257896607246613 14470397462215213903464685)
              ·
                refine ⟨5426399048330705213799257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14470397462215213903464685 5426399048330705213799257)
                ·
                  refine ⟨4069799286248028910349443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426399048330705213799257 4069799286248028910349443)
                  ·
                    refine ⟨6104698929372043365524165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4069799286248028910349443 6104698929372043365524165)
                    ·
                      refine ⟨1144631049257258131035781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6104698929372043365524165 1144631049257258131035781)
                      ·
                        rfl

theorem cell23_2229161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_2229161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229161 prefixEnd_2229161 := by exact prefixLift 2229161
  have htrace : WordTrace (prefixWord ++ tailWord_2229161) baseStart_2229161 baseEnd_2229161 := by
    simpa [prefixWord, tailWord_2229161, baseEnd_2229161] using wordTrace_append hprefix tailTrace_2229161
  have hstable : (prefixWord ++ tailWord_2229161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229161).length < 2 ^ (prefixWord ++ tailWord_2229161).sum := by decide
  have hdescent : baseEnd_2229161 < baseStart_2229161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229201 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 6]
def baseStart_2229201 : Nat := 118140960795 + 2229201 * 2 ^ 59
def prefixEnd_2229201 : Nat := 4983230072969 + 3 ^ 40 * 2229201 * 2
def baseEnd_2229201 : Nat := 127183509831493108281733

theorem tailTrace_2229201 : CollatzResearch.WordTrace tailWord_2229201 prefixEnd_2229201 127183509831493108281733 := by
  unfold tailWord_2229201
  simp only [CollatzResearch.WordTrace]
  refine ⟨81305639996992969065463457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54203759997995312710308971 81305639996992969065463457)
  ·
    refine ⟨60979229997744726799097593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81305639996992969065463457 60979229997744726799097593)
    ·
      refine ⟨45734422498308545099323195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60979229997744726799097593 45734422498308545099323195)
      ·
        refine ⟨68601633747462817648984793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45734422498308545099323195 68601633747462817648984793)
        ·
          refine ⟨51451225310597113236738595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68601633747462817648984793 51451225310597113236738595)
          ·
            refine ⟨77176837965895669855107893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51451225310597113236738595 77176837965895669855107893)
            ·
              refine ⟨7235328559302719048916365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77176837965895669855107893 7235328559302719048916365)
              ·
                refine ⟨2713248209738519643343637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7235328559302719048916365 2713248209738519643343637)
                ·
                  refine ⟨127183509831493108281733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2713248209738519643343637 127183509831493108281733)
                  ·
                    rfl

theorem cell23_2229201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_2229201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229201 prefixEnd_2229201 := by exact prefixLift 2229201
  have htrace : WordTrace (prefixWord ++ tailWord_2229201) baseStart_2229201 baseEnd_2229201 := by
    simpa [prefixWord, tailWord_2229201, baseEnd_2229201] using wordTrace_append hprefix tailTrace_2229201
  have hstable : (prefixWord ++ tailWord_2229201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229201).length < 2 ^ (prefixWord ++ tailWord_2229201).sum := by decide
  have hdescent : baseEnd_2229201 < baseStart_2229201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229215 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2229215 : Nat := 118140960795 + 2229215 * 2 ^ 59
def prefixEnd_2229215 : Nat := 4983230072969 + 3 ^ 40 * 2229215 * 2
def baseEnd_2229215 : Nat := 1144658777212600919760533

theorem tailTrace_2229215 : CollatzResearch.WordTrace tailWord_2229215 prefixEnd_2229215 1144658777212600919760533 := by
  unfold tailWord_2229215
  simp only [CollatzResearch.WordTrace]
  refine ⟨81306150618942249456473099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54204100412628166304315399 81306150618942249456473099)
  ·
    refine ⟨121959225928413374184709649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81306150618942249456473099 121959225928413374184709649)
    ·
      refine ⟨91469419446310030638532237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121959225928413374184709649 91469419446310030638532237)
      ·
        refine ⟨34301032292366261489449589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91469419446310030638532237 34301032292366261489449589)
        ·
          refine ⟨3215721777409337014635899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34301032292366261489449589 3215721777409337014635899)
          ·
            refine ⟨4823582666114005521953849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215721777409337014635899 4823582666114005521953849)
            ·
              refine ⟨3617686999585504141465387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4823582666114005521953849 3617686999585504141465387)
              ·
                refine ⟨5426530499378256212198081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617686999585504141465387 5426530499378256212198081)
                ·
                  refine ⟨4069897874533692159148561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426530499378256212198081 4069897874533692159148561)
                  ·
                    refine ⟨3052423405900269119361421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069897874533692159148561 3052423405900269119361421)
                    ·
                      refine ⟨1144658777212600919760533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052423405900269119361421 1144658777212600919760533)
                      ·
                        rfl

theorem cell23_2229215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2229215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229215 prefixEnd_2229215 := by exact prefixLift 2229215
  have htrace : WordTrace (prefixWord ++ tailWord_2229215) baseStart_2229215 baseEnd_2229215 := by
    simpa [prefixWord, tailWord_2229215, baseEnd_2229215] using wordTrace_append hprefix tailTrace_2229215
  have hstable : (prefixWord ++ tailWord_2229215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229215).length < 2 ^ (prefixWord ++ tailWord_2229215).sum := by decide
  have hdescent : baseEnd_2229215 < baseStart_2229215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229266 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2229266 : Nat := 118140960795 + 2229266 * 2 ^ 59
def prefixEnd_2229266 : Nat := 4983230072969 + 3 ^ 40 * 2229266 * 2
def baseEnd_2229266 : Nat := 1144684964725980220222799

theorem tailTrace_2229266 : CollatzResearch.WordTrace tailWord_2229266 prefixEnd_2229266 1144684964725980220222799 := by
  unfold tailWord_2229266
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327002685439371291644913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54205340494504990111053101 20327002685439371291644913)
  ·
    refine ⟨15245252014079528468733685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20327002685439371291644913 15245252014079528468733685)
    ·
      refine ⟨1429242376319955793943783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15245252014079528468733685 1429242376319955793943783)
      ·
        refine ⟨2143863564479933690915675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429242376319955793943783 2143863564479933690915675)
        ·
          refine ⟨3215795346719900536373513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143863564479933690915675 3215795346719900536373513)
          ·
            refine ⟨2411846510039925402280135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215795346719900536373513 2411846510039925402280135)
            ·
              refine ⟨3617769765059888103420203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411846510039925402280135 3617769765059888103420203)
              ·
                refine ⟨5426654647589832155130305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617769765059888103420203 5426654647589832155130305)
                ·
                  refine ⟨4069990985692374116347729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426654647589832155130305 4069990985692374116347729)
                  ·
                    refine ⟨3052493239269280587260797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4069990985692374116347729 3052493239269280587260797)
                    ·
                      refine ⟨1144684964725980220222799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052493239269280587260797 1144684964725980220222799)
                      ·
                        rfl

theorem cell23_2229266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2229266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229266 prefixEnd_2229266 := by exact prefixLift 2229266
  have htrace : WordTrace (prefixWord ++ tailWord_2229266) baseStart_2229266 baseEnd_2229266 := by
    simpa [prefixWord, tailWord_2229266, baseEnd_2229266] using wordTrace_append hprefix tailTrace_2229266
  have hstable : (prefixWord ++ tailWord_2229266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229266).length < 2 ^ (prefixWord ++ tailWord_2229266).sum := by decide
  have hdescent : baseEnd_2229266 < baseStart_2229266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229272 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2229272 : Nat := 118140960795 + 2229272 * 2 ^ 59
def prefixEnd_2229272 : Nat := 4983230072969 + 3 ^ 40 * 2229272 * 2
def baseEnd_2229272 : Nat := 1144688045609907196747771

theorem tailTrace_2229272 : CollatzResearch.WordTrace tailWord_2229272 prefixEnd_2229272 1144688045609907196747771 := by
  unfold tailWord_2229272
  simp only [CollatzResearch.WordTrace]
  refine ⟨40654114789867874095649035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54205486386490498794198713 40654114789867874095649035)
  ·
    refine ⟨60981172184801811143473553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40654114789867874095649035 60981172184801811143473553)
    ·
      refine ⟨45735879138601358357605165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60981172184801811143473553 45735879138601358357605165)
      ·
        refine ⟨17150954676975509384101937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45735879138601358357605165 17150954676975509384101937)
        ·
          refine ⟨12863216007731632038076453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17150954676975509384101937 12863216007731632038076453)
          ·
            refine ⟨2411853001449681007139335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12863216007731632038076453 2411853001449681007139335)
            ·
              refine ⟨3617779502174521510709003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411853001449681007139335 3617779502174521510709003)
              ·
                refine ⟨5426669253261782266063505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617779502174521510709003 5426669253261782266063505)
                ·
                  refine ⟨4070001939946336699547629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426669253261782266063505 4070001939946336699547629)
                  ·
                    refine ⟨1526250727479876262330361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4070001939946336699547629 1526250727479876262330361)
                    ·
                      refine ⟨1144688045609907196747771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526250727479876262330361 1144688045609907196747771)
                      ·
                        rfl

theorem cell23_2229272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2229272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229272 prefixEnd_2229272 := by exact prefixLift 2229272
  have htrace : WordTrace (prefixWord ++ tailWord_2229272) baseStart_2229272 baseEnd_2229272 := by
    simpa [prefixWord, tailWord_2229272, baseEnd_2229272] using wordTrace_append hprefix tailTrace_2229272
  have hstable : (prefixWord ++ tailWord_2229272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229272).length < 2 ^ (prefixWord ++ tailWord_2229272).sum := by decide
  have hdescent : baseEnd_2229272 < baseStart_2229272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229282 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2229282 : Nat := 118140960795 + 2229282 * 2 ^ 59
def prefixEnd_2229282 : Nat := 4983230072969 + 3 ^ 40 * 2229282 * 2
def baseEnd_2229282 : Nat := 381564393472150719207575

theorem tailTrace_2229282 : CollatzResearch.WordTrace tailWord_2229282 prefixEnd_2229282 381564393472150719207575 := by
  unfold tailWord_2229282
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327148577424879974790525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54205729539799679932774733 20327148577424879974790525)
  ·
    refine ⟨7622680716534329990546447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20327148577424879974790525 7622680716534329990546447)
    ·
      refine ⟨11434021074801494985819671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622680716534329990546447 11434021074801494985819671)
      ·
        refine ⟨17151031612202242478729507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434021074801494985819671 17151031612202242478729507)
        ·
          refine ⟨25726547418303363718094261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17151031612202242478729507 25726547418303363718094261)
          ·
            refine ⟨2411863820465940348571337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25726547418303363718094261 2411863820465940348571337)
            ·
              refine ⟨1808897865349455261428503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411863820465940348571337 1808897865349455261428503)
              ·
                refine ⟨2713346798024182892142755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808897865349455261428503 2713346798024182892142755)
                ·
                  refine ⟨4070020197036274338214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713346798024182892142755 4070020197036274338214133)
                  ·
                    refine ⟨381564393472150719207575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4070020197036274338214133 381564393472150719207575)
                    ·
                      rfl

theorem cell23_2229282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2229282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229282 prefixEnd_2229282 := by exact prefixLift 2229282
  have htrace : WordTrace (prefixWord ++ tailWord_2229282) baseStart_2229282 baseEnd_2229282 := by
    simpa [prefixWord, tailWord_2229282, baseEnd_2229282] using wordTrace_append hprefix tailTrace_2229282
  have hstable : (prefixWord ++ tailWord_2229282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229282).length < 2 ^ (prefixWord ++ tailWord_2229282).sum := by decide
  have hdescent : baseEnd_2229282 < baseStart_2229282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229285 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_2229285 : Nat := 118140960795 + 2229285 * 2 ^ 59
def prefixEnd_2229285 : Nat := 4983230072969 + 3 ^ 40 * 2229285 * 2
def baseEnd_2229285 : Nat := 1144694720858415645885211

theorem tailTrace_2229285 : CollatzResearch.WordTrace tailWord_2229285 prefixEnd_2229285 1144694720858415645885211 := by
  unfold tailWord_2229285
  simp only [CollatzResearch.WordTrace]
  refine ⟨81308703728688651411521309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54205802485792434274347539 81308703728688651411521309)
  ·
    refine ⟨30490763898258244279320491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81308703728688651411521309 30490763898258244279320491)
    ·
      refine ⟨45736145847387366418980737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30490763898258244279320491 45736145847387366418980737)
      ·
        refine ⟨34302109385540524814235553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45736145847387366418980737 34302109385540524814235553)
        ·
          refine ⟨25726582039155393610676665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34302109385540524814235553 25726582039155393610676665)
          ·
            refine ⟨19294936529366545208007499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25726582039155393610676665 19294936529366545208007499)
            ·
              refine ⟨28942404794049817812011249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19294936529366545208007499 28942404794049817812011249)
              ·
                refine ⟨21706803595537363359008437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28942404794049817812011249 21706803595537363359008437)
                ·
                  refine ⟨2035012837081627814907041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21706803595537363359008437 2035012837081627814907041)
                  ·
                    refine ⟨1526259627811220861180281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035012837081627814907041 1526259627811220861180281)
                    ·
                      refine ⟨1144694720858415645885211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526259627811220861180281 1144694720858415645885211)
                      ·
                        rfl

theorem cell23_2229285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_2229285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229285 prefixEnd_2229285 := by exact prefixLift 2229285
  have htrace : WordTrace (prefixWord ++ tailWord_2229285) baseStart_2229285 baseEnd_2229285 := by
    simpa [prefixWord, tailWord_2229285, baseEnd_2229285] using wordTrace_append hprefix tailTrace_2229285
  have hstable : (prefixWord ++ tailWord_2229285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229285).length < 2 ^ (prefixWord ++ tailWord_2229285).sum := by decide
  have hdescent : baseEnd_2229285 < baseStart_2229285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2229301 : Nat := 118140960795 + 2229301 * 2 ^ 59
def prefixEnd_2229301 : Nat := 4983230072969 + 3 ^ 40 * 2229301 * 2
def baseEnd_2229301 : Nat := 1144702936548887583285137

theorem tailTrace_2229301 : CollatzResearch.WordTrace tailWord_2229301 prefixEnd_2229301 1144702936548887583285137 := by
  unfold tailWord_2229301
  simp only [CollatzResearch.WordTrace]
  refine ⟨81309287296630686144103757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54206191531087124096069171 81309287296630686144103757)
  ·
    refine ⟨30490982736236507304038909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81309287296630686144103757 30490982736236507304038909)
    ·
      refine ⟨11434118526088690239014591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30490982736236507304038909 11434118526088690239014591)
      ·
        refine ⟨17151177789133035358521887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434118526088690239014591 17151177789133035358521887)
        ·
          refine ⟨25726766683699553037782831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17151177789133035358521887 25726766683699553037782831)
          ·
            refine ⟨38590150025549329556674247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25726766683699553037782831 38590150025549329556674247)
            ·
              refine ⟨57885225038323994335011371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38590150025549329556674247 57885225038323994335011371)
              ·
                refine ⟨86827837557485991502517057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57885225038323994335011371 86827837557485991502517057)
                ·
                  refine ⟨65120878168114493626887793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86827837557485991502517057 65120878168114493626887793)
                  ·
                    refine ⟨48840658626085870220165845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65120878168114493626887793 48840658626085870220165845)
                    ·
                      refine ⟨1144702936548887583285137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48840658626085870220165845 1144702936548887583285137)
                      ·
                        rfl

theorem cell23_2229301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2229301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229301 prefixEnd_2229301 := by exact prefixLift 2229301
  have htrace : WordTrace (prefixWord ++ tailWord_2229301) baseStart_2229301 baseEnd_2229301 := by
    simpa [prefixWord, tailWord_2229301, baseEnd_2229301] using wordTrace_append hprefix tailTrace_2229301
  have hstable : (prefixWord ++ tailWord_2229301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229301).length < 2 ^ (prefixWord ++ tailWord_2229301).sum := by decide
  have hdescent : baseEnd_2229301 < baseStart_2229301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229325 : List Nat := [1, 6, 1, 1, 1, 2, 4, 7]
def baseStart_2229325 : Nat := 118140960795 + 2229325 * 2 ^ 59
def prefixEnd_2229325 : Nat := 4983230072969 + 3 ^ 40 * 2229325 * 2
def baseEnd_2229325 : Nat := 42396861484614647755001

theorem tailTrace_2229325 : CollatzResearch.WordTrace tailWord_2229325 prefixEnd_2229325 42396861484614647755001 := by
  unfold tailWord_2229325
  simp only [CollatzResearch.WordTrace]
  refine ⟨81310162648543738242977429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54206775099029158828651619 81310162648543738242977429)
  ·
    refine ⟨3811413874150487730139567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81310162648543738242977429 3811413874150487730139567)
    ·
      refine ⟨5717120811225731595209351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811413874150487730139567 5717120811225731595209351)
      ·
        refine ⟨8575681216838597392814027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5717120811225731595209351 8575681216838597392814027)
        ·
          refine ⟨12863521825257896089221041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8575681216838597392814027 12863521825257896089221041)
          ·
            refine ⟨9647641368943422066915781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12863521825257896089221041 9647641368943422066915781)
            ·
              refine ⟨1808932756676891637546709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9647641368943422066915781 1808932756676891637546709)
              ·
                refine ⟨42396861484614647755001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1808932756676891637546709 42396861484614647755001)
                ·
                  rfl

theorem cell23_2229325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 7].length) (baseStart_2229325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229325 prefixEnd_2229325 := by exact prefixLift 2229325
  have htrace : WordTrace (prefixWord ++ tailWord_2229325) baseStart_2229325 baseEnd_2229325 := by
    simpa [prefixWord, tailWord_2229325, baseEnd_2229325] using wordTrace_append hprefix tailTrace_2229325
  have hstable : (prefixWord ++ tailWord_2229325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229325).length < 2 ^ (prefixWord ++ tailWord_2229325).sum := by decide
  have hdescent : baseEnd_2229325 < baseStart_2229325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229328 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2]
def baseStart_2229328 : Nat := 118140960795 + 2229328 * 2 ^ 59
def prefixEnd_2229328 : Nat := 4983230072969 + 3 ^ 40 * 2229328 * 2
def baseEnd_2229328 : Nat := 1144716800526558977647513

theorem tailTrace_2229328 : CollatzResearch.WordTrace tailWord_2229328 prefixEnd_2229328 1144716800526558977647513 := by
  unfold tailWord_2229328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40655136033766434877668319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54206848045021913170224425 40655136033766434877668319)
  ·
    refine ⟨60982704050649652316502479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40655136033766434877668319 60982704050649652316502479)
    ·
      refine ⟨91474056075974478474753719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60982704050649652316502479 91474056075974478474753719)
      ·
        refine ⟨137211084113961717712130579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91474056075974478474753719 137211084113961717712130579)
        ·
          refine ⟨205816626170942576568195869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137211084113961717712130579 205816626170942576568195869)
          ·
            refine ⟨77181234814103466213073451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205816626170942576568195869 77181234814103466213073451)
            ·
              refine ⟨115771852221155199319610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77181234814103466213073451 115771852221155199319610177)
              ·
                refine ⟨86828889165866399489707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115771852221155199319610177 86828889165866399489707633)
                ·
                  refine ⟨65121666874399799617280725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86828889165866399489707633 65121666874399799617280725)
                  ·
                    refine ⟨1526289067368745303530017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65121666874399799617280725 1526289067368745303530017)
                    ·
                      refine ⟨1144716800526558977647513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526289067368745303530017 1144716800526558977647513)
                      ·
                        rfl

theorem cell23_2229328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7, 2].length) (baseStart_2229328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229328 prefixEnd_2229328 := by exact prefixLift 2229328
  have htrace : WordTrace (prefixWord ++ tailWord_2229328) baseStart_2229328 baseEnd_2229328 := by
    simpa [prefixWord, tailWord_2229328, baseEnd_2229328] using wordTrace_append hprefix tailTrace_2229328
  have hstable : (prefixWord ++ tailWord_2229328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229328).length < 2 ^ (prefixWord ++ tailWord_2229328).sum := by decide
  have hdescent : baseEnd_2229328 < baseStart_2229328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229331 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_2229331 : Nat := 118140960795 + 2229331 * 2 ^ 59
def prefixEnd_2229331 : Nat := 4983230072969 + 3 ^ 40 * 2229331 * 2
def baseEnd_2229331 : Nat := 1144718340968522465909999

theorem tailTrace_2229331 : CollatzResearch.WordTrace tailWord_2229331 prefixEnd_2229331 1144718340968522465909999 := by
  unfold tailWord_2229331
  simp only [CollatzResearch.WordTrace]
  refine ⟨81310381486522001267695847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54206920991014667511797231 81310381486522001267695847)
  ·
    refine ⟨121965572229783001901543771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81310381486522001267695847 121965572229783001901543771)
    ·
      refine ⟨182948358344674502852315657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121965572229783001901543771 182948358344674502852315657)
      ·
        refine ⟨137211268758505877139236743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182948358344674502852315657 137211268758505877139236743)
        ·
          refine ⟨205816903137758815708855115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137211268758505877139236743 205816903137758815708855115)
          ·
            refine ⟨308725354706638223563282673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205816903137758815708855115 308725354706638223563282673)
            ·
              refine ⟨231544016029978667672462005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308725354706638223563282673 231544016029978667672462005)
              ·
                refine ⟨21707251502810500094293313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231544016029978667672462005 21707251502810500094293313)
                ·
                  refine ⟨16280438627107875070719985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21707251502810500094293313 16280438627107875070719985)
                  ·
                    refine ⟨12210328970330906303039989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16280438627107875070719985 12210328970330906303039989)
                    ·
                      refine ⟨1144718340968522465909999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12210328970330906303039989 1144718340968522465909999)
                      ·
                        rfl

theorem cell23_2229331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_2229331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229331 prefixEnd_2229331 := by exact prefixLift 2229331
  have htrace : WordTrace (prefixWord ++ tailWord_2229331) baseStart_2229331 baseEnd_2229331 := by
    simpa [prefixWord, tailWord_2229331, baseEnd_2229331] using wordTrace_append hprefix tailTrace_2229331
  have hstable : (prefixWord ++ tailWord_2229331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229331).length < 2 ^ (prefixWord ++ tailWord_2229331).sum := by decide
  have hdescent : baseEnd_2229331 < baseStart_2229331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229342 : List Nat := [4, 4, 1, 1, 1, 3, 9]
def baseStart_2229342 : Nat := 118140960795 + 2229342 * 2 ^ 59
def prefixEnd_2229342 : Nat := 4983230072969 + 3 ^ 40 * 2229342 * 2
def baseEnd_2229342 : Nat := 14132394929082986702129

theorem tailTrace_2229342 : CollatzResearch.WordTrace tailWord_2229342 prefixEnd_2229342 14132394929082986702129 := by
  unfold tailWord_2229342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163847836185268768293285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54207188459654766764230853 10163847836185268768293285)
  ·
    refine ⟨1905721469284737894054991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10163847836185268768293285 1905721469284737894054991)
    ·
      refine ⟨2858582203927106841082487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905721469284737894054991 2858582203927106841082487)
      ·
        refine ⟨4287873305890660261623731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858582203927106841082487 4287873305890660261623731)
        ·
          refine ⟨6431809958835990392435597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287873305890660261623731 6431809958835990392435597)
          ·
            refine ⟨2411928734563496397163349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6431809958835990392435597 2411928734563496397163349)
            ·
              refine ⟨14132394929082986702129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2411928734563496397163349 14132394929082986702129)
              ·
                rfl

theorem cell23_2229342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 9].length) (baseStart_2229342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229342 prefixEnd_2229342 := by exact prefixLift 2229342
  have htrace : WordTrace (prefixWord ++ tailWord_2229342) baseStart_2229342 baseEnd_2229342 := by
    simpa [prefixWord, tailWord_2229342, baseEnd_2229342] using wordTrace_append hprefix tailTrace_2229342
  have hstable : (prefixWord ++ tailWord_2229342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229342).length < 2 ^ (prefixWord ++ tailWord_2229342).sum := by decide
  have hdescent : baseEnd_2229342 < baseStart_2229342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229371 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_2229371 : Nat := 118140960795 + 2229371 * 2 ^ 59
def prefixEnd_2229371 : Nat := 4983230072969 + 3 ^ 40 * 2229371 * 2
def baseEnd_2229371 : Nat := 1144738880194702309409815

theorem tailTrace_2229371 : CollatzResearch.WordTrace tailWord_2229371 prefixEnd_2229371 1144738880194702309409815 := by
  unfold tailWord_2229371
  simp only [CollatzResearch.WordTrace]
  refine ⟨81311840406377088099151967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54207893604251392066101311 81311840406377088099151967)
  ·
    refine ⟨121967760609565632148727951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81311840406377088099151967 121967760609565632148727951)
    ·
      refine ⟨182951640914348448223091927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121967760609565632148727951 182951640914348448223091927)
      ·
        refine ⟨274427461371522672334637891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182951640914348448223091927 274427461371522672334637891)
        ·
          refine ⟨411641192057284008501956837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274427461371522672334637891 411641192057284008501956837)
          ·
            refine ⟨77182723510740751594116907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 411641192057284008501956837 77182723510740751594116907)
            ·
              refine ⟨115774085266111127391175361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77182723510740751594116907 115774085266111127391175361)
              ·
                refine ⟨86830563949583345543381521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115774085266111127391175361 86830563949583345543381521)
                ·
                  refine ⟨65122922962187509157536141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86830563949583345543381521 65122922962187509157536141)
                  ·
                    refine ⟨24421096110820315934076053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65122922962187509157536141 24421096110820315934076053)
                    ·
                      refine ⟨1144738880194702309409815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24421096110820315934076053 1144738880194702309409815)
                      ·
                        rfl

theorem cell23_2229371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_2229371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229371 prefixEnd_2229371 := by exact prefixLift 2229371
  have htrace : WordTrace (prefixWord ++ tailWord_2229371) baseStart_2229371 baseEnd_2229371 := by
    simpa [prefixWord, tailWord_2229371, baseEnd_2229371] using wordTrace_append hprefix tailTrace_2229371
  have hstable : (prefixWord ++ tailWord_2229371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229371).length < 2 ^ (prefixWord ++ tailWord_2229371).sum := by decide
  have hdescent : baseEnd_2229371 < baseStart_2229371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229391 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_2229391 : Nat := 118140960795 + 2229391 * 2 ^ 59
def prefixEnd_2229391 : Nat := 4983230072969 + 3 ^ 40 * 2229391 * 2
def baseEnd_2229391 : Nat := 1144749149807792231159723

theorem tailTrace_2229391 : CollatzResearch.WordTrace tailWord_2229391 prefixEnd_2229391 1144749149807792231159723 := by
  unfold tailWord_2229391
  simp only [CollatzResearch.WordTrace]
  refine ⟨81312569866304631514880027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54208379910869754343253351 81312569866304631514880027)
  ·
    refine ⟨121968854799456947272320041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81312569866304631514880027 121968854799456947272320041)
    ·
      refine ⟨91476641099592710454240031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121968854799456947272320041 91476641099592710454240031)
      ·
        refine ⟨137214961649389065681360047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91476641099592710454240031 137214961649389065681360047)
        ·
          refine ⟨205822442474083598522040071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137214961649389065681360047 205822442474083598522040071)
          ·
            refine ⟨308733663711125397783060107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205822442474083598522040071 308733663711125397783060107)
            ·
              refine ⟨463100495566688096674590161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308733663711125397783060107 463100495566688096674590161)
              ·
                refine ⟨347325371675016072505942621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463100495566688096674590161 347325371675016072505942621)
                ·
                  refine ⟨130247014378131027189728483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347325371675016072505942621 130247014378131027189728483)
                  ·
                    refine ⟨195370521567196540784592725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130247014378131027189728483 195370521567196540784592725)
                    ·
                      refine ⟨1144749149807792231159723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 195370521567196540784592725 1144749149807792231159723)
                      ·
                        rfl

theorem cell23_2229391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_2229391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229391 prefixEnd_2229391 := by exact prefixLift 2229391
  have htrace : WordTrace (prefixWord ++ tailWord_2229391) baseStart_2229391 baseEnd_2229391 := by
    simpa [prefixWord, tailWord_2229391, baseEnd_2229391] using wordTrace_append hprefix tailTrace_2229391
  have hstable : (prefixWord ++ tailWord_2229391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229391).length < 2 ^ (prefixWord ++ tailWord_2229391).sum := by decide
  have hdescent : baseEnd_2229391 < baseStart_2229391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229409 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2229409 : Nat := 118140960795 + 2229409 * 2 ^ 59
def prefixEnd_2229409 : Nat := 4983230072969 + 3 ^ 40 * 2229409 * 2
def baseEnd_2229409 : Nat := 1144758392459573160734641

theorem tailTrace_2229409 : CollatzResearch.WordTrace tailWord_2229409 prefixEnd_2229409 1144758392459573160734641 := by
  unfold tailWord_2229409
  simp only [CollatzResearch.WordTrace]
  refine ⟨81313226380239420589035281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54208817586826280392690187 81313226380239420589035281)
  ·
    refine ⟨60984919785179565441776461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81313226380239420589035281 60984919785179565441776461)
    ·
      refine ⟨22869344919442337040666173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60984919785179565441776461 22869344919442337040666173)
      ·
        refine ⟨8576004344790876390249815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22869344919442337040666173 8576004344790876390249815)
        ·
          refine ⟨12864006517186314585374723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576004344790876390249815 12864006517186314585374723)
          ·
            refine ⟨19296009775779471878062085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864006517186314585374723 19296009775779471878062085)
            ·
              refine ⟨3618001832958650977136641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19296009775779471878062085 3618001832958650977136641)
              ·
                refine ⟨2713501374718988232852481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618001832958650977136641 2713501374718988232852481)
                ·
                  refine ⟨2035126031039241174639361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713501374718988232852481 2035126031039241174639361)
                  ·
                    refine ⟨1526344523279430880979521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035126031039241174639361 1526344523279430880979521)
                    ·
                      refine ⟨1144758392459573160734641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526344523279430880979521 1144758392459573160734641)
                      ·
                        rfl

theorem cell23_2229409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2229409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229409 prefixEnd_2229409 := by exact prefixLift 2229409
  have htrace : WordTrace (prefixWord ++ tailWord_2229409) baseStart_2229409 baseEnd_2229409 := by
    simpa [prefixWord, tailWord_2229409, baseEnd_2229409] using wordTrace_append hprefix tailTrace_2229409
  have hstable : (prefixWord ++ tailWord_2229409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229409).length < 2 ^ (prefixWord ++ tailWord_2229409).sum := by decide
  have hdescent : baseEnd_2229409 < baseStart_2229409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229425 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2229425 : Nat := 118140960795 + 2229425 * 2 ^ 59
def prefixEnd_2229425 : Nat := 4983230072969 + 3 ^ 40 * 2229425 * 2
def baseEnd_2229425 : Nat := 1144766608150045098134567

theorem tailTrace_2229425 : CollatzResearch.WordTrace tailWord_2229425 prefixEnd_2229425 1144766608150045098134567 := by
  unfold tailWord_2229425
  simp only [CollatzResearch.WordTrace]
  refine ⟨81313809948181455321617729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54209206632120970214411819 81313809948181455321617729)
  ·
    refine ⟨60985357461136091491213297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81313809948181455321617729 60985357461136091491213297)
    ·
      refine ⟨45739018095852068618409973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60985357461136091491213297 45739018095852068618409973)
      ·
        refine ⟨4288032946486131432975935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45739018095852068618409973 4288032946486131432975935)
        ·
          refine ⟨6432049419729197149463903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288032946486131432975935 6432049419729197149463903)
          ·
            refine ⟨9648074129593795724195855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6432049419729197149463903 9648074129593795724195855)
            ·
              refine ⟨14472111194390693586293783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9648074129593795724195855 14472111194390693586293783)
              ·
                refine ⟨21708166791586040379440675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14472111194390693586293783 21708166791586040379440675)
                ·
                  refine ⟨32562250187379060569161013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21708166791586040379440675 32562250187379060569161013)
                  ·
                    refine ⟨3052710955066786928358845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32562250187379060569161013 3052710955066786928358845)
                    ·
                      refine ⟨1144766608150045098134567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052710955066786928358845 1144766608150045098134567)
                      ·
                        rfl

theorem cell23_2229425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2229425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229425 prefixEnd_2229425 := by exact prefixLift 2229425
  have htrace : WordTrace (prefixWord ++ tailWord_2229425) baseStart_2229425 baseEnd_2229425 := by
    simpa [prefixWord, tailWord_2229425, baseEnd_2229425] using wordTrace_append hprefix tailTrace_2229425
  have hstable : (prefixWord ++ tailWord_2229425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229425).length < 2 ^ (prefixWord ++ tailWord_2229425).sum := by decide
  have hdescent : baseEnd_2229425 < baseStart_2229425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229460 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2229460 : Nat := 118140960795 + 2229460 * 2 ^ 59
def prefixEnd_2229460 : Nat := 4983230072969 + 3 ^ 40 * 2229460 * 2
def baseEnd_2229460 : Nat := 1144784579972952461196907

theorem tailTrace_2229460 : CollatzResearch.WordTrace tailWord_2229460 prefixEnd_2229460 1144784579972952461196907 := by
  unfold tailWord_2229460
  simp only [CollatzResearch.WordTrace]
  refine ⟨40657543251527328149570917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54210057668703104199427889 40657543251527328149570917)
  ·
    refine ⟨7623289359661374028044547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40657543251527328149570917 7623289359661374028044547)
    ·
      refine ⟨11434934039492061042066821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623289359661374028044547 11434934039492061042066821)
      ·
        refine ⟨2144050132404761445387529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11434934039492061042066821 2144050132404761445387529)
        ·
          refine ⟨1608037599303571084040647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2144050132404761445387529 1608037599303571084040647)
          ·
            refine ⟨2412056398955356626060971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608037599303571084040647 2412056398955356626060971)
            ·
              refine ⟨3618084598433034939091457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412056398955356626060971 3618084598433034939091457)
              ·
                refine ⟨2713563448824776204318593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618084598433034939091457 2713563448824776204318593)
                ·
                  refine ⟨2035172586618582153238945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713563448824776204318593 2035172586618582153238945)
                  ·
                    refine ⟨1526379439963936614929209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035172586618582153238945 1526379439963936614929209)
                    ·
                      refine ⟨1144784579972952461196907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526379439963936614929209 1144784579972952461196907)
                      ·
                        rfl

theorem cell23_2229460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2229460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229460 prefixEnd_2229460 := by exact prefixLift 2229460
  have htrace : WordTrace (prefixWord ++ tailWord_2229460) baseStart_2229460 baseEnd_2229460 := by
    simpa [prefixWord, tailWord_2229460, baseEnd_2229460] using wordTrace_append hprefix tailTrace_2229460
  have hstable : (prefixWord ++ tailWord_2229460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229460).length < 2 ^ (prefixWord ++ tailWord_2229460).sum := by decide
  have hdescent : baseEnd_2229460 < baseStart_2229460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229482 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_2229482 : Nat := 118140960795 + 2229482 * 2 ^ 59
def prefixEnd_2229482 : Nat := 4983230072969 + 3 ^ 40 * 2229482 * 2
def baseEnd_2229482 : Nat := 1144795876547351375121805

theorem tailTrace_2229482 : CollatzResearch.WordTrace tailWord_2229482 prefixEnd_2229482 1144795876547351375121805 := by
  unfold tailWord_2229482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20328972227243738514110675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54210592605983302704295133 20328972227243738514110675)
  ·
    refine ⟨30493458340865607771166013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20328972227243738514110675 30493458340865607771166013)
    ·
      refine ⟨11435046877824602914187255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30493458340865607771166013 11435046877824602914187255)
      ·
        refine ⟨17152570316736904371280883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11435046877824602914187255 17152570316736904371280883)
        ·
          refine ⟨25728855475105356556921325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17152570316736904371280883 25728855475105356556921325)
          ·
            refine ⟨9648320803164508708845497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25728855475105356556921325 9648320803164508708845497)
            ·
              refine ⟨7236240602373381531634123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9648320803164508708845497 7236240602373381531634123)
              ·
                refine ⟨10854360903560072297451185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7236240602373381531634123 10854360903560072297451185)
                ·
                  refine ⟨8140770677670054223088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10854360903560072297451185 8140770677670054223088389)
                  ·
                    refine ⟨1526394502063135166829073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8140770677670054223088389 1526394502063135166829073)
                    ·
                      refine ⟨1144795876547351375121805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526394502063135166829073 1144795876547351375121805)
                      ·
                        rfl

theorem cell23_2229482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_2229482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229482 prefixEnd_2229482 := by exact prefixLift 2229482
  have htrace : WordTrace (prefixWord ++ tailWord_2229482) baseStart_2229482 baseEnd_2229482 := by
    simpa [prefixWord, tailWord_2229482, baseEnd_2229482] using wordTrace_append hprefix tailTrace_2229482
  have hstable : (prefixWord ++ tailWord_2229482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229482).length < 2 ^ (prefixWord ++ tailWord_2229482).sum := by decide
  have hdescent : baseEnd_2229482 < baseStart_2229482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229502 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2229502 : Nat := 118140960795 + 2229502 * 2 ^ 59
def prefixEnd_2229502 : Nat := 4983230072969 + 3 ^ 40 * 2229502 * 2
def baseEnd_2229502 : Nat := 1144806146160441296871713

theorem tailTrace_2229502 : CollatzResearch.WordTrace tailWord_2229502 prefixEnd_2229502 1144806146160441296871713 := by
  unfold tailWord_2229502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164577296112812184021345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54211078912601664981447173 10164577296112812184021345)
  ·
    refine ⟨7623432972084609138016009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10164577296112812184021345 7623432972084609138016009)
    ·
      refine ⟨5717574729063456853512007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7623432972084609138016009 5717574729063456853512007)
      ·
        refine ⟨8576362093595185280268011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5717574729063456853512007 8576362093595185280268011)
        ·
          refine ⟨12864543140392777920402017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576362093595185280268011 12864543140392777920402017)
          ·
            refine ⟨9648407355294583440301513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12864543140392777920402017 9648407355294583440301513)
            ·
              refine ⟨7236305516470937580226135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9648407355294583440301513 7236305516470937580226135)
              ·
                refine ⟨10854458274706406370339203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7236305516470937580226135 10854458274706406370339203)
                ·
                  refine ⟨16281687412059609555508805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10854458274706406370339203 16281687412059609555508805)
                  ·
                    refine ⟨3052816389761176791657901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16281687412059609555508805 3052816389761176791657901)
                    ·
                      refine ⟨1144806146160441296871713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052816389761176791657901 1144806146160441296871713)
                      ·
                        rfl

theorem cell23_2229502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2229502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229502 prefixEnd_2229502 := by exact prefixLift 2229502
  have htrace : WordTrace (prefixWord ++ tailWord_2229502) baseStart_2229502 baseEnd_2229502 := by
    simpa [prefixWord, tailWord_2229502, baseEnd_2229502] using wordTrace_append hprefix tailTrace_2229502
  have hstable : (prefixWord ++ tailWord_2229502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229502).length < 2 ^ (prefixWord ++ tailWord_2229502).sum := by decide
  have hdescent : baseEnd_2229502 < baseStart_2229502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229566 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_2229566 : Nat := 118140960795 + 2229566 * 2 ^ 59
def prefixEnd_2229566 : Nat := 4983230072969 + 3 ^ 40 * 2229566 * 2
def baseEnd_2229566 : Nat := 1144839008922329046471419

theorem tailTrace_2229566 : CollatzResearch.WordTrace tailWord_2229566 prefixEnd_2229566 1144839008922329046471419 := by
  unfold tailWord_2229566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164869080083829550312569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54212635093780424268333701 10164869080083829550312569)
  ·
    refine ⟨7623651810062872162734427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10164869080083829550312569 7623651810062872162734427)
    ·
      refine ⟨11435477715094308244101641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623651810062872162734427 11435477715094308244101641)
      ·
        refine ⟨8576608286320731183076231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11435477715094308244101641 8576608286320731183076231)
        ·
          refine ⟨12864912429481096774614347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576608286320731183076231 12864912429481096774614347)
          ·
            refine ⟨19297368644221645161921521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864912429481096774614347 19297368644221645161921521)
            ·
              refine ⟨14473026483166233871441141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19297368644221645161921521 14473026483166233871441141)
              ·
                refine ⟨1356846232796834425447607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14473026483166233871441141 1356846232796834425447607)
                ·
                  refine ⟨2035269349195251638171411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356846232796834425447607 2035269349195251638171411)
                  ·
                    refine ⟨3052904023792877457257117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035269349195251638171411 3052904023792877457257117)
                    ·
                      refine ⟨1144839008922329046471419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3052904023792877457257117 1144839008922329046471419)
                      ·
                        rfl

theorem cell23_2229566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_2229566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229566 prefixEnd_2229566 := by exact prefixLift 2229566
  have htrace : WordTrace (prefixWord ++ tailWord_2229566) baseStart_2229566 baseEnd_2229566 := by
    simpa [prefixWord, tailWord_2229566, baseEnd_2229566] using wordTrace_append hprefix tailTrace_2229566
  have hstable : (prefixWord ++ tailWord_2229566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229566).length < 2 ^ (prefixWord ++ tailWord_2229566).sum := by decide
  have hdescent : baseEnd_2229566 < baseStart_2229566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229585 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_2229585 : Nat := 118140960795 + 2229585 * 2 ^ 59
def prefixEnd_2229585 : Nat := 4983230072969 + 3 ^ 40 * 2229585 * 2
def baseEnd_2229585 : Nat := 1144848765054764472133831

theorem tailTrace_2229585 : CollatzResearch.WordTrace tailWord_2229585 prefixEnd_2229585 1144848765054764472133831 := by
  unfold tailWord_2229585
  simp only [CollatzResearch.WordTrace]
  refine ⟨81319645627601802647442209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54213097085067868431628139 81319645627601802647442209)
  ·
    refine ⟨60989734220701351985581657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81319645627601802647442209 60989734220701351985581657)
    ·
      refine ⟨45742300665526013989186243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60989734220701351985581657 45742300665526013989186243)
      ·
        refine ⟨68613450998289020983779365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45742300665526013989186243 68613450998289020983779365)
        ·
          refine ⟨12865022062179191434458631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68613450998289020983779365 12865022062179191434458631)
          ·
            refine ⟨19297533093268787151687947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12865022062179191434458631 19297533093268787151687947)
            ·
              refine ⟨28946299639903180727531921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19297533093268787151687947 28946299639903180727531921)
              ·
                refine ⟨21709724729927385545648941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28946299639903180727531921 21709724729927385545648941)
                ·
                  refine ⟨8141146773722769579618353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21709724729927385545648941 8141146773722769579618353)
                  ·
                    refine ⟨6105860080292077184713765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8141146773722769579618353 6105860080292077184713765)
                    ·
                      refine ⟨1144848765054764472133831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6105860080292077184713765 1144848765054764472133831)
                      ·
                        rfl

theorem cell23_2229585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_2229585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229585 prefixEnd_2229585 := by exact prefixLift 2229585
  have htrace : WordTrace (prefixWord ++ tailWord_2229585) baseStart_2229585 baseEnd_2229585 := by
    simpa [prefixWord, tailWord_2229585, baseEnd_2229585] using wordTrace_append hprefix tailTrace_2229585
  have hstable : (prefixWord ++ tailWord_2229585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229585).length < 2 ^ (prefixWord ++ tailWord_2229585).sum := by decide
  have hdescent : baseEnd_2229585 < baseStart_2229585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229612 : List Nat := [2, 2, 1, 1, 5, 2, 3, 7]
def baseStart_2229612 : Nat := 118140960795 + 2229612 * 2 ^ 59
def prefixEnd_2229612 : Nat := 4983230072969 + 3 ^ 40 * 2229612 * 2
def baseEnd_2229612 : Nat := 42402319593793920981341

theorem tailTrace_2229612 : CollatzResearch.WordTrace tailWord_2229612 prefixEnd_2229612 42402319593793920981341 := by
  unfold tailWord_2229612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40660315199251993129337545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54213753599002657505783393 40660315199251993129337545)
  ·
    refine ⟨30495236399438994847003159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40660315199251993129337545 30495236399438994847003159)
    ·
      refine ⟨45742854599158492270504739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30495236399438994847003159 45742854599158492270504739)
      ·
        refine ⟨68614281898737738405757109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45742854599158492270504739 68614281898737738405757109)
        ·
          refine ⟨6432588928006662975539729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68614281898737738405757109 6432588928006662975539729)
          ·
            refine ⟨4824441696004997231654797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6432588928006662975539729 4824441696004997231654797)
            ·
              refine ⟨1809165636001873961870549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4824441696004997231654797 1809165636001873961870549)
              ·
                refine ⟨42402319593793920981341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1809165636001873961870549 42402319593793920981341)
                ·
                  rfl

theorem cell23_2229612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 7].length) (baseStart_2229612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229612 prefixEnd_2229612 := by exact prefixLift 2229612
  have htrace : WordTrace (prefixWord ++ tailWord_2229612) baseStart_2229612 baseEnd_2229612 := by
    simpa [prefixWord, tailWord_2229612, baseEnd_2229612] using wordTrace_append hprefix tailTrace_2229612
  have hstable : (prefixWord ++ tailWord_2229612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229612).length < 2 ^ (prefixWord ++ tailWord_2229612).sum := by decide
  have hdescent : baseEnd_2229612 < baseStart_2229612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229633 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2229633 : Nat := 118140960795 + 2229633 * 2 ^ 59
def prefixEnd_2229633 : Nat := 4983230072969 + 3 ^ 40 * 2229633 * 2
def baseEnd_2229633 : Nat := 381624470708726761444537

theorem tailTrace_2229633 : CollatzResearch.WordTrace tailWord_2229633 prefixEnd_2229633 381624470708726761444537 := by
  unfold tailWord_2229633
  simp only [CollatzResearch.WordTrace]
  refine ⟨81321396331427906845189553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54214264220951937896793035 81321396331427906845189553)
  ·
    refine ⟨60991047248570930133892165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81321396331427906845189553 60991047248570930133892165)
    ·
      refine ⟨11435821359107049400104781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60991047248570930133892165 11435821359107049400104781)
      ·
        refine ⟨4288433009665143525039293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11435821359107049400104781 4288433009665143525039293)
        ·
          refine ⟨1608162378624428821889735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4288433009665143525039293 1608162378624428821889735)
          ·
            refine ⟨2412243567936643232834603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608162378624428821889735 2412243567936643232834603)
            ·
              refine ⟨3618365351904964849251905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412243567936643232834603 3618365351904964849251905)
              ·
                refine ⟨2713774013928723636938929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618365351904964849251905 2713774013928723636938929)
                ·
                  refine ⟨2035330510446542727704197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713774013928723636938929 2035330510446542727704197)
                  ·
                    refine ⟨381624470708726761444537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2035330510446542727704197 381624470708726761444537)
                    ·
                      rfl

theorem cell23_2229633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2229633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229633 prefixEnd_2229633 := by exact prefixLift 2229633
  have htrace : WordTrace (prefixWord ++ tailWord_2229633) baseStart_2229633 baseEnd_2229633 := by
    simpa [prefixWord, tailWord_2229633, baseEnd_2229633] using wordTrace_append hprefix tailTrace_2229633
  have hstable : (prefixWord ++ tailWord_2229633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229633).length < 2 ^ (prefixWord ++ tailWord_2229633).sum := by decide
  have hdescent : baseEnd_2229633 < baseStart_2229633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229639 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2229639 : Nat := 118140960795 + 2229639 * 2 ^ 59
def prefixEnd_2229639 : Nat := 4983230072969 + 3 ^ 40 * 2229639 * 2
def baseEnd_2229639 : Nat := 1144876493010107260858583

theorem tailTrace_2229639 : CollatzResearch.WordTrace tailWord_2229639 prefixEnd_2229639 1144876493010107260858583 := by
  unfold tailWord_2229639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81321615169406169869907971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54214410112937446579938647 81321615169406169869907971)
  ·
    refine ⟨121982422754109254804861957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81321615169406169869907971 121982422754109254804861957)
    ·
      refine ⟨22871704266395485275911617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121982422754109254804861957 22871704266395485275911617)
      ·
        refine ⟨17153778199796613956933713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22871704266395485275911617 17153778199796613956933713)
        ·
          refine ⟨12865333649847460467700285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17153778199796613956933713 12865333649847460467700285)
          ·
            refine ⟨4824500118692797675387607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12865333649847460467700285 4824500118692797675387607)
            ·
              refine ⟨7236750178039196513081411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824500118692797675387607 7236750178039196513081411)
              ·
                refine ⟨10855125267058794769622117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7236750178039196513081411 10855125267058794769622117)
                ·
                  refine ⟨2035335987573524019304147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10855125267058794769622117 2035335987573524019304147)
                  ·
                    refine ⟨3053003981360286028956221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035335987573524019304147 3053003981360286028956221)
                    ·
                      refine ⟨1144876493010107260858583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053003981360286028956221 1144876493010107260858583)
                      ·
                        rfl

theorem cell23_2229639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2229639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229639 prefixEnd_2229639 := by exact prefixLift 2229639
  have htrace : WordTrace (prefixWord ++ tailWord_2229639) baseStart_2229639 baseEnd_2229639 := by
    simpa [prefixWord, tailWord_2229639, baseEnd_2229639] using wordTrace_append hprefix tailTrace_2229639
  have hstable : (prefixWord ++ tailWord_2229639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229639).length < 2 ^ (prefixWord ++ tailWord_2229639).sum := by decide
  have hdescent : baseEnd_2229639 < baseStart_2229639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229656 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2229656 : Nat := 118140960795 + 2229656 * 2 ^ 59
def prefixEnd_2229656 : Nat := 4983230072969 + 3 ^ 40 * 2229656 * 2
def baseEnd_2229656 : Nat := 1144885222181233694346005

theorem tailTrace_2229656 : CollatzResearch.WordTrace tailWord_2229656 prefixEnd_2229656 1144885222181233694346005 := by
  unfold tailWord_2229656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40661117605172290886638411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54214823473563054515517881 40661117605172290886638411)
  ·
    refine ⟨60991676407758436329957617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40661117605172290886638411 60991676407758436329957617)
    ·
      refine ⟨45743757305818827247468213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60991676407758436329957617 45743757305818827247468213)
      ·
        refine ⟨4288477247420515054450145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45743757305818827247468213 4288477247420515054450145)
        ·
          refine ⟨3216357935565386290837609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288477247420515054450145 3216357935565386290837609)
          ·
            refine ⟨2412268451674039718128207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3216357935565386290837609 2412268451674039718128207)
            ·
              refine ⟨3618402677511059577192311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412268451674039718128207 3618402677511059577192311)
              ·
                refine ⟨5427604016266589365788467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618402677511059577192311 5427604016266589365788467)
                ·
                  refine ⟨8141406024399884048682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427604016266589365788467 8141406024399884048682701)
                  ·
                    refine ⟨3053027259149956518256013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8141406024399884048682701 3053027259149956518256013)
                    ·
                      refine ⟨1144885222181233694346005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053027259149956518256013 1144885222181233694346005)
                      ·
                        rfl

theorem cell23_2229656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2229656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229656 prefixEnd_2229656 := by exact prefixLift 2229656
  have htrace : WordTrace (prefixWord ++ tailWord_2229656) baseStart_2229656 baseEnd_2229656 := by
    simpa [prefixWord, tailWord_2229656, baseEnd_2229656] using wordTrace_append hprefix tailTrace_2229656
  have hstable : (prefixWord ++ tailWord_2229656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229656).length < 2 ^ (prefixWord ++ tailWord_2229656).sum := by decide
  have hdescent : baseEnd_2229656 < baseStart_2229656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229666 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2229666 : Nat := 118140960795 + 2229666 * 2 ^ 59
def prefixEnd_2229666 : Nat := 4983230072969 + 3 ^ 40 * 2229666 * 2
def baseEnd_2229666 : Nat := 1144890356987778655220959

theorem tailTrace_2229666 : CollatzResearch.WordTrace tailWord_2229666 prefixEnd_2229666 1144890356987778655220959 := by
  unfold tailWord_2229666
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330649985077088370285213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54215066626872235654093901 20330649985077088370285213)
  ·
    refine ⟨7623993744403908138856955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20330649985077088370285213 7623993744403908138856955)
    ·
      refine ⟨11435990616605862208285433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623993744403908138856955 11435990616605862208285433)
      ·
        refine ⟨8576992962454396656214075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11435990616605862208285433 8576992962454396656214075)
        ·
          refine ⟨12865489443681594984321113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576992962454396656214075 12865489443681594984321113)
          ·
            refine ⟨9649117082761196238240835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12865489443681594984321113 9649117082761196238240835)
            ·
              refine ⟨14473675624141794357361253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9649117082761196238240835 14473675624141794357361253)
              ·
                refine ⟨2713814179526586442005235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14473675624141794357361253 2713814179526586442005235)
                ·
                  refine ⟨4070721269289879663007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713814179526586442005235 4070721269289879663007853)
                  ·
                    refine ⟨1526520475983704873627945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4070721269289879663007853 1526520475983704873627945)
                    ·
                      refine ⟨1144890356987778655220959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526520475983704873627945 1144890356987778655220959)
                      ·
                        rfl

theorem cell23_2229666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2229666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229666 prefixEnd_2229666 := by exact prefixLift 2229666
  have htrace : WordTrace (prefixWord ++ tailWord_2229666) baseStart_2229666 baseEnd_2229666 := by
    simpa [prefixWord, tailWord_2229666, baseEnd_2229666] using wordTrace_append hprefix tailTrace_2229666
  have hstable : (prefixWord ++ tailWord_2229666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229666).length < 2 ^ (prefixWord ++ tailWord_2229666).sum := by decide
  have hdescent : baseEnd_2229666 < baseStart_2229666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229742 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2229742 : Nat := 118140960795 + 2229742 * 2 ^ 59
def prefixEnd_2229742 : Nat := 4983230072969 + 3 ^ 40 * 2229742 * 2
def baseEnd_2229742 : Nat := 1144929381517520357870609

theorem tailTrace_2229742 : CollatzResearch.WordTrace tailWord_2229742 prefixEnd_2229742 1144929381517520357870609 := by
  unfold tailWord_2229742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165671486004127307613435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54216914592022012307271653 10165671486004127307613435)
  ·
    refine ⟨15248507229006190961420153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165671486004127307613435 15248507229006190961420153)
    ·
      refine ⟨11436380421754643221065115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15248507229006190961420153 11436380421754643221065115)
      ·
        refine ⟨17154570632631964831597673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11436380421754643221065115 17154570632631964831597673)
        ·
          refine ⟨12865927974473973623698255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17154570632631964831597673 12865927974473973623698255)
          ·
            refine ⟨19298891961710960435547383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12865927974473973623698255 19298891961710960435547383)
            ·
              refine ⟨28948337942566440653321075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19298891961710960435547383 28948337942566440653321075)
              ·
                refine ⟨43422506913849660979981613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28948337942566440653321075 43422506913849660979981613)
                ·
                  refine ⟨16283440092693622867493105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43422506913849660979981613 16283440092693622867493105)
                  ·
                    refine ⟨12212580069520217150619829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16283440092693622867493105 12212580069520217150619829)
                    ·
                      refine ⟨1144929381517520357870609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12212580069520217150619829 1144929381517520357870609)
                      ·
                        rfl

theorem cell23_2229742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2229742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229742 prefixEnd_2229742 := by exact prefixLift 2229742
  have htrace : WordTrace (prefixWord ++ tailWord_2229742) baseStart_2229742 baseEnd_2229742 := by
    simpa [prefixWord, tailWord_2229742, baseEnd_2229742] using wordTrace_append hprefix tailTrace_2229742
  have hstable : (prefixWord ++ tailWord_2229742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229742).length < 2 ^ (prefixWord ++ tailWord_2229742).sum := by decide
  have hdescent : baseEnd_2229742 < baseStart_2229742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229769 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 4, 2]
def baseStart_2229769 : Nat := 118140960795 + 2229769 * 2 ^ 59
def prefixEnd_2229769 : Nat := 4983230072969 + 3 ^ 40 * 2229769 * 2
def baseEnd_2229769 : Nat := 1144943245495191752232985

theorem tailTrace_2229769 : CollatzResearch.WordTrace tailWord_2229769 prefixEnd_2229769 1144943245495191752232985 := by
  unfold tailWord_2229769
  simp only [CollatzResearch.WordTrace]
  refine ⟨81326356658935202072140361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54217571105956801381426907 81326356658935202072140361)
  ·
    refine ⟨60994767494201401554105271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81326356658935202072140361 60994767494201401554105271)
    ·
      refine ⟨91492151241302102331157907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60994767494201401554105271 91492151241302102331157907)
      ·
        refine ⟨137238226861953153496736861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91492151241302102331157907 137238226861953153496736861)
        ·
          refine ⟨51464335073232432561276323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137238226861953153496736861 51464335073232432561276323)
          ·
            refine ⟨77196502609848648841914485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51464335073232432561276323 77196502609848648841914485)
            ·
              refine ⟨7237172119673310828929483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77196502609848648841914485 7237172119673310828929483)
              ·
                refine ⟨10855758179509966243394225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237172119673310828929483 10855758179509966243394225)
                ·
                  refine ⟨8141818634632474682545669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10855758179509966243394225 8141818634632474682545669)
                  ·
                    refine ⟨1526590993993589002977313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8141818634632474682545669 1526590993993589002977313)
                    ·
                      refine ⟨1144943245495191752232985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526590993993589002977313 1144943245495191752232985)
                      ·
                        rfl

theorem cell23_2229769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4, 2].length) (baseStart_2229769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229769 prefixEnd_2229769 := by exact prefixLift 2229769
  have htrace : WordTrace (prefixWord ++ tailWord_2229769) baseStart_2229769 baseEnd_2229769 := by
    simpa [prefixWord, tailWord_2229769, baseEnd_2229769] using wordTrace_append hprefix tailTrace_2229769
  have hstable : (prefixWord ++ tailWord_2229769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229769).length < 2 ^ (prefixWord ++ tailWord_2229769).sum := by decide
  have hdescent : baseEnd_2229769 < baseStart_2229769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229779 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 3, 4]
def baseStart_2229779 : Nat := 118140960795 + 2229779 * 2 ^ 59
def prefixEnd_2229779 : Nat := 4983230072969 + 3 ^ 40 * 2229779 * 2
def baseEnd_2229779 : Nat := 381649460100578904369313

theorem tailTrace_2229779 : CollatzResearch.WordTrace tailWord_2229779 prefixEnd_2229779 381649460100578904369313 := by
  unfold tailWord_2229779
  simp only [CollatzResearch.WordTrace]
  refine ⟨81326721388898973780004391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54217814259265982520002927 81326721388898973780004391)
  ·
    refine ⟨121990082083348460670006587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81326721388898973780004391 121990082083348460670006587)
    ·
      refine ⟨182985123125022691005009881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121990082083348460670006587 182985123125022691005009881)
      ·
        refine ⟨137238842343767018253757411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182985123125022691005009881 137238842343767018253757411)
        ·
          refine ⟨205858263515650527380636117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137238842343767018253757411 205858263515650527380636117)
          ·
            refine ⟨4824803051148059235483659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 205858263515650527380636117 4824803051148059235483659)
            ·
              refine ⟨7237204576722088853225489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824803051148059235483659 7237204576722088853225489)
              ·
                refine ⟨5427903432541566639919117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237204576722088853225489 5427903432541566639919117)
                ·
                  refine ⟨2035463787203087489969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5427903432541566639919117 2035463787203087489969669)
                  ·
                    refine ⟨381649460100578904369313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2035463787203087489969669 381649460100578904369313)
                    ·
                      rfl

theorem cell23_2229779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 4].length) (baseStart_2229779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229779 prefixEnd_2229779 := by exact prefixLift 2229779
  have htrace : WordTrace (prefixWord ++ tailWord_2229779) baseStart_2229779 baseEnd_2229779 := by
    simpa [prefixWord, tailWord_2229779, baseEnd_2229779] using wordTrace_append hprefix tailTrace_2229779
  have hstable : (prefixWord ++ tailWord_2229779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229779).length < 2 ^ (prefixWord ++ tailWord_2229779).sum := by decide
  have hdescent : baseEnd_2229779 < baseStart_2229779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229789 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2229789 : Nat := 118140960795 + 2229789 * 2 ^ 59
def prefixEnd_2229789 : Nat := 4983230072969 + 3 ^ 40 * 2229789 * 2
def baseEnd_2229789 : Nat := 1144953515108281673982893

theorem tailTrace_2229789 : CollatzResearch.WordTrace tailWord_2229789 prefixEnd_2229789 1144953515108281673982893 := by
  unfold tailWord_2229789
  simp only [CollatzResearch.WordTrace]
  refine ⟨81327086118862745487868421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54218057412575163658578947 81327086118862745487868421)
  ·
    refine ⟨15248828647286764778975329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81327086118862745487868421 15248828647286764778975329)
    ·
      refine ⟨11436621485465073584231497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15248828647286764778975329 11436621485465073584231497)
      ·
        refine ⟨8577466114098805188173623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11436621485465073584231497 8577466114098805188173623)
        ·
          refine ⟨12866199171148207782260435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8577466114098805188173623 12866199171148207782260435)
          ·
            refine ⟨19299298756722311673390653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12866199171148207782260435 19299298756722311673390653)
            ·
              refine ⟨7237237033770866877521495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19299298756722311673390653 7237237033770866877521495)
              ·
                refine ⟨10855855550656300316282243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237237033770866877521495 10855855550656300316282243)
                ·
                  refine ⟨16283783325984450474423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10855855550656300316282243 16283783325984450474423365)
                  ·
                    refine ⟨3053209373622084463954381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16283783325984450474423365 3053209373622084463954381)
                    ·
                      refine ⟨1144953515108281673982893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053209373622084463954381 1144953515108281673982893)
                      ·
                        rfl

theorem cell23_2229789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2229789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229789 prefixEnd_2229789 := by exact prefixLift 2229789
  have htrace : WordTrace (prefixWord ++ tailWord_2229789) baseStart_2229789 baseEnd_2229789 := by
    simpa [prefixWord, tailWord_2229789, baseEnd_2229789] using wordTrace_append hprefix tailTrace_2229789
  have hstable : (prefixWord ++ tailWord_2229789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229789).length < 2 ^ (prefixWord ++ tailWord_2229789).sum := by decide
  have hdescent : baseEnd_2229789 < baseStart_2229789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229829 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_2229829 : Nat := 118140960795 + 2229829 * 2 ^ 59
def prefixEnd_2229829 : Nat := 4983230072969 + 3 ^ 40 * 2229829 * 2
def baseEnd_2229829 : Nat := 1144974054334461517482709

theorem tailTrace_2229829 : CollatzResearch.WordTrace tailWord_2229829 prefixEnd_2229829 1144974054334461517482709 := by
  unfold tailWord_2229829
  simp only [CollatzResearch.WordTrace]
  refine ⟨81328545038717832319324541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54219030025811888212883027 81328545038717832319324541)
  ·
    refine ⟨30498204389519187119746703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81328545038717832319324541 30498204389519187119746703)
    ·
      refine ⟨45747306584278780679620055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30498204389519187119746703 45747306584278780679620055)
      ·
        refine ⟨68620959876418171019430083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45747306584278780679620055 68620959876418171019430083)
        ·
          refine ⟨102931439814627256529145125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68620959876418171019430083 102931439814627256529145125)
          ·
            refine ⟨19299644965242610599214711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102931439814627256529145125 19299644965242610599214711)
            ·
              refine ⟨28949467447863915898822067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19299644965242610599214711 28949467447863915898822067)
              ·
                refine ⟨43424201171795873848233101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28949467447863915898822067 43424201171795873848233101)
                ·
                  refine ⟨16284075439423452693087413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43424201171795873848233101 16284075439423452693087413)
                  ·
                    refine ⟨1526632072445948689976945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16284075439423452693087413 1526632072445948689976945)
                    ·
                      refine ⟨1144974054334461517482709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526632072445948689976945 1144974054334461517482709)
                      ·
                        rfl

theorem cell23_2229829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_2229829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229829 prefixEnd_2229829 := by exact prefixLift 2229829
  have htrace : WordTrace (prefixWord ++ tailWord_2229829) baseStart_2229829 baseEnd_2229829 := by
    simpa [prefixWord, tailWord_2229829, baseEnd_2229829] using wordTrace_append hprefix tailTrace_2229829
  have hstable : (prefixWord ++ tailWord_2229829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229829).length < 2 ^ (prefixWord ++ tailWord_2229829).sum := by decide
  have hdescent : baseEnd_2229829 < baseStart_2229829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229836 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2229836 : Nat := 118140960795 + 2229836 * 2 ^ 59
def prefixEnd_2229836 : Nat := 4983230072969 + 3 ^ 40 * 2229836 * 2
def baseEnd_2229836 : Nat := 1144977648699042990095177

theorem tailTrace_2229836 : CollatzResearch.WordTrace tailWord_2229836 prefixEnd_2229836 1144977648699042990095177 := by
  unfold tailWord_2229836
  simp only [CollatzResearch.WordTrace]
  refine ⟨40664400174846236257414681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54219200233128315009886241 40664400174846236257414681)
  ·
    refine ⟨30498300131134677193061011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40664400174846236257414681 30498300131134677193061011)
    ·
      refine ⟨45747450196702015789591517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30498300131134677193061011 45747450196702015789591517)
      ·
        refine ⟨17155293823763255921096819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45747450196702015789591517 17155293823763255921096819)
        ·
          refine ⟨25732940735644883881645229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17155293823763255921096819 25732940735644883881645229)
          ·
            refine ⟨9649852775866831455616961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25732940735644883881645229 9649852775866831455616961)
            ·
              refine ⟨7237389581900123591712721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9649852775866831455616961 7237389581900123591712721)
              ·
                refine ⟨5428042186425092693784541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237389581900123591712721 5428042186425092693784541)
                ·
                  refine ⟨2035515819909409760169203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5428042186425092693784541 2035515819909409760169203)
                  ·
                    refine ⟨3053273729864114640253805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035515819909409760169203 3053273729864114640253805)
                    ·
                      refine ⟨1144977648699042990095177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053273729864114640253805 1144977648699042990095177)
                      ·
                        rfl

theorem cell23_2229836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2229836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229836 prefixEnd_2229836 := by exact prefixLift 2229836
  have htrace : WordTrace (prefixWord ++ tailWord_2229836) baseStart_2229836 baseEnd_2229836 := by
    simpa [prefixWord, tailWord_2229836, baseEnd_2229836] using wordTrace_append hprefix tailTrace_2229836
  have hstable : (prefixWord ++ tailWord_2229836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229836).length < 2 ^ (prefixWord ++ tailWord_2229836).sum := by decide
  have hdescent : baseEnd_2229836 < baseStart_2229836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229870 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2229870 : Nat := 118140960795 + 2229870 * 2 ^ 59
def prefixEnd_2229870 : Nat := 4983230072969 + 3 ^ 40 * 2229870 * 2
def baseEnd_2229870 : Nat := 1144995107041295857070021

theorem tailTrace_2229870 : CollatzResearch.WordTrace tailWord_2229870 prefixEnd_2229870 1144995107041295857070021 := by
  unfold tailWord_2229870
  simp only [CollatzResearch.WordTrace]
  refine ⟨10166255053946162040195883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54220026954379530881044709 10166255053946162040195883)
  ·
    refine ⟨15249382580919243060293825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10166255053946162040195883 15249382580919243060293825)
    ·
      refine ⟨11437036935689432295220369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15249382580919243060293825 11437036935689432295220369)
      ·
        refine ⟨8577777701767074221415277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11437036935689432295220369 8577777701767074221415277)
        ·
          refine ⟨3216666638162652833030729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8577777701767074221415277 3216666638162652833030729)
          ·
            refine ⟨2412499978621989624773047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3216666638162652833030729 2412499978621989624773047)
            ·
              refine ⟨3618749967932984437159571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412499978621989624773047 3618749967932984437159571)
              ·
                refine ⟨5428124951899476655739357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618749967932984437159571 5428124951899476655739357)
                ·
                  refine ⟨2035546856962303745902259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5428124951899476655739357 2035546856962303745902259)
                  ·
                    refine ⟨3053320285443455618853389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035546856962303745902259 3053320285443455618853389)
                    ·
                      refine ⟨1144995107041295857070021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053320285443455618853389 1144995107041295857070021)
                      ·
                        rfl

theorem cell23_2229870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2229870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229870 prefixEnd_2229870 := by exact prefixLift 2229870
  have htrace : WordTrace (prefixWord ++ tailWord_2229870) baseStart_2229870 baseEnd_2229870 := by
    simpa [prefixWord, tailWord_2229870, baseEnd_2229870] using wordTrace_append hprefix tailTrace_2229870
  have hstable : (prefixWord ++ tailWord_2229870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229870).length < 2 ^ (prefixWord ++ tailWord_2229870).sum := by decide
  have hdescent : baseEnd_2229870 < baseStart_2229870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229879 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_2229879 : Nat := 118140960795 + 2229879 * 2 ^ 59
def prefixEnd_2229879 : Nat := 4983230072969 + 3 ^ 40 * 2229879 * 2
def baseEnd_2229879 : Nat := 1144999728367186321857479

theorem tailTrace_2229879 : CollatzResearch.WordTrace tailWord_2229879 prefixEnd_2229879 1144999728367186321857479 := by
  unfold tailWord_2229879
  simp only [CollatzResearch.WordTrace]
  refine ⟨81330368688536690858644691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54220245792357793905763127 81330368688536690858644691)
  ·
    refine ⟨121995553032805036287967037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81330368688536690858644691 121995553032805036287967037)
    ·
      refine ⟨45748332387301888607987639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121995553032805036287967037 45748332387301888607987639)
      ·
        refine ⟨68622498580952832911981459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45748332387301888607987639 68622498580952832911981459)
        ·
          refine ⟨102933747871429249367972189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68622498580952832911981459 102933747871429249367972189)
          ·
            refine ⟨38600155451785968512989571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102933747871429249367972189 38600155451785968512989571)
            ·
              refine ⟨57900233177678952769484357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38600155451785968512989571 57900233177678952769484357)
              ·
                refine ⟨10856293720814803644278317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57900233177678952769484357 10856293720814803644278317)
                ·
                  refine ⟨4071110145305551366604369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10856293720814803644278317 4071110145305551366604369)
                  ·
                    refine ⟨3053332608979163524953277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071110145305551366604369 3053332608979163524953277)
                    ·
                      refine ⟨1144999728367186321857479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053332608979163524953277 1144999728367186321857479)
                      ·
                        rfl

theorem cell23_2229879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_2229879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229879 prefixEnd_2229879 := by exact prefixLift 2229879
  have htrace : WordTrace (prefixWord ++ tailWord_2229879) baseStart_2229879 baseEnd_2229879 := by
    simpa [prefixWord, tailWord_2229879, baseEnd_2229879] using wordTrace_append hprefix tailTrace_2229879
  have hstable : (prefixWord ++ tailWord_2229879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229879).length < 2 ^ (prefixWord ++ tailWord_2229879).sum := by decide
  have hdescent : baseEnd_2229879 < baseStart_2229879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229889 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2229889 : Nat := 118140960795 + 2229889 * 2 ^ 59
def prefixEnd_2229889 : Nat := 4983230072969 + 3 ^ 40 * 2229889 * 2
def baseEnd_2229889 : Nat := 1145004863173731282732433

theorem tailTrace_2229889 : CollatzResearch.WordTrace tailWord_2229889 prefixEnd_2229889 1145004863173731282732433 := by
  unfold tailWord_2229889
  simp only [CollatzResearch.WordTrace]
  refine ⟨81330733418500462566508721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54220488945666975044339147 81330733418500462566508721)
  ·
    refine ⟨60998050063875346924881541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81330733418500462566508721 60998050063875346924881541)
    ·
      refine ⟨11437134386976627548415289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60998050063875346924881541 11437134386976627548415289)
      ·
        refine ⟨8577850790232470661311467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11437134386976627548415289 8577850790232470661311467)
        ·
          refine ⟨12866776185348705991967201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8577850790232470661311467 12866776185348705991967201)
          ·
            refine ⟨9650082139011529493975401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12866776185348705991967201 9650082139011529493975401)
            ·
              refine ⟨7237561604258647120481551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650082139011529493975401 7237561604258647120481551)
              ·
                refine ⟨10856342406387970680722327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237561604258647120481551 10856342406387970680722327)
                ·
                  refine ⟨16284513609581956021083491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10856342406387970680722327 16284513609581956021083491)
                  ·
                    refine ⟨24426770414372934031625237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16284513609581956021083491 24426770414372934031625237)
                    ·
                      refine ⟨1145004863173731282732433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24426770414372934031625237 1145004863173731282732433)
                      ·
                        rfl

theorem cell23_2229889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2229889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229889 prefixEnd_2229889 := by exact prefixLift 2229889
  have htrace : WordTrace (prefixWord ++ tailWord_2229889) baseStart_2229889 baseEnd_2229889 := by
    simpa [prefixWord, tailWord_2229889, baseEnd_2229889] using wordTrace_append hprefix tailTrace_2229889
  have hstable : (prefixWord ++ tailWord_2229889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229889).length < 2 ^ (prefixWord ++ tailWord_2229889).sum := by decide
  have hdescent : baseEnd_2229889 < baseStart_2229889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229936 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2]
def baseStart_2229936 : Nat := 118140960795 + 2229936 * 2 ^ 59
def prefixEnd_2229936 : Nat := 4983230072969 + 3 ^ 40 * 2229936 * 2
def baseEnd_2229936 : Nat := 1145028996764492598844717

theorem tailTrace_2229936 : CollatzResearch.WordTrace tailWord_2229936 prefixEnd_2229936 1145028996764492598844717 := by
  unfold tailWord_2229936
  simp only [CollatzResearch.WordTrace]
  refine ⟨40666223824665094796734831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54221631766220126395646441 40666223824665094796734831)
  ·
    refine ⟨60999335736997642195102247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40666223824665094796734831 60999335736997642195102247)
    ·
      refine ⟨91499003605496463292653371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60999335736997642195102247 91499003605496463292653371)
      ·
        refine ⟨137248505408244694938980057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91499003605496463292653371 137248505408244694938980057)
        ·
          refine ⟨102936379056183521204235043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137248505408244694938980057 102936379056183521204235043)
          ·
            refine ⟨154404568584275281806352565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102936379056183521204235043 154404568584275281806352565)
            ·
              refine ⟨14475428304775807669345553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154404568584275281806352565 14475428304775807669345553)
              ·
                refine ⟨10856571228581855752009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14475428304775807669345553 10856571228581855752009165)
                ·
                  refine ⟨4071214210718195907003437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10856571228581855752009165 4071214210718195907003437)
                  ·
                    refine ⟨1526705329019323465126289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4071214210718195907003437 1526705329019323465126289)
                    ·
                      refine ⟨1145028996764492598844717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526705329019323465126289 1145028996764492598844717)
                      ·
                        rfl

theorem cell23_2229936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2].length) (baseStart_2229936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229936 prefixEnd_2229936 := by exact prefixLift 2229936
  have htrace : WordTrace (prefixWord ++ tailWord_2229936) baseStart_2229936 baseEnd_2229936 := by
    simpa [prefixWord, tailWord_2229936, baseEnd_2229936] using wordTrace_append hprefix tailTrace_2229936
  have hstable : (prefixWord ++ tailWord_2229936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229936).length < 2 ^ (prefixWord ++ tailWord_2229936).sum := by decide
  have hdescent : baseEnd_2229936 < baseStart_2229936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229943 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_2229943 : Nat := 118140960795 + 2229943 * 2 ^ 59
def prefixEnd_2229943 : Nat := 4983230072969 + 3 ^ 40 * 2229943 * 2
def baseEnd_2229943 : Nat := 1145032591129074071457185

theorem tailTrace_2229943 : CollatzResearch.WordTrace tailWord_2229943 prefixEnd_2229943 1145032591129074071457185 := by
  unfold tailWord_2229943
  simp only [CollatzResearch.WordTrace]
  refine ⟨81332702960304829788974483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54221801973536553192649655 81332702960304829788974483)
  ·
    refine ⟨121999054440457244683461725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81332702960304829788974483 121999054440457244683461725)
    ·
      refine ⟨45749645415171466756298147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121999054440457244683461725 45749645415171466756298147)
      ·
        refine ⟨68624468122757200134447221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45749645415171466756298147 68624468122757200134447221)
        ·
          refine ⟨6433543886508487512604427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68624468122757200134447221 6433543886508487512604427)
          ·
            refine ⟨9650315829762731268906641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6433543886508487512604427 9650315829762731268906641)
            ·
              refine ⟨7237736872322048451679981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650315829762731268906641 7237736872322048451679981)
              ·
                refine ⟨2714151327120768169379993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7237736872322048451679981 2714151327120768169379993)
                ·
                  refine ⟨2035613495340576127034995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2714151327120768169379993 2035613495340576127034995)
                  ·
                    refine ⟨3053420243010864190552493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2035613495340576127034995 3053420243010864190552493)
                    ·
                      refine ⟨1145032591129074071457185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053420243010864190552493 1145032591129074071457185)
                      ·
                        rfl

theorem cell23_2229943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_2229943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229943 prefixEnd_2229943 := by exact prefixLift 2229943
  have htrace : WordTrace (prefixWord ++ tailWord_2229943) baseStart_2229943 baseEnd_2229943 := by
    simpa [prefixWord, tailWord_2229943, baseEnd_2229943] using wordTrace_append hprefix tailTrace_2229943
  have hstable : (prefixWord ++ tailWord_2229943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229943).length < 2 ^ (prefixWord ++ tailWord_2229943).sum := by decide
  have hdescent : baseEnd_2229943 < baseStart_2229943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229949 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2229949 : Nat := 118140960795 + 2229949 * 2 ^ 59
def prefixEnd_2229949 : Nat := 4983230072969 + 3 ^ 40 * 2229949 * 2
def baseEnd_2229949 : Nat := 1145035672013001047982157

theorem tailTrace_2229949 : CollatzResearch.WordTrace tailWord_2229949 prefixEnd_2229949 1145035672013001047982157 := by
  unfold tailWord_2229949
  simp only [CollatzResearch.WordTrace]
  refine ⟨81332921798283092813692901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54221947865522061875795267 81332921798283092813692901)
  ·
    refine ⟨15249922837178079902567419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81332921798283092813692901 15249922837178079902567419)
    ·
      refine ⟨22874884255767119853851129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249922837178079902567419 22874884255767119853851129)
      ·
        refine ⟨17156163191825339890388347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22874884255767119853851129 17156163191825339890388347)
        ·
          refine ⟨25734244787738009835582521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17156163191825339890388347 25734244787738009835582521)
          ·
            refine ⟨19300683590803507376686891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25734244787738009835582521 19300683590803507376686891)
            ·
              refine ⟨28951025386205261065030337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19300683590803507376686891 28951025386205261065030337)
              ·
                refine ⟨21713269039653945798772753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28951025386205261065030337 21713269039653945798772753)
                ·
                  refine ⟨16284951779740459349079565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21713269039653945798772753 16284951779740459349079565)
                  ·
                    refine ⟨6106856917402672255904837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16284951779740459349079565 6106856917402672255904837)
                    ·
                      refine ⟨1145035672013001047982157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6106856917402672255904837 1145035672013001047982157)
                      ·
                        rfl

theorem cell23_2229949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2229949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229949 prefixEnd_2229949 := by exact prefixLift 2229949
  have htrace : WordTrace (prefixWord ++ tailWord_2229949) baseStart_2229949 baseEnd_2229949 := by
    simpa [prefixWord, tailWord_2229949, baseEnd_2229949] using wordTrace_append hprefix tailTrace_2229949
  have hstable : (prefixWord ++ tailWord_2229949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229949).length < 2 ^ (prefixWord ++ tailWord_2229949).sum := by decide
  have hdescent : baseEnd_2229949 < baseStart_2229949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229970 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2229970 : Nat := 118140960795 + 2229970 * 2 ^ 59
def prefixEnd_2229970 : Nat := 4983230072969 + 3 ^ 40 * 2229970 * 2
def baseEnd_2229970 : Nat := 1145046455106745465819561

theorem tailTrace_2229970 : CollatzResearch.WordTrace tailWord_2229970 prefixEnd_2229970 1145046455106745465819561 := by
  unfold tailWord_2229970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20333421932801753350051841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54222458487471342266804909 20333421932801753350051841)
  ·
    refine ⟨15250066449601315012538881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20333421932801753350051841 15250066449601315012538881)
    ·
      refine ⟨11437549837200986259404161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15250066449601315012538881 11437549837200986259404161)
      ·
        refine ⟨8578162377900739694553121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11437549837200986259404161 8578162377900739694553121)
        ·
          refine ⟨6433621783425554770914841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8578162377900739694553121 6433621783425554770914841)
          ·
            refine ⟨4825216337569166078186131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433621783425554770914841 4825216337569166078186131)
            ·
              refine ⟨7237824506353749117279197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825216337569166078186131 7237824506353749117279197)
              ·
                refine ⟨2714184189882655918979699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7237824506353749117279197 2714184189882655918979699)
                ·
                  refine ⟨4071276284823983878469549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714184189882655918979699 4071276284823983878469549)
                  ·
                    refine ⟨1526728606808993954426081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4071276284823983878469549 1526728606808993954426081)
                    ·
                      refine ⟨1145046455106745465819561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526728606808993954426081 1145046455106745465819561)
                      ·
                        rfl

theorem cell23_2229970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2229970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229970 prefixEnd_2229970 := by exact prefixLift 2229970
  have htrace : WordTrace (prefixWord ++ tailWord_2229970) baseStart_2229970 baseEnd_2229970 := by
    simpa [prefixWord, tailWord_2229970, baseEnd_2229970] using wordTrace_append hprefix tailTrace_2229970
  have hstable : (prefixWord ++ tailWord_2229970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229970).length < 2 ^ (prefixWord ++ tailWord_2229970).sum := by decide
  have hdescent : baseEnd_2229970 < baseStart_2229970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229983 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 4, 2, 2]
def baseStart_2229983 : Nat := 118140960795 + 2229983 * 2 ^ 59
def prefixEnd_2229983 : Nat := 4983230072969 + 3 ^ 40 * 2229983 * 2
def baseEnd_2229983 : Nat := 1145053130355253914957001

theorem tailTrace_2229983 : CollatzResearch.WordTrace tailWord_2229983 prefixEnd_2229983 1145053130355253914957001 := by
  unfold tailWord_2229983
  simp only [CollatzResearch.WordTrace]
  refine ⟨81334161880159916620430603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54222774586773277746953735 81334161880159916620430603)
  ·
    refine ⟨122001242820239874930645905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81334161880159916620430603 122001242820239874930645905)
    ·
      refine ⟨91500932115179906197984429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122001242820239874930645905 91500932115179906197984429)
      ·
        refine ⟨34312849543192464824244161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91500932115179906197984429 34312849543192464824244161)
        ·
          refine ⟨25734637157394348618183121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34312849543192464824244161 25734637157394348618183121)
          ·
            refine ⟨19300977868045761463637341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25734637157394348618183121 19300977868045761463637341)
            ·
              refine ⟨7237866700517160548864003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19300977868045761463637341 7237866700517160548864003)
              ·
                refine ⟨10856800050775740823296005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237866700517160548864003 10856800050775740823296005)
                ·
                  refine ⟨2035650009520451404368001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10856800050775740823296005 2035650009520451404368001)
                  ·
                    refine ⟨1526737507140338553276001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2035650009520451404368001 1526737507140338553276001)
                    ·
                      refine ⟨1145053130355253914957001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526737507140338553276001 1145053130355253914957001)
                      ·
                        rfl

theorem cell23_2229983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_2229983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2229983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2229983 prefixEnd_2229983 := by exact prefixLift 2229983
  have htrace : WordTrace (prefixWord ++ tailWord_2229983) baseStart_2229983 baseEnd_2229983 := by
    simpa [prefixWord, tailWord_2229983, baseEnd_2229983] using wordTrace_append hprefix tailTrace_2229983
  have hstable : (prefixWord ++ tailWord_2229983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229983).length < 2 ^ (prefixWord ++ tailWord_2229983).sum := by decide
  have hdescent : baseEnd_2229983 < baseStart_2229983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230004 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2230004 : Nat := 118140960795 + 2230004 * 2 ^ 59
def prefixEnd_2230004 : Nat := 4983230072969 + 3 ^ 40 * 2230004 * 2
def baseEnd_2230004 : Nat := 1145063913448998332794405

theorem tailTrace_2230004 : CollatzResearch.WordTrace tailWord_2230004 prefixEnd_2230004 1145063913448998332794405 := by
  unfold tailWord_2230004
  simp only [CollatzResearch.WordTrace]
  refine ⟨40667463906541918603472533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54223285208722558137963377 40667463906541918603472533)
  ·
    refine ⟨1906287370619152434537775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40667463906541918603472533 1906287370619152434537775)
    ·
      refine ⟨2859431055928728651806663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906287370619152434537775 2859431055928728651806663)
      ·
        refine ⟨4289146583893092977709995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859431055928728651806663 4289146583893092977709995)
        ·
          refine ⟨6433719875839639466564993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4289146583893092977709995 6433719875839639466564993)
          ·
            refine ⟨4825289906879729599923745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433719875839639466564993 4825289906879729599923745)
            ·
              refine ⟨3618967430159797199942809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825289906879729599923745 3618967430159797199942809)
              ·
                refine ⟨2714225572619847899957107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618967430159797199942809 2714225572619847899957107)
                ·
                  refine ⟨4071338358929771849935661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714225572619847899957107 4071338358929771849935661)
                  ·
                    refine ⟨1526751884598664443725873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4071338358929771849935661 1526751884598664443725873)
                    ·
                      refine ⟨1145063913448998332794405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526751884598664443725873 1145063913448998332794405)
                      ·
                        rfl

theorem cell23_2230004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2230004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230004 prefixEnd_2230004 := by exact prefixLift 2230004
  have htrace : WordTrace (prefixWord ++ tailWord_2230004) baseStart_2230004 baseEnd_2230004 := by
    simpa [prefixWord, tailWord_2230004, baseEnd_2230004] using wordTrace_append hprefix tailTrace_2230004
  have hstable : (prefixWord ++ tailWord_2230004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230004).length < 2 ^ (prefixWord ++ tailWord_2230004).sum := by decide
  have hdescent : baseEnd_2230004 < baseStart_2230004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230006 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2230006 : Nat := 118140960795 + 2230006 * 2 ^ 59
def prefixEnd_2230006 : Nat := 4983230072969 + 3 ^ 40 * 2230006 * 2
def baseEnd_2230006 : Nat := 127229437823367480552155

theorem tailTrace_2230006 : CollatzResearch.WordTrace tailWord_2230006 prefixEnd_2230006 127229437823367480552155 := by
  unfold tailWord_2230006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083437547442286971782367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54223333839384394365678581 5083437547442286971782367)
  ·
    refine ⟨7625156321163430457673551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083437547442286971782367 7625156321163430457673551)
    ·
      refine ⟨11437734481745145686510327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625156321163430457673551 11437734481745145686510327)
      ·
        refine ⟨17156601722617718529765491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437734481745145686510327 17156601722617718529765491)
        ·
          refine ⟨25734902583926577794648237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17156601722617718529765491 25734902583926577794648237)
          ·
            refine ⟨9650588468972466672993089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25734902583926577794648237 9650588468972466672993089)
            ·
              refine ⟨7237941351729350004744817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650588468972466672993089 7237941351729350004744817)
              ·
                refine ⟨5428456013797012503558613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237941351729350004744817 5428456013797012503558613)
                ·
                  refine ⟨127229437823367480552155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5428456013797012503558613 127229437823367480552155)
                  ·
                    rfl

theorem cell23_2230006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2230006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230006 prefixEnd_2230006 := by exact prefixLift 2230006
  have htrace : WordTrace (prefixWord ++ tailWord_2230006) baseStart_2230006 baseEnd_2230006 := by
    simpa [prefixWord, tailWord_2230006, baseEnd_2230006] using wordTrace_append hprefix tailTrace_2230006
  have hstable : (prefixWord ++ tailWord_2230006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230006).length < 2 ^ (prefixWord ++ tailWord_2230006).sum := by decide
  have hdescent : baseEnd_2230006 < baseStart_2230006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230019 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 7]
def baseStart_2230019 : Nat := 118140960795 + 2230019 * 2 ^ 59
def prefixEnd_2230019 : Nat := 4983230072969 + 3 ^ 40 * 2230019 * 2
def baseEnd_2230019 : Nat := 381690538552938591368945

theorem tailTrace_2230019 : CollatzResearch.WordTrace tailWord_2230019 prefixEnd_2230019 381690538552938591368945 := by
  unfold tailWord_2230019
  simp only [CollatzResearch.WordTrace]
  refine ⟨81335474908029494768741111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54223649938686329845827407 81335474908029494768741111)
  ·
    refine ⟨122003212362044242153111667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81335474908029494768741111 122003212362044242153111667)
    ·
      refine ⟨183004818543066363229667501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122003212362044242153111667 183004818543066363229667501)
      ·
        refine ⟨68626806953649886211125313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183004818543066363229667501 68626806953649886211125313)
        ·
          refine ⟨51470105215237414658343985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68626806953649886211125313 51470105215237414658343985)
          ·
            refine ⟨38602578911428060993757989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51470105215237414658343985 38602578911428060993757989)
            ·
              refine ⟨7237983545892761436329623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38602578911428060993757989 7237983545892761436329623)
              ·
                refine ⟨10856975318839142154494435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237983545892761436329623 10856975318839142154494435)
                ·
                  refine ⟨16285462978258713231741653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10856975318839142154494435 16285462978258713231741653)
                  ·
                    refine ⟨381690538552938591368945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16285462978258713231741653 381690538552938591368945)
                    ·
                      rfl

theorem cell23_2230019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_2230019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230019 prefixEnd_2230019 := by exact prefixLift 2230019
  have htrace : WordTrace (prefixWord ++ tailWord_2230019) baseStart_2230019 baseEnd_2230019 := by
    simpa [prefixWord, tailWord_2230019, baseEnd_2230019] using wordTrace_append hprefix tailTrace_2230019
  have hstable : (prefixWord ++ tailWord_2230019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230019).length < 2 ^ (prefixWord ++ tailWord_2230019).sum := by decide
  have hdescent : baseEnd_2230019 < baseStart_2230019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230070 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2230070 : Nat := 118140960795 + 2230070 * 2 ^ 59
def prefixEnd_2230070 : Nat := 4983230072969 + 3 ^ 40 * 2230070 * 2
def baseEnd_2230070 : Nat := 381699267724065024856367

theorem tailTrace_2230070 : CollatzResearch.WordTrace tailWord_2230070 prefixEnd_2230070 381699267724065024856367 := by
  unfold tailWord_2230070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083583439427795654927979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54224890020563153652565109 5083583439427795654927979)
  ·
    refine ⟨7625375159141693482391969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083583439427795654927979 7625375159141693482391969)
    ·
      refine ⟨5719031369356270111793977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7625375159141693482391969 5719031369356270111793977)
      ·
        refine ⟨4289273527017202583845483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5719031369356270111793977 4289273527017202583845483)
        ·
          refine ⟨6433910290525803875768225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4289273527017202583845483 6433910290525803875768225)
          ·
            refine ⟨4825432717894352906826169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433910290525803875768225 4825432717894352906826169)
            ·
              refine ⟨3619074538420764680119627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825432717894352906826169 3619074538420764680119627)
              ·
                refine ⟨5428611807631147020179441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619074538420764680119627 5428611807631147020179441)
                ·
                  refine ⟨4071458855723360265134581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428611807631147020179441 4071458855723360265134581)
                  ·
                    refine ⟨381699267724065024856367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4071458855723360265134581 381699267724065024856367)
                    ·
                      rfl

theorem cell23_2230070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2230070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230070 prefixEnd_2230070 := by exact prefixLift 2230070
  have htrace : WordTrace (prefixWord ++ tailWord_2230070) baseStart_2230070 baseEnd_2230070 := by
    simpa [prefixWord, tailWord_2230070, baseEnd_2230070] using wordTrace_append hprefix tailTrace_2230070
  have hstable : (prefixWord ++ tailWord_2230070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230070).length < 2 ^ (prefixWord ++ tailWord_2230070).sum := by decide
  have hdescent : baseEnd_2230070 < baseStart_2230070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230076 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_2230076 : Nat := 118140960795 + 2230076 * 2 ^ 59
def prefixEnd_2230076 : Nat := 4983230072969 + 3 ^ 40 * 2230076 * 2
def baseEnd_2230076 : Nat := 1145100884056122051094073

theorem tailTrace_2230076 : CollatzResearch.WordTrace tailWord_2230076 prefixEnd_2230076 1145100884056122051094073 := by
  unfold tailWord_2230076
  simp only [CollatzResearch.WordTrace]
  refine ⟨40668776934411496751783041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54225035912548662335710721 40668776934411496751783041)
  ·
    refine ⟨30501582700808622563837281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40668776934411496751783041 30501582700808622563837281)
    ·
      refine ⟨22876187025606466922877961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30501582700808622563837281 22876187025606466922877961)
      ·
        refine ⟨17157140269204850192158471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22876187025606466922877961 17157140269204850192158471)
        ·
          refine ⟨25735710403807275288237707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17157140269204850192158471 25735710403807275288237707)
          ·
            refine ⟨38603565605710912932356561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25735710403807275288237707 38603565605710912932356561)
            ·
              refine ⟨28952674204283184699267421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38603565605710912932356561 28952674204283184699267421)
              ·
                refine ⟨10857252826606194262225283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28952674204283184699267421 10857252826606194262225283)
                ·
                  refine ⟨16285879239909291393337925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10857252826606194262225283 16285879239909291393337925)
                  ·
                    refine ⟨3053602357482992136250861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16285879239909291393337925 3053602357482992136250861)
                    ·
                      refine ⟨1145100884056122051094073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053602357482992136250861 1145100884056122051094073)
                      ·
                        rfl

theorem cell23_2230076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_2230076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230076 prefixEnd_2230076 := by exact prefixLift 2230076
  have htrace : WordTrace (prefixWord ++ tailWord_2230076) baseStart_2230076 baseEnd_2230076 := by
    simpa [prefixWord, tailWord_2230076, baseEnd_2230076] using wordTrace_append hprefix tailTrace_2230076
  have hstable : (prefixWord ++ tailWord_2230076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230076).length < 2 ^ (prefixWord ++ tailWord_2230076).sum := by decide
  have hdescent : baseEnd_2230076 < baseStart_2230076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230134 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2230134 : Nat := 118140960795 + 2230134 * 2 ^ 59
def prefixEnd_2230134 : Nat := 4983230072969 + 3 ^ 40 * 2230134 * 2
def baseEnd_2230134 : Nat := 381710221978027608056269

theorem tailTrace_2230134 : CollatzResearch.WordTrace tailWord_2230134 prefixEnd_2230134 381710221978027608056269 := by
  unfold tailWord_2230134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083729331413304338073591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54226446201741912939451637 5083729331413304338073591)
  ·
    refine ⟨7625593997119956507110387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083729331413304338073591 7625593997119956507110387)
    ·
      refine ⟨11438390995679934760665581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625593997119956507110387 11438390995679934760665581)
      ·
        refine ⟨4289396623379975535249593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11438390995679934760665581 4289396623379975535249593)
        ·
          refine ⟨3217047467534981651437195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4289396623379975535249593 3217047467534981651437195)
          ·
            refine ⟨4825571201302472477155793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217047467534981651437195 4825571201302472477155793)
            ·
              refine ⟨3619178400976854357866845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825571201302472477155793 3619178400976854357866845)
              ·
                refine ⟨1357191900366320384200067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619178400976854357866845 1357191900366320384200067)
                ·
                  refine ⟨2035787850549480576300101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357191900366320384200067 2035787850549480576300101)
                  ·
                    refine ⟨381710221978027608056269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2035787850549480576300101 381710221978027608056269)
                    ·
                      rfl

theorem cell23_2230134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2230134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230134 prefixEnd_2230134 := by exact prefixLift 2230134
  have htrace : WordTrace (prefixWord ++ tailWord_2230134) baseStart_2230134 baseEnd_2230134 := by
    simpa [prefixWord, tailWord_2230134, baseEnd_2230134] using wordTrace_append hprefix tailTrace_2230134
  have hstable : (prefixWord ++ tailWord_2230134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230134).length < 2 ^ (prefixWord ++ tailWord_2230134).sum := by decide
  have hdescent : baseEnd_2230134 < baseStart_2230134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230173 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2230173 : Nat := 118140960795 + 2230173 * 2 ^ 59
def prefixEnd_2230173 : Nat := 4983230072969 + 3 ^ 40 * 2230173 * 2
def baseEnd_2230173 : Nat := 381716897226536057193709

theorem tailTrace_2230173 : CollatzResearch.WordTrace tailWord_2230173 prefixEnd_2230173 381716897226536057193709 := by
  unfold tailWord_2230173
  simp only [CollatzResearch.WordTrace]
  refine ⟨81341091749471579069847173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54227394499647719379898115 81341091749471579069847173)
  ·
    refine ⟨15251454703025921075596345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81341091749471579069847173 15251454703025921075596345)
    ·
      refine ⟨11438591027269440806697259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15251454703025921075596345 11438591027269440806697259)
      ·
        refine ⟨17157886540904161210045889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11438591027269440806697259 17157886540904161210045889)
        ·
          refine ⟨12868414905678120907534417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17157886540904161210045889 12868414905678120907534417)
          ·
            refine ⟨9651311179258590680650813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12868414905678120907534417 9651311179258590680650813)
            ·
              refine ⟨3619241692221971505244055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9651311179258590680650813 3619241692221971505244055)
              ·
                refine ⟨5428862538332957257866083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619241692221971505244055 5428862538332957257866083)
                ·
                  refine ⟨8143293807499435886799125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5428862538332957257866083 8143293807499435886799125)
                  ·
                    refine ⟨381716897226536057193709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8143293807499435886799125 381716897226536057193709)
                    ·
                      rfl

theorem cell23_2230173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2230173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230173 prefixEnd_2230173 := by exact prefixLift 2230173
  have htrace : WordTrace (prefixWord ++ tailWord_2230173) baseStart_2230173 baseEnd_2230173 := by
    simpa [prefixWord, tailWord_2230173, baseEnd_2230173] using wordTrace_append hprefix tailTrace_2230173
  have hstable : (prefixWord ++ tailWord_2230173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230173).length < 2 ^ (prefixWord ++ tailWord_2230173).sum := by decide
  have hdescent : baseEnd_2230173 < baseStart_2230173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230180 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_2230180 : Nat := 118140960795 + 2230180 * 2 ^ 59
def prefixEnd_2230180 : Nat := 4983230072969 + 3 ^ 40 * 2230180 * 2
def baseEnd_2230180 : Nat := 1145154286044189644193595

theorem tailTrace_2230180 : CollatzResearch.WordTrace tailWord_2230180 prefixEnd_2230180 1145154286044189644193595 := by
  unfold tailWord_2230180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40670673530223109632675997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54227564706964146176901329 40670673530223109632675997)
  ·
    refine ⟨15251502573833666112253499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40670673530223109632675997 15251502573833666112253499)
    ·
      refine ⟨22877253860750499168380249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15251502573833666112253499 22877253860750499168380249)
      ·
        refine ⟨17157940395562874376285187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22877253860750499168380249 17157940395562874376285187)
        ·
          refine ⟨25736910593344311564427781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17157940395562874376285187 25736910593344311564427781)
          ·
            refine ⟨4825670736252058418330209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25736910593344311564427781 4825670736252058418330209)
            ·
              refine ⟨3619253052189043813747657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825670736252058418330209 3619253052189043813747657)
              ·
                refine ⟨2714439789141782860310743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619253052189043813747657 2714439789141782860310743)
                ·
                  refine ⟨4071659683712674290466115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714439789141782860310743 4071659683712674290466115)
                  ·
                    refine ⟨6107489525569011435699173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4071659683712674290466115 6107489525569011435699173)
                    ·
                      refine ⟨1145154286044189644193595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6107489525569011435699173 1145154286044189644193595)
                      ·
                        rfl

theorem cell23_2230180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_2230180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230180 prefixEnd_2230180 := by exact prefixLift 2230180
  have htrace : WordTrace (prefixWord ++ tailWord_2230180) baseStart_2230180 baseEnd_2230180 := by
    simpa [prefixWord, tailWord_2230180, baseEnd_2230180] using wordTrace_append hprefix tailTrace_2230180
  have hstable : (prefixWord ++ tailWord_2230180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230180).length < 2 ^ (prefixWord ++ tailWord_2230180).sum := by decide
  have hdescent : baseEnd_2230180 < baseStart_2230180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230234 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_2230234 : Nat := 118140960795 + 2230234 * 2 ^ 59
def prefixEnd_2230234 : Nat := 4983230072969 + 3 ^ 40 * 2230234 * 2
def baseEnd_2230234 : Nat := 1145182013999532432918347

theorem tailTrace_2230234 : CollatzResearch.WordTrace tailWord_2230234 prefixEnd_2230234 1145182013999532432918347 := by
  unfold tailWord_2230234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20335829150562646621954439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54228877734833724325211837 20335829150562646621954439)
  ·
    refine ⟨30503743725843969932931659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20335829150562646621954439 30503743725843969932931659)
    ·
      refine ⟨45755615588765954899397489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30503743725843969932931659 45755615588765954899397489)
      ·
        refine ⟨34316711691574466174548117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45755615588765954899397489 34316711691574466174548117)
        ·
          refine ⟨1608595860542553101931943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34316711691574466174548117 1608595860542553101931943)
          ·
            refine ⟨2412893790813829652897915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608595860542553101931943 2412893790813829652897915)
            ·
              refine ⟨3619340686220744479346873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412893790813829652897915 3619340686220744479346873)
              ·
                refine ⟨2714505514665558359510155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619340686220744479346873 2714505514665558359510155)
                ·
                  refine ⟨4071758271998337539265233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714505514665558359510155 4071758271998337539265233)
                  ·
                    refine ⟨3053818703998753154448925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071758271998337539265233 3053818703998753154448925)
                    ·
                      refine ⟨1145182013999532432918347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053818703998753154448925 1145182013999532432918347)
                      ·
                        rfl

theorem cell23_2230234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_2230234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230234 prefixEnd_2230234 := by exact prefixLift 2230234
  have htrace : WordTrace (prefixWord ++ tailWord_2230234) baseStart_2230234 baseEnd_2230234 := by
    simpa [prefixWord, tailWord_2230234, baseEnd_2230234] using wordTrace_append hprefix tailTrace_2230234
  have hstable : (prefixWord ++ tailWord_2230234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230234).length < 2 ^ (prefixWord ++ tailWord_2230234).sum := by decide
  have hdescent : baseEnd_2230234 < baseStart_2230234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230266 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_2230266 : Nat := 118140960795 + 2230266 * 2 ^ 59
def prefixEnd_2230266 : Nat := 4983230072969 + 3 ^ 40 * 2230266 * 2
def baseEnd_2230266 : Nat := 1145198445380476307718199

theorem tailTrace_2230266 : CollatzResearch.WordTrace tailWord_2230266 prefixEnd_2230266 1145198445380476307718199 := by
  unfold tailWord_2230266
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336120934533663988245663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54229655825423103968655101 20336120934533663988245663)
  ·
    refine ⟨30504181401800495982368495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336120934533663988245663 30504181401800495982368495)
    ·
      refine ⟨45756272102700743973552743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30504181401800495982368495 45756272102700743973552743)
      ·
        refine ⟨68634408154051115960329115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45756272102700743973552743 68634408154051115960329115)
        ·
          refine ⟨102951612231076673940493673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68634408154051115960329115 102951612231076673940493673)
          ·
            refine ⟨77213709173307505455370255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102951612231076673940493673 77213709173307505455370255)
            ·
              refine ⟨115820563759961258183055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77213709173307505455370255 115820563759961258183055383)
              ·
                refine ⟨173730845639941887274583075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115820563759961258183055383 173730845639941887274583075)
                ·
                  refine ⟨260596268459912830911874613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173730845639941887274583075 260596268459912830911874613)
                  ·
                    refine ⟨24430900168116827897988245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 260596268459912830911874613 24430900168116827897988245)
                    ·
                      refine ⟨1145198445380476307718199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24430900168116827897988245 1145198445380476307718199)
                      ·
                        rfl

theorem cell23_2230266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_2230266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230266 prefixEnd_2230266 := by exact prefixLift 2230266
  have htrace : WordTrace (prefixWord ++ tailWord_2230266) baseStart_2230266 baseEnd_2230266 := by
    simpa [prefixWord, tailWord_2230266, baseEnd_2230266] using wordTrace_append hprefix tailTrace_2230266
  have hstable : (prefixWord ++ tailWord_2230266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230266).length < 2 ^ (prefixWord ++ tailWord_2230266).sum := by decide
  have hdescent : baseEnd_2230266 < baseStart_2230266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230270 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2230270 : Nat := 118140960795 + 2230270 * 2 ^ 59
def prefixEnd_2230270 : Nat := 4983230072969 + 3 ^ 40 * 2230270 * 2
def baseEnd_2230270 : Nat := 1145200499303094292068181

theorem tailTrace_2230270 : CollatzResearch.WordTrace tailWord_2230270 prefixEnd_2230270 1145200499303094292068181 := by
  unfold tailWord_2230270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168078703765020579516033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54229753086746776424085509 10168078703765020579516033)
  ·
    refine ⟨7626059027823765434637025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10168078703765020579516033 7626059027823765434637025)
    ·
      refine ⟨5719544270867824075977769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7626059027823765434637025 5719544270867824075977769)
      ·
        refine ⟨4289658203150868056983327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5719544270867824075977769 4289658203150868056983327)
        ·
          refine ⟨6434487304726302085474991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4289658203150868056983327 6434487304726302085474991)
          ·
            refine ⟨9651730957089453128212487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434487304726302085474991 9651730957089453128212487)
            ·
              refine ⟨14477596435634179692318731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9651730957089453128212487 14477596435634179692318731)
              ·
                refine ⟨21716394653451269538478097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14477596435634179692318731 21716394653451269538478097)
                ·
                  refine ⟨16287295990088452153858573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21716394653451269538478097 16287295990088452153858573)
                  ·
                    refine ⟨6107735996283169557696965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16287295990088452153858573 6107735996283169557696965)
                    ·
                      refine ⟨1145200499303094292068181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6107735996283169557696965 1145200499303094292068181)
                      ·
                        rfl

theorem cell23_2230270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2230270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230270 prefixEnd_2230270 := by exact prefixLift 2230270
  have htrace : WordTrace (prefixWord ++ tailWord_2230270) baseStart_2230270 baseEnd_2230270 := by
    simpa [prefixWord, tailWord_2230270, baseEnd_2230270] using wordTrace_append hprefix tailTrace_2230270
  have hstable : (prefixWord ++ tailWord_2230270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230270).length < 2 ^ (prefixWord ++ tailWord_2230270).sum := by decide
  have hdescent : baseEnd_2230270 < baseStart_2230270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230273 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2230273 : Nat := 118140960795 + 2230273 * 2 ^ 59
def prefixEnd_2230273 : Nat := 4983230072969 + 3 ^ 40 * 2230273 * 2
def baseEnd_2230273 : Nat := 1145202039745057780330667

theorem tailTrace_2230273 : CollatzResearch.WordTrace tailWord_2230273 prefixEnd_2230273 1145202039745057780330667 := by
  unfold tailWord_2230273
  simp only [CollatzResearch.WordTrace]
  refine ⟨81344739049109296148487473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54229826032739530765658315 81344739049109296148487473)
  ·
    refine ⟨61008554286831972111365605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81344739049109296148487473 61008554286831972111365605)
    ·
      refine ⟨11439103928780994770881051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61008554286831972111365605 11439103928780994770881051)
      ·
        refine ⟨17158655893171492156321577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439103928780994770881051 17158655893171492156321577)
        ·
          refine ⟨12868991919878619117241183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17158655893171492156321577 12868991919878619117241183)
          ·
            refine ⟨19303487879817928675861775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12868991919878619117241183 19303487879817928675861775)
            ·
              refine ⟨28955231819726893013792663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19303487879817928675861775 28955231819726893013792663)
              ·
                refine ⟨43432847729590339520688995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28955231819726893013792663 43432847729590339520688995)
                ·
                  refine ⟨65149271594385509281033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43432847729590339520688995 65149271594385509281033493)
                  ·
                    refine ⟨3053872105986820747548445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65149271594385509281033493 3053872105986820747548445)
                    ·
                      refine ⟨1145202039745057780330667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053872105986820747548445 1145202039745057780330667)
                      ·
                        rfl

theorem cell23_2230273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2230273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230273 prefixEnd_2230273 := by exact prefixLift 2230273
  have htrace : WordTrace (prefixWord ++ tailWord_2230273) baseStart_2230273 baseEnd_2230273 := by
    simpa [prefixWord, tailWord_2230273, baseEnd_2230273] using wordTrace_append hprefix tailTrace_2230273
  have hstable : (prefixWord ++ tailWord_2230273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230273).length < 2 ^ (prefixWord ++ tailWord_2230273).sum := by decide
  have hdescent : baseEnd_2230273 < baseStart_2230273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230283 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_2230283 : Nat := 118140960795 + 2230283 * 2 ^ 59
def prefixEnd_2230283 : Nat := 4983230072969 + 3 ^ 40 * 2230283 * 2
def baseEnd_2230283 : Nat := 1145207174551602741205621

theorem tailTrace_2230283 : CollatzResearch.WordTrace tailWord_2230283 prefixEnd_2230283 1145207174551602741205621 := by
  unfold tailWord_2230283
  simp only [CollatzResearch.WordTrace]
  refine ⟨81345103779073067856351503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54230069186048711904234335 81345103779073067856351503)
  ·
    refine ⟨122017655668609601784527255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81345103779073067856351503 122017655668609601784527255)
    ·
      refine ⟨183026483502914402676790883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122017655668609601784527255 183026483502914402676790883)
      ·
        refine ⟨274539725254371604015186325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183026483502914402676790883 274539725254371604015186325)
        ·
          refine ⟨12869049621298668938211859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 274539725254371604015186325 12869049621298668938211859)
          ·
            refine ⟨19303574431948003407317789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869049621298668938211859 19303574431948003407317789)
            ·
              refine ⟨7238840411980501277744171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19303574431948003407317789 7238840411980501277744171)
              ·
                refine ⟨10858260617970751916616257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238840411980501277744171 10858260617970751916616257)
                ·
                  refine ⟨8143695463478063937462193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10858260617970751916616257 8143695463478063937462193)
                  ·
                    refine ⟨6107771597608547953096645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8143695463478063937462193 6107771597608547953096645)
                    ·
                      refine ⟨1145207174551602741205621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6107771597608547953096645 1145207174551602741205621)
                      ·
                        rfl

theorem cell23_2230283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_2230283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230283 prefixEnd_2230283 := by exact prefixLift 2230283
  have htrace : WordTrace (prefixWord ++ tailWord_2230283) baseStart_2230283 baseEnd_2230283 := by
    simpa [prefixWord, tailWord_2230283, baseEnd_2230283] using wordTrace_append hprefix tailTrace_2230283
  have hstable : (prefixWord ++ tailWord_2230283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230283).length < 2 ^ (prefixWord ++ tailWord_2230283).sum := by decide
  have hdescent : baseEnd_2230283 < baseStart_2230283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230303 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2230303 : Nat := 118140960795 + 2230303 * 2 ^ 59
def prefixEnd_2230303 : Nat := 4983230072969 + 3 ^ 40 * 2230303 * 2
def baseEnd_2230303 : Nat := 1145217444164692662955529

theorem tailTrace_2230303 : CollatzResearch.WordTrace tailWord_2230303 prefixEnd_2230303 1145217444164692662955529 := by
  unfold tailWord_2230303
  simp only [CollatzResearch.WordTrace]
  refine ⟨81345833239000611272079563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54230555492667074181386375 81345833239000611272079563)
  ·
    refine ⟨122018749858500916908119345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81345833239000611272079563 122018749858500916908119345)
    ·
      refine ⟨91514062393875687681089509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122018749858500916908119345 91514062393875687681089509)
      ·
        refine ⟨17158886698851691440204283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91514062393875687681089509 17158886698851691440204283)
        ·
          refine ⟨25738330048277537160306425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17158886698851691440204283 25738330048277537160306425)
          ·
            refine ⟨19303747536208152870229819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25738330048277537160306425 19303747536208152870229819)
            ·
              refine ⟨28955621304312229305344729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19303747536208152870229819 28955621304312229305344729)
              ·
                refine ⟨21716715978234171979008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28955621304312229305344729 21716715978234171979008547)
                ·
                  refine ⟨32575073967351257968512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21716715978234171979008547 32575073967351257968512821)
                  ·
                    refine ⟨3053913184439180434548077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32575073967351257968512821 3053913184439180434548077)
                    ·
                      refine ⟨1145217444164692662955529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3053913184439180434548077 1145217444164692662955529)
                      ·
                        rfl

theorem cell23_2230303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2230303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230303 prefixEnd_2230303 := by exact prefixLift 2230303
  have htrace : WordTrace (prefixWord ++ tailWord_2230303) baseStart_2230303 baseEnd_2230303 := by
    simpa [prefixWord, tailWord_2230303, baseEnd_2230303] using wordTrace_append hprefix tailTrace_2230303
  have hstable : (prefixWord ++ tailWord_2230303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230303).length < 2 ^ (prefixWord ++ tailWord_2230303).sum := by decide
  have hdescent : baseEnd_2230303 < baseStart_2230303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230308 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2230308 : Nat := 118140960795 + 2230308 * 2 ^ 59
def prefixEnd_2230308 : Nat := 4983230072969 + 3 ^ 40 * 2230308 * 2
def baseEnd_2230308 : Nat := 1145220011567965143393007

theorem tailTrace_2230308 : CollatzResearch.WordTrace tailWord_2230308 prefixEnd_2230308 1145220011567965143393007 := by
  unfold tailWord_2230308
  simp only [CollatzResearch.WordTrace]
  refine ⟨40673007801991248563005789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54230677069321664750674385 40673007801991248563005789)
  ·
    refine ⟨15252377925746718211127171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40673007801991248563005789 15252377925746718211127171)
    ·
      refine ⟨22878566888620077316690757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15252377925746718211127171 22878566888620077316690757)
      ·
        refine ⟨4289731291616264496879517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22878566888620077316690757 4289731291616264496879517)
        ·
          refine ⟨1608649234356099186329819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4289731291616264496879517 1608649234356099186329819)
          ·
            refine ⟨2412973851534148779494729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608649234356099186329819 2412973851534148779494729)
            ·
              refine ⟨1809730388650611584621047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2412973851534148779494729 1809730388650611584621047)
              ·
                refine ⟨2714595582975917376931571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809730388650611584621047 2714595582975917376931571)
                ·
                  refine ⟨4071893374463876065397357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714595582975917376931571 4071893374463876065397357)
                  ·
                    refine ⟨1526960015423953524524009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4071893374463876065397357 1526960015423953524524009)
                    ·
                      refine ⟨1145220011567965143393007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1526960015423953524524009 1145220011567965143393007)
                      ·
                        rfl

theorem cell23_2230308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2230308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230308 prefixEnd_2230308 := by exact prefixLift 2230308
  have htrace : WordTrace (prefixWord ++ tailWord_2230308) baseStart_2230308 baseEnd_2230308 := by
    simpa [prefixWord, tailWord_2230308, baseEnd_2230308] using wordTrace_append hprefix tailTrace_2230308
  have hstable : (prefixWord ++ tailWord_2230308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230308).length < 2 ^ (prefixWord ++ tailWord_2230308).sum := by decide
  have hdescent : baseEnd_2230308 < baseStart_2230308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230323 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 2, 5]
def baseStart_2230323 : Nat := 118140960795 + 2230323 * 2 ^ 59
def prefixEnd_2230323 : Nat := 4983230072969 + 3 ^ 40 * 2230323 * 2
def baseEnd_2230323 : Nat := 381742571259260861568479

theorem tailTrace_2230323 : CollatzResearch.WordTrace tailWord_2230323 prefixEnd_2230323 381742571259260861568479 := by
  unfold tailWord_2230323
  simp only [CollatzResearch.WordTrace]
  refine ⟨81346562698928154687807623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54231041799285436458538415 81346562698928154687807623)
  ·
    refine ⟨122019844048392232031711435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81346562698928154687807623 122019844048392232031711435)
    ·
      refine ⟨183029766072588348047567153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122019844048392232031711435 183029766072588348047567153)
      ·
        refine ⟨137272324554441261035675365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183029766072588348047567153 137272324554441261035675365)
        ·
          refine ⟨25738560853957736444189131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137272324554441261035675365 25738560853957736444189131)
          ·
            refine ⟨38607841280936604666283697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25738560853957736444189131 38607841280936604666283697)
            ·
              refine ⟨28955880960702453499712773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38607841280936604666283697 28955880960702453499712773)
              ·
                refine ⟨5429227680131710031196145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28955880960702453499712773 5429227680131710031196145)
                ·
                  refine ⟨4071920760098782523397109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429227680131710031196145 4071920760098782523397109)
                  ·
                    refine ⟨381742571259260861568479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4071920760098782523397109 381742571259260861568479)
                    ·
                      rfl

theorem cell23_2230323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].length) (baseStart_2230323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230323 prefixEnd_2230323 := by exact prefixLift 2230323
  have htrace : WordTrace (prefixWord ++ tailWord_2230323) baseStart_2230323 baseEnd_2230323 := by
    simpa [prefixWord, tailWord_2230323, baseEnd_2230323] using wordTrace_append hprefix tailTrace_2230323
  have hstable : (prefixWord ++ tailWord_2230323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230323).length < 2 ^ (prefixWord ++ tailWord_2230323).sum := by decide
  have hdescent : baseEnd_2230323 < baseStart_2230323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230333 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2230333 : Nat := 118140960795 + 2230333 * 2 ^ 59
def prefixEnd_2230333 : Nat := 4983230072969 + 3 ^ 40 * 2230333 * 2
def baseEnd_2230333 : Nat := 1145232848584327545580391

theorem tailTrace_2230333 : CollatzResearch.WordTrace tailWord_2230333 prefixEnd_2230333 1145232848584327545580391 := by
  unfold tailWord_2230333
  simp only [CollatzResearch.WordTrace]
  refine ⟨81346927428891926395671653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54231284952594617597114435 81346927428891926395671653)
  ·
    refine ⟨15252548892917236199188435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81346927428891926395671653 15252548892917236199188435)
    ·
      refine ⟨22878823339375854298782653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15252548892917236199188435 22878823339375854298782653)
      ·
        refine ⟨8579558752265945362043495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22878823339375854298782653 8579558752265945362043495)
        ·
          refine ⟨12869338128398918043065243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8579558752265945362043495 12869338128398918043065243)
          ·
            refine ⟨19304007192598377064597865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869338128398918043065243 19304007192598377064597865)
            ·
              refine ⟨14478005394448782798448399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19304007192598377064597865 14478005394448782798448399)
              ·
                refine ⟨21717008091673174197672599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14478005394448782798448399 21717008091673174197672599)
                ·
                  refine ⟨32575512137509761296508899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21717008091673174197672599 32575512137509761296508899)
                  ·
                    refine ⟨48863268206264641944763349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32575512137509761296508899 48863268206264641944763349)
                    ·
                      refine ⟨1145232848584327545580391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48863268206264641944763349 1145232848584327545580391)
                      ·
                        rfl

theorem cell23_2230333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2230333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230333 prefixEnd_2230333 := by exact prefixLift 2230333
  have htrace : WordTrace (prefixWord ++ tailWord_2230333) baseStart_2230333 baseEnd_2230333 := by
    simpa [prefixWord, tailWord_2230333, baseEnd_2230333] using wordTrace_append hprefix tailTrace_2230333
  have hstable : (prefixWord ++ tailWord_2230333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230333).length < 2 ^ (prefixWord ++ tailWord_2230333).sum := by decide
  have hdescent : baseEnd_2230333 < baseStart_2230333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230343 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2230343 : Nat := 118140960795 + 2230343 * 2 ^ 59
def prefixEnd_2230343 : Nat := 4983230072969 + 3 ^ 40 * 2230343 * 2
def baseEnd_2230343 : Nat := 1145237983390872506455345

theorem tailTrace_2230343 : CollatzResearch.WordTrace tailWord_2230343 prefixEnd_2230343 1145237983390872506455345 := by
  unfold tailWord_2230343
  simp only [CollatzResearch.WordTrace]
  refine ⟨81347292158855698103535683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54231528105903798735690455 81347292158855698103535683)
  ·
    refine ⟨122020938238283547155303525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81347292158855698103535683 122020938238283547155303525)
    ·
      refine ⟨22878925919678165091619411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122020938238283547155303525 22878925919678165091619411)
      ·
        refine ⟨34318388879517247637429117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22878925919678165091619411 34318388879517247637429117)
        ·
          refine ⟨12869395829818967864035919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34318388879517247637429117 12869395829818967864035919)
          ·
            refine ⟨19304093744728451796053879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869395829818967864035919 19304093744728451796053879)
            ·
              refine ⟨28956140617092677694080819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19304093744728451796053879 28956140617092677694080819)
              ·
                refine ⟨43434210925639016541121229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28956140617092677694080819 43434210925639016541121229)
                ·
                  refine ⟨16287829097114631202920461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43434210925639016541121229 16287829097114631202920461)
                  ·
                    refine ⟨6107935911417986701095173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16287829097114631202920461 6107935911417986701095173)
                    ·
                      refine ⟨1145237983390872506455345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6107935911417986701095173 1145237983390872506455345)
                      ·
                        rfl

theorem cell23_2230343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2230343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230343 prefixEnd_2230343 := by exact prefixLift 2230343
  have htrace : WordTrace (prefixWord ++ tailWord_2230343) baseStart_2230343 baseEnd_2230343 := by
    simpa [prefixWord, tailWord_2230343, baseEnd_2230343] using wordTrace_append hprefix tailTrace_2230343
  have hstable : (prefixWord ++ tailWord_2230343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230343).length < 2 ^ (prefixWord ++ tailWord_2230343).sum := by decide
  have hdescent : baseEnd_2230343 < baseStart_2230343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230380 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_2230380 : Nat := 118140960795 + 2230380 * 2 ^ 59
def prefixEnd_2230380 : Nat := 4983230072969 + 3 ^ 40 * 2230380 * 2
def baseEnd_2230380 : Nat := 1145256982175088861692675

theorem tailTrace_2230380 : CollatzResearch.WordTrace tailWord_2230380 prefixEnd_2230380 1145256982175088861692675 := by
  unfold tailWord_2230380
  simp only [CollatzResearch.WordTrace]
  refine ⟨40674320829860826711316297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54232427773147768948421729 40674320829860826711316297)
  ·
    refine ⟨30505740622395620033487223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40674320829860826711316297 30505740622395620033487223)
    ·
      refine ⟨45758610933593430050230835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30505740622395620033487223 45758610933593430050230835)
      ·
        refine ⟨68637916400390145075346253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45758610933593430050230835 68637916400390145075346253)
        ·
          refine ⟨25739218650146304403254845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68637916400390145075346253 25739218650146304403254845)
          ·
            refine ⟨9652206993804864151220567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25739218650146304403254845 9652206993804864151220567)
            ·
              refine ⟨14478310490707296226830851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9652206993804864151220567 14478310490707296226830851)
              ·
                refine ⟨21717465736060944340246277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14478310490707296226830851 21717465736060944340246277)
                ·
                  refine ⟨4072024825511427063796177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21717465736060944340246277 4072024825511427063796177)
                  ·
                    refine ⟨3054018619133570297847133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4072024825511427063796177 3054018619133570297847133)
                    ·
                      refine ⟨1145256982175088861692675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054018619133570297847133 1145256982175088861692675)
                      ·
                        rfl

theorem cell23_2230380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_2230380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230380 prefixEnd_2230380 := by exact prefixLift 2230380
  have htrace : WordTrace (prefixWord ++ tailWord_2230380) baseStart_2230380 baseEnd_2230380 := by
    simpa [prefixWord, tailWord_2230380, baseEnd_2230380] using wordTrace_append hprefix tailTrace_2230380
  have hstable : (prefixWord ++ tailWord_2230380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230380).length < 2 ^ (prefixWord ++ tailWord_2230380).sum := by decide
  have hdescent : baseEnd_2230380 < baseStart_2230380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230383 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 8]
def baseStart_2230383 : Nat := 118140960795 + 2230383 * 2 ^ 59
def prefixEnd_2230383 : Nat := 4983230072969 + 3 ^ 40 * 2230383 * 2
def baseEnd_2230383 : Nat := 127250946957450261106129

theorem tailTrace_2230383 : CollatzResearch.WordTrace tailWord_2230383 prefixEnd_2230383 127250946957450261106129 := by
  unfold tailWord_2230383
  simp only [CollatzResearch.WordTrace]
  refine ⟨81348751078710784934991803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54232500719140523289994535 81348751078710784934991803)
  ·
    refine ⟨122023126618066177402487705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81348751078710784934991803 122023126618066177402487705)
    ·
      refine ⟨91517344963549633051865779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122023126618066177402487705 91517344963549633051865779)
      ·
        refine ⟨137276017445324449577798669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91517344963549633051865779 137276017445324449577798669)
        ·
          refine ⟨51478506541996668591674501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137276017445324449577798669 51478506541996668591674501)
          ·
            refine ⟨9652219976624375360938969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51478506541996668591674501 9652219976624375360938969)
            ·
              refine ⟨7239164982468281520704227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9652219976624375360938969 7239164982468281520704227)
              ·
                refine ⟨10858747473702422281056341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7239164982468281520704227 10858747473702422281056341)
                ·
                  refine ⟨127250946957450261106129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10858747473702422281056341 127250946957450261106129)
                  ·
                    rfl

theorem cell23_2230383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 8].length) (baseStart_2230383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230383 prefixEnd_2230383 := by exact prefixLift 2230383
  have htrace : WordTrace (prefixWord ++ tailWord_2230383) baseStart_2230383 baseEnd_2230383 := by
    simpa [prefixWord, tailWord_2230383, baseEnd_2230383] using wordTrace_append hprefix tailTrace_2230383
  have hstable : (prefixWord ++ tailWord_2230383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230383).length < 2 ^ (prefixWord ++ tailWord_2230383).sum := by decide
  have hdescent : baseEnd_2230383 < baseStart_2230383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230414 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2230414 : Nat := 118140960795 + 2230414 * 2 ^ 59
def prefixEnd_2230414 : Nat := 4983230072969 + 3 ^ 40 * 2230414 * 2
def baseEnd_2230414 : Nat := 1145274440517341728667519

theorem tailTrace_2230414 : CollatzResearch.WordTrace tailWord_2230414 prefixEnd_2230414 1145274440517341728667519 := by
  unfold tailWord_2230414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168735217699809653671287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54233254494398984819580197 10168735217699809653671287)
  ·
    refine ⟨15253102826549714480506931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168735217699809653671287 15253102826549714480506931)
    ·
      refine ⟨22879654239824571720760397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253102826549714480506931 22879654239824571720760397)
      ·
        refine ⟨8579870339934214395285149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22879654239824571720760397 8579870339934214395285149)
        ·
          refine ⟨3217451377475330398231931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8579870339934214395285149 3217451377475330398231931)
          ·
            refine ⟨4826177066212995597347897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217451377475330398231931 4826177066212995597347897)
            ·
              refine ⟨3619632799659746698010923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826177066212995597347897 3619632799659746698010923)
              ·
                refine ⟨5429449199489620047016385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619632799659746698010923 5429449199489620047016385)
                ·
                  refine ⟨4072086899617215035262289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429449199489620047016385 4072086899617215035262289)
                  ·
                    refine ⟨3054065174712911276446717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4072086899617215035262289 3054065174712911276446717)
                    ·
                      refine ⟨1145274440517341728667519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054065174712911276446717 1145274440517341728667519)
                      ·
                        rfl

theorem cell23_2230414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2230414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230414 prefixEnd_2230414 := by exact prefixLift 2230414
  have htrace : WordTrace (prefixWord ++ tailWord_2230414) baseStart_2230414 baseEnd_2230414 := by
    simpa [prefixWord, tailWord_2230414, baseEnd_2230414] using wordTrace_append hprefix tailTrace_2230414
  have hstable : (prefixWord ++ tailWord_2230414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230414).length < 2 ^ (prefixWord ++ tailWord_2230414).sum := by decide
  have hdescent : baseEnd_2230414 < baseStart_2230414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230437 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_2230437 : Nat := 118140960795 + 2230437 * 2 ^ 59
def prefixEnd_2230437 : Nat := 4983230072969 + 3 ^ 40 * 2230437 * 2
def baseEnd_2230437 : Nat := 1145286250572395138679913

theorem tailTrace_2230437 : CollatzResearch.WordTrace tailWord_2230437 prefixEnd_2230437 1145286250572395138679913 := by
  unfold tailWord_2230437
  simp only [CollatzResearch.WordTrace]
  refine ⟨81350720620515152157457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54233813747010101438305043 81350720620515152157457565)
  ·
    refine ⟨30506520232693182059046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81350720620515152157457565 30506520232693182059046587)
    ·
      refine ⟨45759780349039773088569881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30506520232693182059046587 45759780349039773088569881)
      ·
        refine ⟨34319835261779829816427411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45759780349039773088569881 34319835261779829816427411)
        ·
          refine ⟨51479752892669744724641117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34319835261779829816427411 51479752892669744724641117)
          ·
            refine ⟨19304907334751154271740419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51479752892669744724641117 19304907334751154271740419)
            ·
              refine ⟨28957361002126731407610629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19304907334751154271740419 28957361002126731407610629)
              ·
                refine ⟨5429505187898762138926993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28957361002126731407610629 5429505187898762138926993)
                ·
                  refine ⟨4072128890924071604195245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429505187898762138926993 4072128890924071604195245)
                  ·
                    refine ⟨1527048334096526851573217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4072128890924071604195245 1527048334096526851573217)
                    ·
                      refine ⟨1145286250572395138679913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527048334096526851573217 1145286250572395138679913)
                      ·
                        rfl

theorem cell23_2230437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_2230437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230437 prefixEnd_2230437 := by exact prefixLift 2230437
  have htrace : WordTrace (prefixWord ++ tailWord_2230437) baseStart_2230437 baseEnd_2230437 := by
    simpa [prefixWord, tailWord_2230437, baseEnd_2230437] using wordTrace_append hprefix tailTrace_2230437
  have hstable : (prefixWord ++ tailWord_2230437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230437).length < 2 ^ (prefixWord ++ tailWord_2230437).sum := by decide
  have hdescent : baseEnd_2230437 < baseStart_2230437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230450 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2230450 : Nat := 118140960795 + 2230450 * 2 ^ 59
def prefixEnd_2230450 : Nat := 4983230072969 + 3 ^ 40 * 2230450 * 2
def baseEnd_2230450 : Nat := 1145292925820903587817353

theorem tailTrace_2230450 : CollatzResearch.WordTrace tailWord_2230450 prefixEnd_2230450 1145292925820903587817353 := by
  unfold tailWord_2230450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337798692367013844420201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54234129846312036918453869 20337798692367013844420201)
  ·
    refine ⟨15253349019275260383315151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20337798692367013844420201 15253349019275260383315151)
    ·
      refine ⟨22880023528912890574972727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253349019275260383315151 22880023528912890574972727)
      ·
        refine ⟨34320035293369335862459091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22880023528912890574972727 34320035293369335862459091)
        ·
          refine ⟨51480052940054003793688637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34320035293369335862459091 51480052940054003793688637)
          ·
            refine ⟨19305019852520251422633239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51480052940054003793688637 19305019852520251422633239)
            ·
              refine ⟨28957529778780377133949859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19305019852520251422633239 28957529778780377133949859)
              ·
                refine ⟨43436294668170565700924789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28957529778780377133949859 43436294668170565700924789)
                ·
                  refine ⟨4072152625140990534461699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43436294668170565700924789 4072152625140990534461699)
                  ·
                    refine ⟨6108228937711485801692549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072152625140990534461699 6108228937711485801692549)
                    ·
                      refine ⟨1145292925820903587817353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6108228937711485801692549 1145292925820903587817353)
                      ·
                        rfl

theorem cell23_2230450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2230450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230450 prefixEnd_2230450 := by exact prefixLift 2230450
  have htrace : WordTrace (prefixWord ++ tailWord_2230450) baseStart_2230450 baseEnd_2230450 := by
    simpa [prefixWord, tailWord_2230450, baseEnd_2230450] using wordTrace_append hprefix tailTrace_2230450
  have hstable : (prefixWord ++ tailWord_2230450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230450).length < 2 ^ (prefixWord ++ tailWord_2230450).sum := by decide
  have hdescent : baseEnd_2230450 < baseStart_2230450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230501 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2230501 : Nat := 118140960795 + 2230501 * 2 ^ 59
def prefixEnd_2230501 : Nat := 4983230072969 + 3 ^ 40 * 2230501 * 2
def baseEnd_2230501 : Nat := 1145319113334282888279619

theorem tailTrace_2230501 : CollatzResearch.WordTrace tailWord_2230501 prefixEnd_2230501 1145319113334282888279619 := by
  unfold tailWord_2230501
  simp only [CollatzResearch.WordTrace]
  refine ⟨81353054892283291087787357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54235369928188860725191571 81353054892283291087787357)
  ·
    refine ⟨30507395584606234157920259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81353054892283291087787357 30507395584606234157920259)
    ·
      refine ⟨45761093376909351236880389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30507395584606234157920259 45761093376909351236880389)
      ·
        refine ⟨8580205008170503356915073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45761093376909351236880389 8580205008170503356915073)
        ·
          refine ⟨6435153756127877517686305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580205008170503356915073 6435153756127877517686305)
          ·
            refine ⟨4826365317095908138264729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6435153756127877517686305 4826365317095908138264729)
            ·
              refine ⟨3619773987821931103698547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826365317095908138264729 3619773987821931103698547)
              ·
                refine ⟨5429660981732896655547821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619773987821931103698547 5429660981732896655547821)
                ·
                  refine ⟨2036122868149836245830433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5429660981732896655547821 2036122868149836245830433)
                  ·
                    refine ⟨1527092151112377184372825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2036122868149836245830433 1527092151112377184372825)
                    ·
                      refine ⟨1145319113334282888279619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527092151112377184372825 1145319113334282888279619)
                      ·
                        rfl

theorem cell23_2230501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2230501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230501 prefixEnd_2230501 := by exact prefixLift 2230501
  have htrace : WordTrace (prefixWord ++ tailWord_2230501) baseStart_2230501 baseEnd_2230501 := by
    simpa [prefixWord, tailWord_2230501, baseEnd_2230501] using wordTrace_append hprefix tailTrace_2230501
  have hstable : (prefixWord ++ tailWord_2230501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230501).length < 2 ^ (prefixWord ++ tailWord_2230501).sum := by decide
  have hdescent : baseEnd_2230501 < baseStart_2230501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230514 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2230514 : Nat := 118140960795 + 2230514 * 2 ^ 59
def prefixEnd_2230514 : Nat := 4983230072969 + 3 ^ 40 * 2230514 * 2
def baseEnd_2230514 : Nat := 1145325788582791337417059

theorem tailTrace_2230514 : CollatzResearch.WordTrace tailWord_2230514 prefixEnd_2230514 1145325788582791337417059 := by
  unfold tailWord_2230514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338382260309048577002649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54235686027490796205340397 20338382260309048577002649)
  ·
    refine ⟨15253786695231786432751987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20338382260309048577002649 15253786695231786432751987)
    ·
      refine ⟨22880680042847679649127981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253786695231786432751987 22880680042847679649127981)
      ·
        refine ⟨8580255016067879868422993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22880680042847679649127981 8580255016067879868422993)
        ·
          refine ⟨6435191262050909901317245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580255016067879868422993 6435191262050909901317245)
          ·
            refine ⟨2413196723269091212993967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6435191262050909901317245 2413196723269091212993967)
            ·
              refine ⟨3619795084903636819490951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413196723269091212993967 3619795084903636819490951)
              ·
                refine ⟨5429692627355455229236427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619795084903636819490951 5429692627355455229236427)
                ·
                  refine ⟨8144538941033182843854641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429692627355455229236427 8144538941033182843854641)
                  ·
                    refine ⟨6108404205774887132890981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8144538941033182843854641 6108404205774887132890981)
                    ·
                      refine ⟨1145325788582791337417059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6108404205774887132890981 1145325788582791337417059)
                      ·
                        rfl

theorem cell23_2230514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2230514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230514 prefixEnd_2230514 := by exact prefixLift 2230514
  have htrace : WordTrace (prefixWord ++ tailWord_2230514) baseStart_2230514 baseEnd_2230514 := by
    simpa [prefixWord, tailWord_2230514, baseEnd_2230514] using wordTrace_append hprefix tailTrace_2230514
  have hstable : (prefixWord ++ tailWord_2230514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230514).length < 2 ^ (prefixWord ++ tailWord_2230514).sum := by decide
  have hdescent : baseEnd_2230514 < baseStart_2230514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230578 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_2230578 : Nat := 118140960795 + 2230578 * 2 ^ 59
def prefixEnd_2230578 : Nat := 4983230072969 + 3 ^ 40 * 2230578 * 2
def baseEnd_2230578 : Nat := 1145358651344679087016765

theorem tailTrace_2230578 : CollatzResearch.WordTrace tailWord_2230578 prefixEnd_2230578 1145358651344679087016765 := by
  unfold tailWord_2230578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338965828251083309585097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54237242208669555492226925 20338965828251083309585097)
  ·
    refine ⟨15254224371188312482188823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20338965828251083309585097 15254224371188312482188823)
    ·
      refine ⟨22881336556782468723283235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15254224371188312482188823 22881336556782468723283235)
      ·
        refine ⟨34322004835173703084924853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22881336556782468723283235 34322004835173703084924853)
        ·
          refine ⟨3217687953297534664211705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34322004835173703084924853 3217687953297534664211705)
          ·
            refine ⟨2413265964973150998158779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3217687953297534664211705 2413265964973150998158779)
            ·
              refine ⟨3619898947459726497238169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413265964973150998158779 3619898947459726497238169)
              ·
                refine ⟨2714924210594794872928627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619898947459726497238169 2714924210594794872928627)
                ·
                  refine ⟨4072386315892192309392941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714924210594794872928627 4072386315892192309392941)
                  ·
                    refine ⟨1527144868459572116022353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4072386315892192309392941 1527144868459572116022353)
                    ·
                      refine ⟨1145358651344679087016765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527144868459572116022353 1145358651344679087016765)
                      ·
                        rfl

theorem cell23_2230578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_2230578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230578 prefixEnd_2230578 := by exact prefixLift 2230578
  have htrace : WordTrace (prefixWord ++ tailWord_2230578) baseStart_2230578 baseEnd_2230578 := by
    simpa [prefixWord, tailWord_2230578, baseEnd_2230578] using wordTrace_append hprefix tailTrace_2230578
  have hstable : (prefixWord ++ tailWord_2230578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230578).length < 2 ^ (prefixWord ++ tailWord_2230578).sum := by decide
  have hdescent : baseEnd_2230578 < baseStart_2230578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230624 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2230624 : Nat := 118140960795 + 2230624 * 2 ^ 59
def prefixEnd_2230624 : Nat := 4983230072969 + 3 ^ 40 * 2230624 * 2
def baseEnd_2230624 : Nat := 1145382271454785907041553

theorem tailTrace_2230624 : CollatzResearch.WordTrace tailWord_2230624 prefixEnd_2230624 1145382271454785907041553 := by
  unfold tailWord_2230624
  simp only [CollatzResearch.WordTrace]
  refine ⟨40678770535418841547257463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54238360713891788729676617 40678770535418841547257463)
  ·
    refine ⟨61018155803128262320886195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40678770535418841547257463 61018155803128262320886195)
    ·
      refine ⟨91527233704692393481329293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61018155803128262320886195 91527233704692393481329293)
      ·
        refine ⟨34322712639259647555498485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91527233704692393481329293 34322712639259647555498485)
        ·
          refine ⟨3217754309930591958327983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34322712639259647555498485 3217754309930591958327983)
          ·
            refine ⟨4826631464895887937491975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217754309930591958327983 4826631464895887937491975)
            ·
              refine ⟨7239947197343831906237963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826631464895887937491975 7239947197343831906237963)
              ·
                refine ⟨10859920796015747859356945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7239947197343831906237963 10859920796015747859356945)
                ·
                  refine ⟨8144940597011810894517709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10859920796015747859356945 8144940597011810894517709)
                  ·
                    refine ⟨3054352723879429085444141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8144940597011810894517709 3054352723879429085444141)
                    ·
                      refine ⟨1145382271454785907041553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054352723879429085444141 1145382271454785907041553)
                      ·
                        rfl

theorem cell23_2230624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2230624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230624 prefixEnd_2230624 := by exact prefixLift 2230624
  have htrace : WordTrace (prefixWord ++ tailWord_2230624) baseStart_2230624 baseEnd_2230624 := by
    simpa [prefixWord, tailWord_2230624, baseEnd_2230624] using wordTrace_append hprefix tailTrace_2230624
  have hstable : (prefixWord ++ tailWord_2230624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230624).length < 2 ^ (prefixWord ++ tailWord_2230624).sum := by decide
  have hdescent : baseEnd_2230624 < baseStart_2230624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230647 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_2230647 : Nat := 118140960795 + 2230647 * 2 ^ 59
def prefixEnd_2230647 : Nat := 4983230072969 + 3 ^ 40 * 2230647 * 2
def baseEnd_2230647 : Nat := 1145394081509839317053947

theorem tailTrace_2230647 : CollatzResearch.WordTrace tailWord_2230647 prefixEnd_2230647 1145394081509839317053947 := by
  unfold tailWord_2230647
  simp only [CollatzResearch.WordTrace]
  refine ⟨81358379949754358022602195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54238919966502905348401463 81358379949754358022602195)
  ·
    refine ⟨122037569924631537033903293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81358379949754358022602195 122037569924631537033903293)
    ·
      refine ⟨45764088721736826387713735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122037569924631537033903293 45764088721736826387713735)
      ·
        refine ⟨68646133082605239581570603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45764088721736826387713735 68646133082605239581570603)
        ·
          refine ⟨102969199623907859372355905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68646133082605239581570603 102969199623907859372355905)
          ·
            refine ⟨77226899717930894529266929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102969199623907859372355905 77226899717930894529266929)
            ·
              refine ⟨57920174788448170896950197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77226899717930894529266929 57920174788448170896950197)
              ·
                refine ⟨5430016386417016021589081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57920174788448170896950197 5430016386417016021589081)
                ·
                  refine ⟨4072512289812762016191811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5430016386417016021589081 4072512289812762016191811)
                  ·
                    refine ⟨6108768434719143024287717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072512289812762016191811 6108768434719143024287717)
                    ·
                      refine ⟨1145394081509839317053947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6108768434719143024287717 1145394081509839317053947)
                      ·
                        rfl

theorem cell23_2230647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_2230647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230647 prefixEnd_2230647 := by exact prefixLift 2230647
  have htrace : WordTrace (prefixWord ++ tailWord_2230647) baseStart_2230647 baseEnd_2230647 := by
    simpa [prefixWord, tailWord_2230647, baseEnd_2230647] using wordTrace_append hprefix tailTrace_2230647
  have hstable : (prefixWord ++ tailWord_2230647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230647).length < 2 ^ (prefixWord ++ tailWord_2230647).sum := by decide
  have hdescent : baseEnd_2230647 < baseStart_2230647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230650 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_2230650 : Nat := 118140960795 + 2230650 * 2 ^ 59
def prefixEnd_2230650 : Nat := 4983230072969 + 3 ^ 40 * 2230650 * 2
def baseEnd_2230650 : Nat := 1145395621951802805316433

theorem tailTrace_2230650 : CollatzResearch.WordTrace tailWord_2230650 prefixEnd_2230650 1145395621951802805316433 := by
  unfold tailWord_2230650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20339622342185872383740351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54238992912495659689974269 20339622342185872383740351)
  ·
    refine ⟨30509433513278808575610527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20339622342185872383740351 30509433513278808575610527)
    ·
      refine ⟨45764150269918212863415791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30509433513278808575610527 45764150269918212863415791)
      ·
        refine ⟨68646225404877319295123687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45764150269918212863415791 68646225404877319295123687)
        ·
          refine ⟨102969338107315978942685531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68646225404877319295123687 102969338107315978942685531)
          ·
            refine ⟨154454007160973968414028297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102969338107315978942685531 154454007160973968414028297)
            ·
              refine ⟨115840505370730476310521223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154454007160973968414028297 115840505370730476310521223)
              ·
                refine ⟨173760758056095714465781835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115840505370730476310521223 173760758056095714465781835)
                ·
                  refine ⟨260641137084143571698672753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173760758056095714465781835 260641137084143571698672753)
                  ·
                    refine ⟨195480852813107678774004565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260641137084143571698672753 195480852813107678774004565)
                    ·
                      refine ⟨1145395621951802805316433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 195480852813107678774004565 1145395621951802805316433)
                      ·
                        rfl

theorem cell23_2230650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_2230650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230650 prefixEnd_2230650 := by exact prefixLift 2230650
  have htrace : WordTrace (prefixWord ++ tailWord_2230650) baseStart_2230650 baseEnd_2230650 := by
    simpa [prefixWord, tailWord_2230650, baseEnd_2230650] using wordTrace_append hprefix tailTrace_2230650
  have hstable : (prefixWord ++ tailWord_2230650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230650).length < 2 ^ (prefixWord ++ tailWord_2230650).sum := by decide
  have hdescent : baseEnd_2230650 < baseStart_2230650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230664 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_2230664 : Nat := 118140960795 + 2230664 * 2 ^ 59
def prefixEnd_2230664 : Nat := 4983230072969 + 3 ^ 40 * 2230664 * 2
def baseEnd_2230664 : Nat := 1145402810680965750541369

theorem tailTrace_2230664 : CollatzResearch.WordTrace tailWord_2230664 prefixEnd_2230664 1145402810680965750541369 := by
  unfold tailWord_2230664
  simp only [CollatzResearch.WordTrace]
  refine ⟨40679499995346384962985523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54239333327128513283980697 40679499995346384962985523)
  ·
    refine ⟨61019249993019577444478285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40679499995346384962985523 61019249993019577444478285)
    ·
      refine ⟨22882218747382341541679357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61019249993019577444478285 22882218747382341541679357)
      ·
        refine ⟨8580832030268378078129759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22882218747382341541679357 8580832030268378078129759)
        ·
          refine ⟨12871248045402567117194639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580832030268378078129759 12871248045402567117194639)
          ·
            refine ⟨19306872068103850675791959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12871248045402567117194639 19306872068103850675791959)
            ·
              refine ⟨28960308102155776013687939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19306872068103850675791959 28960308102155776013687939)
              ·
                refine ⟨43440462153233664020531909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28960308102155776013687939 43440462153233664020531909)
                ·
                  refine ⟨8145086653731312003849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43440462153233664020531909 8145086653731312003849733)
                  ·
                    refine ⟨1527203747574621000721825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8145086653731312003849733 1527203747574621000721825)
                    ·
                      refine ⟨1145402810680965750541369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527203747574621000721825 1145402810680965750541369)
                      ·
                        rfl

theorem cell23_2230664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_2230664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230664 prefixEnd_2230664 := by exact prefixLift 2230664
  have htrace : WordTrace (prefixWord ++ tailWord_2230664) baseStart_2230664 baseEnd_2230664 := by
    simpa [prefixWord, tailWord_2230664, baseEnd_2230664] using wordTrace_append hprefix tailTrace_2230664
  have hstable : (prefixWord ++ tailWord_2230664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230664).length < 2 ^ (prefixWord ++ tailWord_2230664).sum := by decide
  have hdescent : baseEnd_2230664 < baseStart_2230664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230714 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_2230714 : Nat := 118140960795 + 2230714 * 2 ^ 59
def prefixEnd_2230714 : Nat := 4983230072969 + 3 ^ 40 * 2230714 * 2
def baseEnd_2230714 : Nat := 1145428484713690554916139

theorem tailTrace_2230714 : CollatzResearch.WordTrace tailWord_2230714 prefixEnd_2230714 1145428484713690554916139 := by
  unfold tailWord_2230714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340205910127907116322799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54240549093674418976860797 20340205910127907116322799)
  ·
    refine ⟨30510308865191860674484199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20340205910127907116322799 30510308865191860674484199)
    ·
      refine ⟨45765463297787791011726299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30510308865191860674484199 45765463297787791011726299)
      ·
        refine ⟨68648194946681686517589449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45765463297787791011726299 68648194946681686517589449)
        ·
          refine ⟨51486146210011264888192087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68648194946681686517589449 51486146210011264888192087)
          ·
            refine ⟨77229219315016897332288131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51486146210011264888192087 77229219315016897332288131)
            ·
              refine ⟨115843828972525345998432197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77229219315016897332288131 115843828972525345998432197)
              ·
                refine ⟨21720717932348502374706037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115843828972525345998432197 21720717932348502374706037)
                ·
                  refine ⟨2036317306157672097628691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21720717932348502374706037 2036317306157672097628691)
                  ·
                    refine ⟨3054475959236508146443037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036317306157672097628691 3054475959236508146443037)
                    ·
                      refine ⟨1145428484713690554916139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054475959236508146443037 1145428484713690554916139)
                      ·
                        rfl

theorem cell23_2230714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_2230714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230714 prefixEnd_2230714 := by exact prefixLift 2230714
  have htrace : WordTrace (prefixWord ++ tailWord_2230714) baseStart_2230714 baseEnd_2230714 := by
    simpa [prefixWord, tailWord_2230714, baseEnd_2230714] using wordTrace_append hprefix tailTrace_2230714
  have hstable : (prefixWord ++ tailWord_2230714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230714).length < 2 ^ (prefixWord ++ tailWord_2230714).sum := by decide
  have hdescent : baseEnd_2230714 < baseStart_2230714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230751 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 1, 5]
def baseStart_2230751 : Nat := 118140960795 + 2230751 * 2 ^ 59
def prefixEnd_2230751 : Nat := 4983230072969 + 3 ^ 40 * 2230751 * 2
def baseEnd_2230751 : Nat := 381815827832635636717823

theorem tailTrace_2230751 : CollatzResearch.WordTrace tailWord_2230751 prefixEnd_2230751 381815827832635636717823 := by
  unfold tailWord_2230751
  simp only [CollatzResearch.WordTrace]
  refine ⟨81362173141377583784388107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54241448760918389189592071 81362173141377583784388107)
  ·
    refine ⟨122043259712066375676582161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81362173141377583784388107 122043259712066375676582161)
    ·
      refine ⟨91532444784049781757436621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122043259712066375676582161 91532444784049781757436621)
      ·
        refine ⟨34324666794018668159038733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91532444784049781757436621 34324666794018668159038733)
        ·
          refine ⟨12871750047757000559639525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34324666794018668159038733 12871750047757000559639525)
          ·
            refine ⟨2413453133954437604932411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12871750047757000559639525 2413453133954437604932411)
            ·
              refine ⟨3620179700931656407398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413453133954437604932411 3620179700931656407398617)
              ·
                refine ⟨2715134775698742305548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620179700931656407398617 2715134775698742305548963)
                ·
                  refine ⟨4072702163548113458323445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715134775698742305548963 4072702163548113458323445)
                  ·
                    refine ⟨381815827832635636717823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4072702163548113458323445 381815827832635636717823)
                    ·
                      rfl

theorem cell23_2230751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_2230751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230751 prefixEnd_2230751 := by exact prefixLift 2230751
  have htrace : WordTrace (prefixWord ++ tailWord_2230751) baseStart_2230751 baseEnd_2230751 := by
    simpa [prefixWord, tailWord_2230751, baseEnd_2230751] using wordTrace_append hprefix tailTrace_2230751
  have hstable : (prefixWord ++ tailWord_2230751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230751).length < 2 ^ (prefixWord ++ tailWord_2230751).sum := by decide
  have hdescent : baseEnd_2230751 < baseStart_2230751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230771 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 1, 1, 4]
def baseStart_2230771 : Nat := 118140960795 + 2230771 * 2 ^ 59
def prefixEnd_2230771 : Nat := 4983230072969 + 3 ^ 40 * 2230771 * 2
def baseEnd_2230771 : Nat := 1145457753110996831903377

theorem tailTrace_2230771 : CollatzResearch.WordTrace tailWord_2230771 prefixEnd_2230771 1145457753110996831903377 := by
  unfold tailWord_2230771
  simp only [CollatzResearch.WordTrace]
  refine ⟨81362902601305127200116167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54241935067536751466744111 81362902601305127200116167)
  ·
    refine ⟨122044353901957690800174251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81362902601305127200116167 122044353901957690800174251)
    ·
      refine ⟨183066530852936536200261377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122044353901957690800174251 183066530852936536200261377)
      ·
        refine ⟨137299898139702402150196033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183066530852936536200261377 137299898139702402150196033)
        ·
          refine ⟨102974923604776801612647025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137299898139702402150196033 102974923604776801612647025)
          ·
            refine ⟨77231192703582601209485269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102974923604776801612647025 77231192703582601209485269)
            ·
              refine ⟨1810106078990217215847311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77231192703582601209485269 1810106078990217215847311)
              ·
                refine ⟨2715159118485325823770967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810106078990217215847311 2715159118485325823770967)
                ·
                  refine ⟨4072738677727988735656451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715159118485325823770967 4072738677727988735656451)
                  ·
                    refine ⟨6109108016591983103484677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072738677727988735656451 6109108016591983103484677)
                    ·
                      refine ⟨1145457753110996831903377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6109108016591983103484677 1145457753110996831903377)
                      ·
                        rfl

theorem cell23_2230771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 1, 4].length) (baseStart_2230771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230771 prefixEnd_2230771 := by exact prefixLift 2230771
  have htrace : WordTrace (prefixWord ++ tailWord_2230771) baseStart_2230771 baseEnd_2230771 := by
    simpa [prefixWord, tailWord_2230771, baseEnd_2230771] using wordTrace_append hprefix tailTrace_2230771
  have hstable : (prefixWord ++ tailWord_2230771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230771).length < 2 ^ (prefixWord ++ tailWord_2230771).sum := by decide
  have hdescent : baseEnd_2230771 < baseStart_2230771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230781 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2230781 : Nat := 118140960795 + 2230781 * 2 ^ 59
def prefixEnd_2230781 : Nat := 4983230072969 + 3 ^ 40 * 2230781 * 2
def baseEnd_2230781 : Nat := 381820962639180597592777

theorem tailTrace_2230781 : CollatzResearch.WordTrace tailWord_2230781 prefixEnd_2230781 381820962639180597592777 := by
  unfold tailWord_2230781
  simp only [CollatzResearch.WordTrace]
  refine ⟨81363267331268898907980197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54242178220845932605320131 81363267331268898907980197)
  ·
    refine ⟨15255612624612918545246287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81363267331268898907980197 15255612624612918545246287)
    ·
      refine ⟨22883418936919377817869431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15255612624612918545246287 22883418936919377817869431)
      ·
        refine ⟨34325128405379066726804147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22883418936919377817869431 34325128405379066726804147)
        ·
          refine ⟨51487692608068600090206221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34325128405379066726804147 51487692608068600090206221)
          ·
            refine ⟨19307884728025725033827333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51487692608068600090206221 19307884728025725033827333)
            ·
              refine ⟨3620228386504823443842625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19307884728025725033827333 3620228386504823443842625)
              ·
                refine ⟨2715171289878617582881969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620228386504823443842625 2715171289878617582881969)
                ·
                  refine ⟨2036378467408963187161477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715171289878617582881969 2036378467408963187161477)
                  ·
                    refine ⟨381820962639180597592777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036378467408963187161477 381820962639180597592777)
                    ·
                      rfl

theorem cell23_2230781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2230781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230781 prefixEnd_2230781 := by exact prefixLift 2230781
  have htrace : WordTrace (prefixWord ++ tailWord_2230781) baseStart_2230781 baseEnd_2230781 := by
    simpa [prefixWord, tailWord_2230781, baseEnd_2230781] using wordTrace_append hprefix tailTrace_2230781
  have hstable : (prefixWord ++ tailWord_2230781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230781).length < 2 ^ (prefixWord ++ tailWord_2230781).sum := by decide
  have hdescent : baseEnd_2230781 < baseStart_2230781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230852 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2230852 : Nat := 118140960795 + 2230852 * 2 ^ 59
def prefixEnd_2230852 : Nat := 4983230072969 + 3 ^ 40 * 2230852 * 2
def baseEnd_2230852 : Nat := 1145499345044011014990505

theorem tailTrace_2230852 : CollatzResearch.WordTrace tailWord_2230852 prefixEnd_2230852 1145499345044011014990505 := by
  unfold tailWord_2230852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40682928457005839016907405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54243904609341118689209873 40682928457005839016907405)
  ·
    refine ⟨15256098171377189631340277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40682928457005839016907405 15256098171377189631340277)
    ·
      refine ⟨1430259203566611527938151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15256098171377189631340277 1430259203566611527938151)
      ·
        refine ⟨2145388805349917291907227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430259203566611527938151 2145388805349917291907227)
        ·
          refine ⟨3218083208024875937860841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145388805349917291907227 3218083208024875937860841)
          ·
            refine ⟨2413562406018656953395631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218083208024875937860841 2413562406018656953395631)
            ·
              refine ⟨3620343609027985430093447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413562406018656953395631 3620343609027985430093447)
              ·
                refine ⟨5430515413541978145140171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620343609027985430093447 5430515413541978145140171)
                ·
                  refine ⟨8145773120312967217710257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430515413541978145140171 8145773120312967217710257)
                  ·
                    refine ⟨6109329840234725413282693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8145773120312967217710257 6109329840234725413282693)
                    ·
                      refine ⟨1145499345044011014990505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6109329840234725413282693 1145499345044011014990505)
                      ·
                        rfl

theorem cell23_2230852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2230852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230852 prefixEnd_2230852 := by exact prefixLift 2230852
  have htrace : WordTrace (prefixWord ++ tailWord_2230852) baseStart_2230852 baseEnd_2230852 := by
    simpa [prefixWord, tailWord_2230852, baseEnd_2230852] using wordTrace_append hprefix tailTrace_2230852
  have hstable : (prefixWord ++ tailWord_2230852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230852).length < 2 ^ (prefixWord ++ tailWord_2230852).sum := by decide
  have hdescent : baseEnd_2230852 < baseStart_2230852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230855 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_2230855 : Nat := 118140960795 + 2230855 * 2 ^ 59
def prefixEnd_2230855 : Nat := 4983230072969 + 3 ^ 40 * 2230855 * 2
def baseEnd_2230855 : Nat := 1145500885485974503252991

theorem tailTrace_2230855 : CollatzResearch.WordTrace tailWord_2230855 prefixEnd_2230855 1145500885485974503252991 := by
  unfold tailWord_2230855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81365966333000809546174019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54243977555333873030782679 81365966333000809546174019)
  ·
    refine ⟨122048949499501214319261029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81365966333000809546174019 122048949499501214319261029)
    ·
      refine ⟨22884178031156477684861443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122048949499501214319261029 22884178031156477684861443)
      ·
        refine ⟨34326267046734716527292165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22884178031156477684861443 34326267046734716527292165)
        ·
          refine ⟨6436175071262759348867281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34326267046734716527292165 6436175071262759348867281)
          ·
            refine ⟨4827131303447069511650461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6436175071262759348867281 4827131303447069511650461)
            ·
              refine ⟨1810174238792651066868923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4827131303447069511650461 1810174238792651066868923)
              ·
                refine ⟨2715261358188976600303385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810174238792651066868923 2715261358188976600303385)
                ·
                  refine ⟨2036446018641732450227539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715261358188976600303385 2036446018641732450227539)
                  ·
                    refine ⟨3054669027962598675341309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036446018641732450227539 3054669027962598675341309)
                    ·
                      refine ⟨1145500885485974503252991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054669027962598675341309 1145500885485974503252991)
                      ·
                        rfl

theorem cell23_2230855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_2230855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230855 prefixEnd_2230855 := by exact prefixLift 2230855
  have htrace : WordTrace (prefixWord ++ tailWord_2230855) baseStart_2230855 baseEnd_2230855 := by
    simpa [prefixWord, tailWord_2230855, baseEnd_2230855] using wordTrace_append hprefix tailTrace_2230855
  have hstable : (prefixWord ++ tailWord_2230855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230855).length < 2 ^ (prefixWord ++ tailWord_2230855).sum := by decide
  have hdescent : baseEnd_2230855 < baseStart_2230855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230912 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2]
def baseStart_2230912 : Nat := 118140960795 + 2230912 * 2 ^ 59
def prefixEnd_2230912 : Nat := 4983230072969 + 3 ^ 40 * 2230912 * 2
def baseEnd_2230912 : Nat := 1145530153883280780240229

theorem tailTrace_2230912 : CollatzResearch.WordTrace tailWord_2230912 prefixEnd_2230912 1145530153883280780240229 := by
  unfold tailWord_2230912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40684022646897154140499495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54245363529196205520665993 40684022646897154140499495)
  ·
    refine ⟨61026033970345731210749243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40684022646897154140499495 61026033970345731210749243)
    ·
      refine ⟨91539050955518596816123865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61026033970345731210749243 91539050955518596816123865)
      ·
        refine ⟨68654288216638947612092899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91539050955518596816123865 68654288216638947612092899)
        ·
          refine ⟨102981432324958421418139349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68654288216638947612092899 102981432324958421418139349)
          ·
            refine ⟨2413627320116213001987641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 102981432324958421418139349 2413627320116213001987641)
            ·
              refine ⟨1810220490087159751490731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413627320116213001987641 1810220490087159751490731)
              ·
                refine ⟨2715330735130739627236097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810220490087159751490731 2715330735130739627236097)
                ·
                  refine ⟨2036498051348054720427073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715330735130739627236097 2036498051348054720427073)
                  ·
                    refine ⟨1527373538511041040320305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2036498051348054720427073 1527373538511041040320305)
                    ·
                      refine ⟨1145530153883280780240229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527373538511041040320305 1145530153883280780240229)
                      ·
                        rfl

theorem cell23_2230912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_2230912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230912 prefixEnd_2230912 := by exact prefixLift 2230912
  have htrace : WordTrace (prefixWord ++ tailWord_2230912) baseStart_2230912 baseEnd_2230912 := by
    simpa [prefixWord, tailWord_2230912, baseEnd_2230912] using wordTrace_append hprefix tailTrace_2230912
  have hstable : (prefixWord ++ tailWord_2230912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230912).length < 2 ^ (prefixWord ++ tailWord_2230912).sum := by decide
  have hdescent : baseEnd_2230912 < baseStart_2230912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230958 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2230958 : Nat := 118140960795 + 2230958 * 2 ^ 59
def prefixEnd_2230958 : Nat := 4983230072969 + 3 ^ 40 * 2230958 * 2
def baseEnd_2230958 : Nat := 1145553773993387600265017

theorem tailTrace_2230958 : CollatzResearch.WordTrace tailWord_2230958 prefixEnd_2230958 1145553773993387600265017 := by
  unfold tailWord_2230958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10171215381453457267146691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54246482034418438758115685 10171215381453457267146691)
  ·
    refine ⟨15256823072180185900720037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10171215381453457267146691 15256823072180185900720037)
    ·
      refine ⟨2860654326033784856385007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15256823072180185900720037 2860654326033784856385007)
      ·
        refine ⟨4290981489050677284577511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2860654326033784856385007 4290981489050677284577511)
        ·
          refine ⟨6436472233576015926866267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290981489050677284577511 6436472233576015926866267)
          ·
            refine ⟨9654708350364023890299401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436472233576015926866267 9654708350364023890299401)
            ·
              refine ⟨7241031262773017917724551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9654708350364023890299401 7241031262773017917724551)
              ·
                refine ⟨10861546894159526876586827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241031262773017917724551 10861546894159526876586827)
                ·
                  refine ⟨16292320341239290314880241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10861546894159526876586827 16292320341239290314880241)
                  ·
                    refine ⟨12219240255929467736160181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16292320341239290314880241 12219240255929467736160181)
                    ·
                      refine ⟨1145553773993387600265017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12219240255929467736160181 1145553773993387600265017)
                      ·
                        rfl

theorem cell23_2230958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2230958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230958 prefixEnd_2230958 := by exact prefixLift 2230958
  have htrace : WordTrace (prefixWord ++ tailWord_2230958) baseStart_2230958 baseEnd_2230958 := by
    simpa [prefixWord, tailWord_2230958, baseEnd_2230958] using wordTrace_append hprefix tailTrace_2230958
  have hstable : (prefixWord ++ tailWord_2230958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230958).length < 2 ^ (prefixWord ++ tailWord_2230958).sum := by decide
  have hdescent : baseEnd_2230958 < baseStart_2230958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230988 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2230988 : Nat := 118140960795 + 2230988 * 2 ^ 59
def prefixEnd_2230988 : Nat := 4983230072969 + 3 ^ 40 * 2230988 * 2
def baseEnd_2230988 : Nat := 1145569178413022482889879

theorem tailTrace_2230988 : CollatzResearch.WordTrace tailWord_2230988 prefixEnd_2230988 1145569178413022482889879 := by
  unfold tailWord_2230988
  simp only [CollatzResearch.WordTrace]
  refine ⟨40685408620759486630382809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54247211494345982173843745 40685408620759486630382809)
  ·
    refine ⟨30514056465569614972787107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40685408620759486630382809 30514056465569614972787107)
    ·
      refine ⟨45771084698354422459180661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30514056465569614972787107 45771084698354422459180661)
      ·
        refine ⟨4291039190470727105548187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45771084698354422459180661 4291039190470727105548187)
        ·
          refine ⟨6436558785706090658322281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291039190470727105548187 6436558785706090658322281)
          ·
            refine ⟨4827419089279567993741711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6436558785706090658322281 4827419089279567993741711)
            ·
              refine ⟨7241128633919351990612567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827419089279567993741711 7241128633919351990612567)
              ·
                refine ⟨10861692950879027985918851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241128633919351990612567 10861692950879027985918851)
                ·
                  refine ⟨16292539426318541978878277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10861692950879027985918851 16292539426318541978878277)
                  ·
                    refine ⟨3054851142434726621039677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16292539426318541978878277 3054851142434726621039677)
                    ·
                      refine ⟨1145569178413022482889879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054851142434726621039677 1145569178413022482889879)
                      ·
                        rfl

theorem cell23_2230988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2230988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2230988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2230988 prefixEnd_2230988 := by exact prefixLift 2230988
  have htrace : WordTrace (prefixWord ++ tailWord_2230988) baseStart_2230988 baseEnd_2230988 := by
    simpa [prefixWord, tailWord_2230988, baseEnd_2230988] using wordTrace_append hprefix tailTrace_2230988
  have hstable : (prefixWord ++ tailWord_2230988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230988).length < 2 ^ (prefixWord ++ tailWord_2230988).sum := by decide
  have hdescent : baseEnd_2230988 < baseStart_2230988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231011 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2231011 : Nat := 118140960795 + 2231011 * 2 ^ 59
def prefixEnd_2231011 : Nat := 4983230072969 + 3 ^ 40 * 2231011 * 2
def baseEnd_2231011 : Nat := 1145580988468075892902273

theorem tailTrace_2231011 : CollatzResearch.WordTrace tailWord_2231011 prefixEnd_2231011 1145580988468075892902273 := by
  unfold tailWord_2231011
  simp only [CollatzResearch.WordTrace]
  refine ⟨81371656120435648188852887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54247770746957098792568591 81371656120435648188852887)
  ·
    refine ⟨122057484180653472283279331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81371656120435648188852887 122057484180653472283279331)
    ·
      refine ⟨183086226270980208424918997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122057484180653472283279331 183086226270980208424918997)
      ·
        refine ⟨4291083428226098634959039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 183086226270980208424918997 4291083428226098634959039)
        ·
          refine ⟨6436625142339147952438559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291083428226098634959039 6436625142339147952438559)
          ·
            refine ⟨9654937713508721928657839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436625142339147952438559 9654937713508721928657839)
            ·
              refine ⟨14482406570263082892986759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654937713508721928657839 14482406570263082892986759)
              ·
                refine ⟨21723609855394624339480139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14482406570263082892986759 21723609855394624339480139)
                ·
                  refine ⟨32585414783091936509220209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21723609855394624339480139 32585414783091936509220209)
                  ·
                    refine ⟨24439061087318952381915157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32585414783091936509220209 24439061087318952381915157)
                    ·
                      refine ⟨1145580988468075892902273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24439061087318952381915157 1145580988468075892902273)
                      ·
                        rfl

theorem cell23_2231011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2231011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231011 prefixEnd_2231011 := by exact prefixLift 2231011
  have htrace : WordTrace (prefixWord ++ tailWord_2231011) baseStart_2231011 baseEnd_2231011 := by
    simpa [prefixWord, tailWord_2231011, baseEnd_2231011] using wordTrace_append hprefix tailTrace_2231011
  have hstable : (prefixWord ++ tailWord_2231011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231011).length < 2 ^ (prefixWord ++ tailWord_2231011).sum := by decide
  have hdescent : baseEnd_2231011 < baseStart_2231011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231068 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2231068 : Nat := 118140960795 + 2231068 * 2 ^ 59
def prefixEnd_2231068 : Nat := 4983230072969 + 3 ^ 40 * 2231068 * 2
def baseEnd_2231068 : Nat := 381870085621794056629837

theorem tailTrace_2231068 : CollatzResearch.WordTrace tailWord_2231068 prefixEnd_2231068 381870085621794056629837 := by
  unfold tailWord_2231068
  simp only [CollatzResearch.WordTrace]
  refine ⟨40686867540614573461838929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54249156720819431282451905 40686867540614573461838929)
  ·
    refine ⟨30515150655460930096379197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40686867540614573461838929 30515150655460930096379197)
    ·
      refine ⟨11443181495797848786142199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30515150655460930096379197 11443181495797848786142199)
      ·
        refine ⟨17164772243696773179213299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443181495797848786142199 17164772243696773179213299)
        ·
          refine ⟨25747158365545159768819949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164772243696773179213299 25747158365545159768819949)
          ·
            refine ⟨9655184387079434913307481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25747158365545159768819949 9655184387079434913307481)
            ·
              refine ⟨7241388290309576184980611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9655184387079434913307481 7241388290309576184980611)
              ·
                refine ⟨10862082435464364277470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241388290309576184980611 10862082435464364277470917)
                ·
                  refine ⟨2036640456649568302025797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10862082435464364277470917 2036640456649568302025797)
                  ·
                    refine ⟨381870085621794056629837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036640456649568302025797 381870085621794056629837)
                    ·
                      rfl

theorem cell23_2231068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2231068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231068 prefixEnd_2231068 := by exact prefixLift 2231068
  have htrace : WordTrace (prefixWord ++ tailWord_2231068) baseStart_2231068 baseEnd_2231068 := by
    simpa [prefixWord, tailWord_2231068, baseEnd_2231068] using wordTrace_append hprefix tailTrace_2231068
  have hstable : (prefixWord ++ tailWord_2231068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231068).length < 2 ^ (prefixWord ++ tailWord_2231068).sum := by decide
  have hdescent : baseEnd_2231068 < baseStart_2231068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231069 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2231069 : Nat := 118140960795 + 2231069 * 2 ^ 59
def prefixEnd_2231069 : Nat := 4983230072969 + 3 ^ 40 * 2231069 * 2
def baseEnd_2231069 : Nat := 1145610770346036665977007

theorem tailTrace_2231069 : CollatzResearch.WordTrace tailWord_2231069 prefixEnd_2231069 1145610770346036665977007 := by
  unfold tailWord_2231069
  simp only [CollatzResearch.WordTrace]
  refine ⟨81373771554225524094464261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54249181036150349396309507 81373771554225524094464261)
  ·
    refine ⟨15257582166417285767712049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81373771554225524094464261 15257582166417285767712049)
    ·
      refine ⟨11443186624812964325784037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15257582166417285767712049 11443186624812964325784037)
      ·
        refine ⟨2145597492152430811084507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11443186624812964325784037 2145597492152430811084507)
        ·
          refine ⟨3218396238228646216626761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145597492152430811084507 3218396238228646216626761)
          ·
            refine ⟨2413797178671484662470071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218396238228646216626761 2413797178671484662470071)
            ·
              refine ⟨3620695768007226993705107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413797178671484662470071 3620695768007226993705107)
              ·
                refine ⟨5431043652010840490557661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620695768007226993705107 5431043652010840490557661)
                ·
                  refine ⟨2036641369504065183959123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5431043652010840490557661 2036641369504065183959123)
                  ·
                    refine ⟨3054962054256097775938685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036641369504065183959123 3054962054256097775938685)
                    ·
                      refine ⟨1145610770346036665977007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3054962054256097775938685 1145610770346036665977007)
                      ·
                        rfl

theorem cell23_2231069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2231069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231069 prefixEnd_2231069 := by exact prefixLift 2231069
  have htrace : WordTrace (prefixWord ++ tailWord_2231069) baseStart_2231069 baseEnd_2231069 := by
    simpa [prefixWord, tailWord_2231069, baseEnd_2231069] using wordTrace_append hprefix tailTrace_2231069
  have hstable : (prefixWord ++ tailWord_2231069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231069).length < 2 ^ (prefixWord ++ tailWord_2231069).sum := by decide
  have hdescent : baseEnd_2231069 < baseStart_2231069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231071 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2231071 : Nat := 118140960795 + 2231071 * 2 ^ 59
def prefixEnd_2231071 : Nat := 4983230072969 + 3 ^ 40 * 2231071 * 2
def baseEnd_2231071 : Nat := 1145611797307345658151997

theorem tailTrace_2231071 : CollatzResearch.WordTrace tailWord_2231071 prefixEnd_2231071 1145611797307345658151997 := by
  unfold tailWord_2231071
  simp only [CollatzResearch.WordTrace]
  refine ⟨81373844500218278436037067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54249229666812185624024711 81373844500218278436037067)
  ·
    refine ⟨122060766750327417654055601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81373844500218278436037067 122060766750327417654055601)
    ·
      refine ⟨91545575062745563240541701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122060766750327417654055601 91545575062745563240541701)
      ·
        refine ⟨17164795324264793107601569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91545575062745563240541701 17164795324264793107601569)
        ·
          refine ⟨12873596493198594830701177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17164795324264793107601569 12873596493198594830701177)
          ·
            refine ⟨9655197369898946123025883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12873596493198594830701177 9655197369898946123025883)
            ·
              refine ⟨14482796054848419184538825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655197369898946123025883 14482796054848419184538825)
              ·
                refine ⟨10862097041136314388404119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14482796054848419184538825 10862097041136314388404119)
                ·
                  refine ⟨16293145561704471582606179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10862097041136314388404119 16293145561704471582606179)
                  ·
                    refine ⟨24439718342556707373909269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16293145561704471582606179 24439718342556707373909269)
                    ·
                      refine ⟨1145611797307345658151997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24439718342556707373909269 1145611797307345658151997)
                      ·
                        rfl

theorem cell23_2231071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2231071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231071 prefixEnd_2231071 := by exact prefixLift 2231071
  have htrace : WordTrace (prefixWord ++ tailWord_2231071) baseStart_2231071 baseEnd_2231071 := by
    simpa [prefixWord, tailWord_2231071, baseEnd_2231071] using wordTrace_append hprefix tailTrace_2231071
  have hstable : (prefixWord ++ tailWord_2231071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231071).length < 2 ^ (prefixWord ++ tailWord_2231071).sum := by decide
  have hdescent : baseEnd_2231071 < baseStart_2231071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231141 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2231141 : Nat := 118140960795 + 2231141 * 2 ^ 59
def prefixEnd_2231141 : Nat := 4983230072969 + 3 ^ 40 * 2231141 * 2
def baseEnd_2231141 : Nat := 381882580317720128092225

theorem tailTrace_2231141 : CollatzResearch.WordTrace tailWord_2231141 prefixEnd_2231141 381882580317720128092225 := by
  unfold tailWord_2231141
  simp only [CollatzResearch.WordTrace]
  refine ⟨81376397609964680391085277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54250931739976453594056851 81376397609964680391085277)
  ·
    refine ⟨30516149103736755146656979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81376397609964680391085277 30516149103736755146656979)
    ·
      refine ⟨45774223655605132719985469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30516149103736755146656979 45774223655605132719985469)
      ·
        refine ⟨17165333870851924769994551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45774223655605132719985469 17165333870851924769994551)
        ·
          refine ⟨25748000806277887154991827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165333870851924769994551 25748000806277887154991827)
          ·
            refine ⟨38622001209416830732487741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25748000806277887154991827 38622001209416830732487741)
            ·
              refine ⟨14483250453531311524682903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38622001209416830732487741 14483250453531311524682903)
              ·
                refine ⟨21724875680296967287024355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14483250453531311524682903 21724875680296967287024355)
                ·
                  refine ⟨32587313520445450930536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21724875680296967287024355 32587313520445450930536533)
                  ·
                    refine ⟨381882580317720128092225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32587313520445450930536533 381882580317720128092225)
                    ·
                      rfl

theorem cell23_2231141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2231141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231141 prefixEnd_2231141 := by exact prefixLift 2231141
  have htrace : WordTrace (prefixWord ++ tailWord_2231141) baseStart_2231141 baseEnd_2231141 := by
    simpa [prefixWord, tailWord_2231141, baseEnd_2231141] using wordTrace_append hprefix tailTrace_2231141
  have hstable : (prefixWord ++ tailWord_2231141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231141).length < 2 ^ (prefixWord ++ tailWord_2231141).sum := by decide
  have hdescent : baseEnd_2231141 < baseStart_2231141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_2231151 : Nat := 118140960795 + 2231151 * 2 ^ 59
def prefixEnd_2231151 : Nat := 4983230072969 + 3 ^ 40 * 2231151 * 2
def baseEnd_2231151 : Nat := 1145652875759705345151629

theorem tailTrace_2231151 : CollatzResearch.WordTrace tailWord_2231151 prefixEnd_2231151 1145652875759705345151629 := by
  unfold tailWord_2231151
  simp only [CollatzResearch.WordTrace]
  refine ⟨81376762339928452098949307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54251174893285634732632871 81376762339928452098949307)
  ·
    refine ⟨122065143509892678148423961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81376762339928452098949307 122065143509892678148423961)
    ·
      refine ⟨91548857632419508611317971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122065143509892678148423961 91548857632419508611317971)
      ·
        refine ⟨137323286448629262916976957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91548857632419508611317971 137323286448629262916976957)
        ·
          refine ⟨51496232418235973593866359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137323286448629262916976957 51496232418235973593866359)
          ·
            refine ⟨77244348627353960390799539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51496232418235973593866359 77244348627353960390799539)
            ·
              refine ⟨115866522941030940586199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77244348627353960390799539 115866522941030940586199309)
              ·
                refine ⟨43449946102886602719824741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115866522941030940586199309 43449946102886602719824741)
                ·
                  refine ⟨8146864894291238009967139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43449946102886602719824741 8146864894291238009967139)
                  ·
                    refine ⟨12220297341436857014950709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8146864894291238009967139 12220297341436857014950709)
                    ·
                      refine ⟨1145652875759705345151629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12220297341436857014950709 1145652875759705345151629)
                      ·
                        rfl

theorem cell23_2231151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_2231151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231151 prefixEnd_2231151 := by exact prefixLift 2231151
  have htrace : WordTrace (prefixWord ++ tailWord_2231151) baseStart_2231151 baseEnd_2231151 := by
    simpa [prefixWord, tailWord_2231151, baseEnd_2231151] using wordTrace_append hprefix tailTrace_2231151
  have hstable : (prefixWord ++ tailWord_2231151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231151).length < 2 ^ (prefixWord ++ tailWord_2231151).sum := by decide
  have hdescent : baseEnd_2231151 < baseStart_2231151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231165 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_2231165 : Nat := 118140960795 + 2231165 * 2 ^ 59
def prefixEnd_2231165 : Nat := 4983230072969 + 3 ^ 40 * 2231165 * 2
def baseEnd_2231165 : Nat := 1145660064488868290376565

theorem tailTrace_2231165 : CollatzResearch.WordTrace tailWord_2231165 prefixEnd_2231165 1145660064488868290376565 := by
  unfold tailWord_2231165
  simp only [CollatzResearch.WordTrace]
  refine ⟨81377272961877732489958949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54251515307918488326639299 81377272961877732489958949)
  ·
    refine ⟨15258238680352074841867303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81377272961877732489958949 15258238680352074841867303)
    ·
      refine ⟨22887358020528112262800955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15258238680352074841867303 22887358020528112262800955)
      ·
        refine ⟨34331037030792168394201433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22887358020528112262800955 34331037030792168394201433)
        ·
          refine ⟨25748277773094126295651075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34331037030792168394201433 25748277773094126295651075)
          ·
            refine ⟨38622416659641189443476613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25748277773094126295651075 38622416659641189443476613)
            ·
              refine ⟨7241703123682723020651865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38622416659641189443476613 7241703123682723020651865)
              ·
                refine ⟨5431277342762042265488899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7241703123682723020651865 5431277342762042265488899)
                ·
                  refine ⟨8146916014143063398233349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431277342762042265488899 8146916014143063398233349)
                  ·
                    refine ⟨1527546752651824387168753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8146916014143063398233349 1527546752651824387168753)
                    ·
                      refine ⟨1145660064488868290376565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527546752651824387168753 1145660064488868290376565)
                      ·
                        rfl

theorem cell23_2231165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_2231165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231165 prefixEnd_2231165 := by exact prefixLift 2231165
  have htrace : WordTrace (prefixWord ++ tailWord_2231165) baseStart_2231165 baseEnd_2231165 := by
    simpa [prefixWord, tailWord_2231165, baseEnd_2231165] using wordTrace_append hprefix tailTrace_2231165
  have hstable : (prefixWord ++ tailWord_2231165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231165).length < 2 ^ (prefixWord ++ tailWord_2231165).sum := by decide
  have hdescent : baseEnd_2231165 < baseStart_2231165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231171 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 9]
def baseStart_2231171 : Nat := 118140960795 + 2231171 * 2 ^ 59
def prefixEnd_2231171 : Nat := 4983230072969 + 3 ^ 40 * 2231171 * 2
def baseEnd_2231171 : Nat := 127295905041421696322393

theorem tailTrace_2231171 : CollatzResearch.WordTrace tailWord_2231171 prefixEnd_2231171 127295905041421696322393 := by
  unfold tailWord_2231171
  simp only [CollatzResearch.WordTrace]
  refine ⟨81377491799855995514677367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54251661199903997009784911 81377491799855995514677367)
  ·
    refine ⟨122066237699783993272016051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81377491799855995514677367 122066237699783993272016051)
    ·
      refine ⟨183099356549675989908024077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122066237699783993272016051 183099356549675989908024077)
      ·
        refine ⟨68662258706128496215509029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183099356549675989908024077 68662258706128496215509029)
        ·
          refine ⟨12874173507399093040407943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68662258706128496215509029 12874173507399093040407943)
          ·
            refine ⟨19311260261098639560611915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12874173507399093040407943 19311260261098639560611915)
            ·
              refine ⟨28966890391647959340917873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19311260261098639560611915 28966890391647959340917873)
              ·
                refine ⟨21725167793735969505688405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28966890391647959340917873 21725167793735969505688405)
                ·
                  refine ⟨127295905041421696322393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21725167793735969505688405 127295905041421696322393)
                  ·
                    rfl

theorem cell23_2231171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 9].length) (baseStart_2231171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231171 prefixEnd_2231171 := by exact prefixLift 2231171
  have htrace : WordTrace (prefixWord ++ tailWord_2231171) baseStart_2231171 baseEnd_2231171 := by
    simpa [prefixWord, tailWord_2231171, baseEnd_2231171] using wordTrace_append hprefix tailTrace_2231171
  have hstable : (prefixWord ++ tailWord_2231171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231171).length < 2 ^ (prefixWord ++ tailWord_2231171).sum := by decide
  have hdescent : baseEnd_2231171 < baseStart_2231171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231211 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_2231211 : Nat := 118140960795 + 2231211 * 2 ^ 59
def prefixEnd_2231211 : Nat := 4983230072969 + 3 ^ 40 * 2231211 * 2
def baseEnd_2231211 : Nat := 1145683684598975110401353

theorem tailTrace_2231211 : CollatzResearch.WordTrace tailWord_2231211 prefixEnd_2231211 1145683684598975110401353 := by
  unfold tailWord_2231211
  simp only [CollatzResearch.WordTrace]
  refine ⟨81378950719711082346133487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54252633813140721564088991 81378950719711082346133487)
  ·
    refine ⟨122068426079566623519200231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81378950719711082346133487 122068426079566623519200231)
    ·
      refine ⟨183102639119349935278800347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122068426079566623519200231 183102639119349935278800347)
      ·
        refine ⟨274653958679024902918200521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183102639119349935278800347 274653958679024902918200521)
        ·
          refine ⟨205990469009268677188650391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274653958679024902918200521 205990469009268677188650391)
          ·
            refine ⟨308985703513903015782975587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205990469009268677188650391 308985703513903015782975587)
            ·
              refine ⟨463478555270854523674463381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308985703513903015782975587 463478555270854523674463381)
              ·
                refine ⟨21725557278321305797240471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463478555270854523674463381 21725557278321305797240471)
                ·
                  refine ⟨32588335917481958695860707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21725557278321305797240471 32588335917481958695860707)
                  ·
                    refine ⟨48882503876222938043791061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32588335917481958695860707 48882503876222938043791061)
                    ·
                      refine ⟨1145683684598975110401353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48882503876222938043791061 1145683684598975110401353)
                      ·
                        rfl

theorem cell23_2231211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_2231211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231211 prefixEnd_2231211 := by exact prefixLift 2231211
  have htrace : WordTrace (prefixWord ++ tailWord_2231211) baseStart_2231211 baseEnd_2231211 := by
    simpa [prefixWord, tailWord_2231211, baseEnd_2231211] using wordTrace_append hprefix tailTrace_2231211
  have hstable : (prefixWord ++ tailWord_2231211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231211).length < 2 ^ (prefixWord ++ tailWord_2231211).sum := by decide
  have hdescent : baseEnd_2231211 < baseStart_2231211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231305 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_2231305 : Nat := 118140960795 + 2231305 * 2 ^ 59
def prefixEnd_2231305 : Nat := 4983230072969 + 3 ^ 40 * 2231305 * 2
def baseEnd_2231305 : Nat := 1145731951780497742625921

theorem tailTrace_2231305 : CollatzResearch.WordTrace tailWord_2231305 prefixEnd_2231305 1145731951780497742625921 := by
  unfold tailWord_2231305
  simp only [CollatzResearch.WordTrace]
  refine ⟨81382379181370536400055369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54254919454247024266703579 81382379181370536400055369)
  ·
    refine ⟨61036784386027902300041527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81382379181370536400055369 61036784386027902300041527)
    ·
      refine ⟨91555176579041853450062291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61036784386027902300041527 91555176579041853450062291)
      ·
        refine ⟨137332764868562780175093437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91555176579041853450062291 137332764868562780175093437)
        ·
          refine ⟨51499786825711042565660039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137332764868562780175093437 51499786825711042565660039)
          ·
            refine ⟨77249680238566563848490059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51499786825711042565660039 77249680238566563848490059)
            ·
              refine ⟨115874520357849845772735089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77249680238566563848490059 115874520357849845772735089)
              ·
                refine ⟨86905890268387384329551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115874520357849845772735089 86905890268387384329551317)
                ·
                  refine ⟨2036856803165329320223859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86905890268387384329551317 2036856803165329320223859)
                  ·
                    refine ⟨3055285204747993980335789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036856803165329320223859 3055285204747993980335789)
                    ·
                      refine ⟨1145731951780497742625921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055285204747993980335789 1145731951780497742625921)
                      ·
                        rfl

theorem cell23_2231305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_2231305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231305 prefixEnd_2231305 := by exact prefixLift 2231305
  have htrace : WordTrace (prefixWord ++ tailWord_2231305) baseStart_2231305 baseEnd_2231305 := by
    simpa [prefixWord, tailWord_2231305, baseEnd_2231305] using wordTrace_append hprefix tailTrace_2231305
  have hstable : (prefixWord ++ tailWord_2231305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231305).length < 2 ^ (prefixWord ++ tailWord_2231305).sum := by decide
  have hdescent : baseEnd_2231305 < baseStart_2231305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231315 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 5, 2]
def baseStart_2231315 : Nat := 118140960795 + 2231315 * 2 ^ 59
def prefixEnd_2231315 : Nat := 4983230072969 + 3 ^ 40 * 2231315 * 2
def baseEnd_2231315 : Nat := 1145737086587042703500875

theorem tailTrace_2231315 : CollatzResearch.WordTrace tailWord_2231315 prefixEnd_2231315 1145737086587042703500875 := by
  unfold tailWord_2231315
  simp only [CollatzResearch.WordTrace]
  refine ⟨81382743911334308107919399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54255162607556205405279599 81382743911334308107919399)
  ·
    refine ⟨122074115867001462161879099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81382743911334308107919399 122074115867001462161879099)
    ·
      refine ⟨183111173800502193242818649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122074115867001462161879099 183111173800502193242818649)
      ·
        refine ⟨137333380350376644932113987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183111173800502193242818649 137333380350376644932113987)
        ·
          refine ⟨206000070525564967398170981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137333380350376644932113987 206000070525564967398170981)
          ·
            refine ⟨38625013223543431387157059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206000070525564967398170981 38625013223543431387157059)
            ·
              refine ⟨57937519835315147080735589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38625013223543431387157059 57937519835315147080735589)
              ·
                refine ⟨10863284969121590077637923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57937519835315147080735589 10863284969121590077637923)
                ·
                  refine ⟨16294927453682385116456885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10863284969121590077637923 16294927453682385116456885)
                  ·
                    refine ⟨1527649448782723604667833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16294927453682385116456885 1527649448782723604667833)
                    ·
                      refine ⟨1145737086587042703500875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527649448782723604667833 1145737086587042703500875)
                      ·
                        rfl

theorem cell23_2231315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5, 2].length) (baseStart_2231315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231315 prefixEnd_2231315 := by exact prefixLift 2231315
  have htrace : WordTrace (prefixWord ++ tailWord_2231315) baseStart_2231315 baseEnd_2231315 := by
    simpa [prefixWord, tailWord_2231315, baseEnd_2231315] using wordTrace_append hprefix tailTrace_2231315
  have hstable : (prefixWord ++ tailWord_2231315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231315).length < 2 ^ (prefixWord ++ tailWord_2231315).sum := by decide
  have hdescent : baseEnd_2231315 < baseStart_2231315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231322 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_2231322 : Nat := 118140960795 + 2231322 * 2 ^ 59
def prefixEnd_2231322 : Nat := 4983230072969 + 3 ^ 40 * 2231322 * 2
def baseEnd_2231322 : Nat := 1145740680951624176113343

theorem tailTrace_2231322 : CollatzResearch.WordTrace tailWord_2231322 prefixEnd_2231322 1145740680951624176113343 := by
  unfold tailWord_2231322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20345749805577237075856055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54255332814872632202282813 20345749805577237075856055)
  ·
    refine ⟨30518624708365855613784083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20345749805577237075856055 30518624708365855613784083)
    ·
      refine ⟨45777937062548783420676125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30518624708365855613784083 45777937062548783420676125)
      ·
        refine ⟨17166726398455793782753547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45777937062548783420676125 17166726398455793782753547)
        ·
          refine ⟨25750089597683690674130321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17166726398455793782753547 25750089597683690674130321)
          ·
            refine ⟨19312567198262768005597741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25750089597683690674130321 19312567198262768005597741)
            ·
              refine ⟨7242212699348538002099153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19312567198262768005597741 7242212699348538002099153)
              ·
                refine ⟨5431659524511403501574365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242212699348538002099153 5431659524511403501574365)
                ·
                  refine ⟨2036872321691776313090387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5431659524511403501574365 2036872321691776313090387)
                  ·
                    refine ⟨3055308482537664469635581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036872321691776313090387 3055308482537664469635581)
                    ·
                      refine ⟨1145740680951624176113343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055308482537664469635581 1145740680951624176113343)
                      ·
                        rfl

theorem cell23_2231322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_2231322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231322 prefixEnd_2231322 := by exact prefixLift 2231322
  have htrace : WordTrace (prefixWord ++ tailWord_2231322) baseStart_2231322 baseEnd_2231322 := by
    simpa [prefixWord, tailWord_2231322, baseEnd_2231322] using wordTrace_append hprefix tailTrace_2231322
  have hstable : (prefixWord ++ tailWord_2231322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231322).length < 2 ^ (prefixWord ++ tailWord_2231322).sum := by decide
  have hdescent : baseEnd_2231322 < baseStart_2231322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231339 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 1, 1, 3]
def baseStart_2231339 : Nat := 118140960795 + 2231339 * 2 ^ 59
def prefixEnd_2231339 : Nat := 4983230072969 + 3 ^ 40 * 2231339 * 2
def baseEnd_2231339 : Nat := 1145749410122750609600765

theorem tailTrace_2231339 : CollatzResearch.WordTrace tailWord_2231339 prefixEnd_2231339 1145749410122750609600765 := by
  unfold tailWord_2231339
  simp only [CollatzResearch.WordTrace]
  refine ⟨81383619263247360206793071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54255746175498240137862047 81383619263247360206793071)
  ·
    refine ⟨122075428894871040310189607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81383619263247360206793071 122075428894871040310189607)
    ·
      refine ⟨183113143342306560465284411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122075428894871040310189607 183113143342306560465284411)
      ·
        refine ⟨274669715013459840697926617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183113143342306560465284411 274669715013459840697926617)
        ·
          refine ⟨206002286260094880523444963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274669715013459840697926617 206002286260094880523444963)
          ·
            refine ⟨309003429390142320785167445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206002286260094880523444963 309003429390142320785167445)
            ·
              refine ⟨3621133938165730321701181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 309003429390142320785167445 3621133938165730321701181)
              ·
                refine ⟨1357925226812148870637943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3621133938165730321701181 1357925226812148870637943)
                ·
                  refine ⟨2036887840218223305956915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357925226812148870637943 2036887840218223305956915)
                  ·
                    refine ⟨3055331760327334958935373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036887840218223305956915 3055331760327334958935373)
                    ·
                      refine ⟨1145749410122750609600765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055331760327334958935373 1145749410122750609600765)
                      ·
                        rfl

theorem cell23_2231339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 1, 3].length) (baseStart_2231339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231339 prefixEnd_2231339 := by exact prefixLift 2231339
  have htrace : WordTrace (prefixWord ++ tailWord_2231339) baseStart_2231339 baseEnd_2231339 := by
    simpa [prefixWord, tailWord_2231339, baseEnd_2231339] using wordTrace_append hprefix tailTrace_2231339
  have hstable : (prefixWord ++ tailWord_2231339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231339).length < 2 ^ (prefixWord ++ tailWord_2231339).sum := by decide
  have hdescent : baseEnd_2231339 < baseStart_2231339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231342 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2231342 : Nat := 118140960795 + 2231342 * 2 ^ 59
def prefixEnd_2231342 : Nat := 4983230072969 + 3 ^ 40 * 2231342 * 2
def baseEnd_2231342 : Nat := 381916983521571365954417

theorem tailTrace_2231342 : CollatzResearch.WordTrace tailWord_2231342 prefixEnd_2231342 381916983521571365954417 := by
  unfold tailWord_2231342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172966085279561464894035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54255819121490994479434853 10172966085279561464894035)
  ·
    refine ⟨15259449127919342197341053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10172966085279561464894035 15259449127919342197341053)
    ·
      refine ⟨5722293422969753324002895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15259449127919342197341053 5722293422969753324002895)
      ·
        refine ⟨8583440134454629986004343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5722293422969753324002895 8583440134454629986004343)
        ·
          refine ⟨12875160201681944979006515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8583440134454629986004343 12875160201681944979006515)
          ·
            refine ⟨19312740302522917468509773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12875160201681944979006515 19312740302522917468509773)
            ·
              refine ⟨7242277613446094050691165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19312740302522917468509773 7242277613446094050691165)
              ·
                refine ⟨2715854105042285269009187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7242277613446094050691165 2715854105042285269009187)
                ·
                  refine ⟨4073781157563427903513781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715854105042285269009187 4073781157563427903513781)
                  ·
                    refine ⟨381916983521571365954417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4073781157563427903513781 381916983521571365954417)
                    ·
                      rfl

theorem cell23_2231342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2231342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231342 prefixEnd_2231342 := by exact prefixLift 2231342
  have htrace : WordTrace (prefixWord ++ tailWord_2231342) baseStart_2231342 baseEnd_2231342 := by
    simpa [prefixWord, tailWord_2231342, baseEnd_2231342] using wordTrace_append hprefix tailTrace_2231342
  have hstable : (prefixWord ++ tailWord_2231342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231342).length < 2 ^ (prefixWord ++ tailWord_2231342).sum := by decide
  have hdescent : baseEnd_2231342 < baseStart_2231342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231365 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_2231365 : Nat := 118140960795 + 2231365 * 2 ^ 59
def prefixEnd_2231365 : Nat := 4983230072969 + 3 ^ 40 * 2231365 * 2
def baseEnd_2231365 : Nat := 1145762760619767507875645

theorem tailTrace_2231365 : CollatzResearch.WordTrace tailWord_2231365 prefixEnd_2231365 1145762760619767507875645 := by
  unfold tailWord_2231365
  simp only [CollatzResearch.WordTrace]
  refine ⟨81384567561153166647239549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54256378374102111098159699 81384567561153166647239549)
  ·
    refine ⟨30519212835432437492714831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81384567561153166647239549 30519212835432437492714831)
    ·
      refine ⟨45778819253148656239072247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30519212835432437492714831 45778819253148656239072247)
      ·
        refine ⟨68668228879722984358608371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45778819253148656239072247 68668228879722984358608371)
        ·
          refine ⟨103002343319584476537912557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68668228879722984358608371 103002343319584476537912557)
          ·
            refine ⟨38625878744844178701717209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103002343319584476537912557 38625878744844178701717209)
            ·
              refine ⟨28969409058633134026287907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38625878744844178701717209 28969409058633134026287907)
              ·
                refine ⟨43454113587949701039431861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28969409058633134026287907 43454113587949701039431861)
                ·
                  refine ⟨4073823148870284472446737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43454113587949701039431861 4073823148870284472446737)
                  ·
                    refine ⟨3055367361652713354335053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4073823148870284472446737 3055367361652713354335053)
                    ·
                      refine ⟨1145762760619767507875645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055367361652713354335053 1145762760619767507875645)
                      ·
                        rfl

theorem cell23_2231365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_2231365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231365 prefixEnd_2231365 := by exact prefixLift 2231365
  have htrace : WordTrace (prefixWord ++ tailWord_2231365) baseStart_2231365 baseEnd_2231365 := by
    simpa [prefixWord, tailWord_2231365, baseEnd_2231365] using wordTrace_append hprefix tailTrace_2231365
  have hstable : (prefixWord ++ tailWord_2231365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231365).length < 2 ^ (prefixWord ++ tailWord_2231365).sum := by decide
  have hdescent : baseEnd_2231365 < baseStart_2231365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231368 : List Nat := [2, 1, 3, 1, 1, 1, 4, 10]
def baseStart_2231368 : Nat := 118140960795 + 2231368 * 2 ^ 59
def prefixEnd_2231368 : Nat := 4983230072969 + 3 ^ 40 * 2231368 * 2
def baseEnd_2231368 : Nat := 42435714854138185042153

theorem tailTrace_2231368 : CollatzResearch.WordTrace tailWord_2231368 prefixEnd_2231368 42435714854138185042153 := by
  unfold tailWord_2231368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40692338490071149079799379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54256451320094865439732505 40692338490071149079799379)
  ·
    refine ⟨61038507735106723619699069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40692338490071149079799379 61038507735106723619699069)
    ·
      refine ⟨22889440400665021357387151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61038507735106723619699069 22889440400665021357387151)
      ·
        refine ⟨34334160600997532036080727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22889440400665021357387151 34334160600997532036080727)
        ·
          refine ⟨51501240901496298054121091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34334160600997532036080727 51501240901496298054121091)
          ·
            refine ⟨77251861352244447081181637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51501240901496298054121091 77251861352244447081181637)
            ·
              refine ⟨14484724003545833827721557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77251861352244447081181637 14484724003545833827721557)
              ·
                refine ⟨42435714854138185042153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14484724003545833827721557 42435714854138185042153)
                ·
                  rfl

theorem cell23_2231368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 10].length) (baseStart_2231368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231368 prefixEnd_2231368 := by exact prefixLift 2231368
  have htrace : WordTrace (prefixWord ++ tailWord_2231368) baseStart_2231368 baseEnd_2231368 := by
    simpa [prefixWord, tailWord_2231368, baseEnd_2231368] using wordTrace_append hprefix tailTrace_2231368
  have hstable : (prefixWord ++ tailWord_2231368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231368).length < 2 ^ (prefixWord ++ tailWord_2231368).sum := by decide
  have hdescent : baseEnd_2231368 < baseStart_2231368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231390 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2231390 : Nat := 118140960795 + 2231390 * 2 ^ 59
def prefixEnd_2231390 : Nat := 4983230072969 + 3 ^ 40 * 2231390 * 2
def baseEnd_2231390 : Nat := 1145775597636129910063031

theorem tailTrace_2231390 : CollatzResearch.WordTrace tailWord_2231390 prefixEnd_2231390 1145775597636129910063031 := by
  unfold tailWord_2231390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173184923257824489612453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54256986257375063944599749 10173184923257824489612453)
  ·
    refine ⟨1907472173110842091802335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10173184923257824489612453 1907472173110842091802335)
    ·
      refine ⟨2861208259666263137703503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907472173110842091802335 2861208259666263137703503)
      ·
        refine ⟨4291812389499394706555255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861208259666263137703503 4291812389499394706555255)
        ·
          refine ⟨6437718584249092059832883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291812389499394706555255 6437718584249092059832883)
          ·
            refine ⟨9656577876373638089749325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437718584249092059832883 9656577876373638089749325)
            ·
              refine ⟨3621216703640114283655997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9656577876373638089749325 3621216703640114283655997)
              ·
                refine ⟨1357956263865042856370999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3621216703640114283655997 1357956263865042856370999)
                ·
                  refine ⟨2036934395797564284556499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357956263865042856370999 2036934395797564284556499)
                  ·
                    refine ⟨3055401593696346426834749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2036934395797564284556499 3055401593696346426834749)
                    ·
                      refine ⟨1145775597636129910063031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055401593696346426834749 1145775597636129910063031)
                      ·
                        rfl

theorem cell23_2231390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2231390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231390 prefixEnd_2231390 := by exact prefixLift 2231390
  have htrace : WordTrace (prefixWord ++ tailWord_2231390) baseStart_2231390 baseEnd_2231390 := by
    simpa [prefixWord, tailWord_2231390, baseEnd_2231390] using wordTrace_append hprefix tailTrace_2231390
  have hstable : (prefixWord ++ tailWord_2231390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231390).length < 2 ^ (prefixWord ++ tailWord_2231390).sum := by decide
  have hdescent : baseEnd_2231390 < baseStart_2231390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231395 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2231395 : Nat := 118140960795 + 2231395 * 2 ^ 59
def prefixEnd_2231395 : Nat := 4983230072969 + 3 ^ 40 * 2231395 * 2
def baseEnd_2231395 : Nat := 1145778165039402390500507

theorem tailTrace_2231395 : CollatzResearch.WordTrace tailWord_2231395 prefixEnd_2231395 1145778165039402390500507 := by
  unfold tailWord_2231395
  simp only [CollatzResearch.WordTrace]
  refine ⟨81385661751044481770831639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54257107834029654513887759 81385661751044481770831639)
  ·
    refine ⟨122078492626566722656247459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81385661751044481770831639 122078492626566722656247459)
    ·
      refine ⟨183117738939850083984371189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122078492626566722656247459 183117738939850083984371189)
      ·
        refine ⟨17167288025610945373534799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183117738939850083984371189 17167288025610945373534799)
        ·
          refine ⟨25750932038416418060302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17167288025610945373534799 25750932038416418060302199)
          ·
            refine ⟨38626398057624627090453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25750932038416418060302199 38626398057624627090453299)
            ·
              refine ⟨57939597086436940635679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38626398057624627090453299 57939597086436940635679949)
              ·
                refine ⟨21727348907413852738379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57939597086436940635679949 21727348907413852738379981)
                ·
                  refine ⟨8147755840280194776892493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21727348907413852738379981 8147755840280194776892493)
                  ·
                    refine ⟨3055408440105073041334685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8147755840280194776892493 3055408440105073041334685)
                    ·
                      refine ⟨1145778165039402390500507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055408440105073041334685 1145778165039402390500507)
                      ·
                        rfl

theorem cell23_2231395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2231395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231395 prefixEnd_2231395 := by exact prefixLift 2231395
  have htrace : WordTrace (prefixWord ++ tailWord_2231395) baseStart_2231395 baseEnd_2231395 := by
    simpa [prefixWord, tailWord_2231395, baseEnd_2231395] using wordTrace_append hprefix tailTrace_2231395
  have hstable : (prefixWord ++ tailWord_2231395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231395).length < 2 ^ (prefixWord ++ tailWord_2231395).sum := by decide
  have hdescent : baseEnd_2231395 < baseStart_2231395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231456 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2]
def baseStart_2231456 : Nat := 118140960795 + 2231456 * 2 ^ 59
def prefixEnd_2231456 : Nat := 4983230072969 + 3 ^ 40 * 2231456 * 2
def baseEnd_2231456 : Nat := 1145809487359326651837727

theorem tailTrace_2231456 : CollatzResearch.WordTrace tailWord_2231456 prefixEnd_2231456 1145809487359326651837727 := by
  unfold tailWord_2231456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40693943301911744594401111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54258591069215659459201481 40693943301911744594401111)
  ·
    refine ⟨61040914952867616891601667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40693943301911744594401111 61040914952867616891601667)
    ·
      refine ⟨91561372429301425337402501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61040914952867616891601667 91561372429301425337402501)
      ·
        refine ⟨17167757330494017250762969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91561372429301425337402501 17167757330494017250762969)
        ·
          refine ⟨12875817997870512938072227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17167757330494017250762969 12875817997870512938072227)
          ·
            refine ⟨19313726996805769407108341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12875817997870512938072227 19313726996805769407108341)
            ·
              refine ⟨1810661905950540881916407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19313726996805769407108341 1810661905950540881916407)
              ·
                refine ⟨2715992858925811322874611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810661905950540881916407 2715992858925811322874611)
                ·
                  refine ⟨4073989288388716984311917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715992858925811322874611 4073989288388716984311917)
                  ·
                    refine ⟨1527745983145768869116969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4073989288388716984311917 1527745983145768869116969)
                    ·
                      refine ⟨1145809487359326651837727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527745983145768869116969 1145809487359326651837727)
                      ·
                        rfl

theorem cell23_2231456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_2231456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231456 prefixEnd_2231456 := by exact prefixLift 2231456
  have htrace : WordTrace (prefixWord ++ tailWord_2231456) baseStart_2231456 baseEnd_2231456 := by
    simpa [prefixWord, tailWord_2231456, baseEnd_2231456] using wordTrace_append hprefix tailTrace_2231456
  have hstable : (prefixWord ++ tailWord_2231456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231456).length < 2 ^ (prefixWord ++ tailWord_2231456).sum := by decide
  have hdescent : baseEnd_2231456 < baseStart_2231456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231486 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_2231486 : Nat := 118140960795 + 2231486 * 2 ^ 59
def prefixEnd_2231486 : Nat := 4983230072969 + 3 ^ 40 * 2231486 * 2
def baseEnd_2231486 : Nat := 1145824891778961534462589

theorem tailTrace_2231486 : CollatzResearch.WordTrace tailWord_2231486 prefixEnd_2231486 1145824891778961534462589 := by
  unfold tailWord_2231486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173622599214350539049289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54259320529143202874929541 10173622599214350539049289)
  ·
    refine ⟨7630216949410762904286967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10173622599214350539049289 7630216949410762904286967)
    ·
      refine ⟨11445325424116144356430451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630216949410762904286967 11445325424116144356430451)
      ·
        refine ⟨17167988136174216534645677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11445325424116144356430451 17167988136174216534645677)
        ·
          refine ⟨6437995551065331200492129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17167988136174216534645677 6437995551065331200492129)
          ·
            refine ⟨4828496663298998400369097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6437995551065331200492129 4828496663298998400369097)
            ·
              refine ⟨3621372497474248800276823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828496663298998400369097 3621372497474248800276823)
              ·
                refine ⟨5432058746211373200415235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621372497474248800276823 5432058746211373200415235)
                ·
                  refine ⟨8148088119317059800622853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432058746211373200415235 8148088119317059800622853)
                  ·
                    refine ⟨1527766522371948712616785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8148088119317059800622853 1527766522371948712616785)
                    ·
                      refine ⟨1145824891778961534462589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527766522371948712616785 1145824891778961534462589)
                      ·
                        rfl

theorem cell23_2231486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_2231486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231486 prefixEnd_2231486 := by exact prefixLift 2231486
  have htrace : WordTrace (prefixWord ++ tailWord_2231486) baseStart_2231486 baseEnd_2231486 := by
    simpa [prefixWord, tailWord_2231486, baseEnd_2231486] using wordTrace_append hprefix tailTrace_2231486
  have hstable : (prefixWord ++ tailWord_2231486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231486).length < 2 ^ (prefixWord ++ tailWord_2231486).sum := by decide
  have hdescent : baseEnd_2231486 < baseStart_2231486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231509 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 5]
def baseStart_2231509 : Nat := 118140960795 + 2231509 * 2 ^ 59
def prefixEnd_2231509 : Nat := 4983230072969 + 3 ^ 40 * 2231509 * 2
def baseEnd_2231509 : Nat := 127315189092668327163887

theorem tailTrace_2231509 : CollatzResearch.WordTrace tailWord_2231509 prefixEnd_2231509 127315189092668327163887 := by
  unfold tailWord_2231509
  simp only [CollatzResearch.WordTrace]
  refine ⟨81389819672631479240481581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54259879781754319493654387 81389819672631479240481581)
  ·
    refine ⟨30521182377236804715180593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81389819672631479240481581 30521182377236804715180593)
    ·
      refine ⟨22890886782927603536385445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30521182377236804715180593 22890886782927603536385445)
      ·
        refine ⟨4292041271798925663072271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22890886782927603536385445 4292041271798925663072271)
        ·
          refine ⟨6438061907698388494608407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292041271798925663072271 6438061907698388494608407)
          ·
            refine ⟨9657092861547582741912611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438061907698388494608407 9657092861547582741912611)
            ·
              refine ⟨14485639292321374112868917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657092861547582741912611 14485639292321374112868917)
              ·
                refine ⟨1358028683655128823081461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14485639292321374112868917 1358028683655128823081461)
                ·
                  refine ⟨127315189092668327163887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1358028683655128823081461 127315189092668327163887)
                  ·
                    rfl

theorem cell23_2231509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_2231509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231509 prefixEnd_2231509 := by exact prefixLift 2231509
  have htrace : WordTrace (prefixWord ++ tailWord_2231509) baseStart_2231509 baseEnd_2231509 := by
    simpa [prefixWord, tailWord_2231509, baseEnd_2231509] using wordTrace_append hprefix tailTrace_2231509
  have hstable : (prefixWord ++ tailWord_2231509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231509).length < 2 ^ (prefixWord ++ tailWord_2231509).sum := by decide
  have hdescent : baseEnd_2231509 < baseStart_2231509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231613 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2231613 : Nat := 118140960795 + 2231613 * 2 ^ 59
def prefixEnd_2231613 : Nat := 4983230072969 + 3 ^ 40 * 2231613 * 2
def baseEnd_2231613 : Nat := 1145890103822082537574505

theorem tailTrace_2231613 : CollatzResearch.WordTrace tailWord_2231613 prefixEnd_2231613 1145890103822082537574505 := by
  unfold tailWord_2231613
  simp only [CollatzResearch.WordTrace]
  refine ⟨81393612864254705002267493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54262408576169803334844995 81393612864254705002267493)
  ·
    refine ⟨15261302412047757187925155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81393612864254705002267493 15261302412047757187925155)
    ·
      refine ⟨22891953618071635781887733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15261302412047757187925155 22891953618071635781887733)
      ·
        refine ⟨2146120651694215854551975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22891953618071635781887733 2146120651694215854551975)
        ·
          refine ⟨3219180977541323781827963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146120651694215854551975 3219180977541323781827963)
          ·
            refine ⟨4828771466311985672741945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219180977541323781827963 4828771466311985672741945)
            ·
              refine ⟨3621578599733989254556459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828771466311985672741945 3621578599733989254556459)
              ·
                refine ⟨5432367899600983881834689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621578599733989254556459 5432367899600983881834689)
                ·
                  refine ⟨4074275924700737911376017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432367899600983881834689 4074275924700737911376017)
                  ·
                    refine ⟨3055706943525553433532013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074275924700737911376017 3055706943525553433532013)
                    ·
                      refine ⟨1145890103822082537574505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055706943525553433532013 1145890103822082537574505)
                      ·
                        rfl

theorem cell23_2231613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2231613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231613 prefixEnd_2231613 := by exact prefixLift 2231613
  have htrace : WordTrace (prefixWord ++ tailWord_2231613) baseStart_2231613 baseEnd_2231613 := by
    simpa [prefixWord, tailWord_2231613, baseEnd_2231613] using wordTrace_append hprefix tailTrace_2231613
  have hstable : (prefixWord ++ tailWord_2231613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231613).length < 2 ^ (prefixWord ++ tailWord_2231613).sum := by decide
  have hdescent : baseEnd_2231613 < baseStart_2231613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231636 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_2231636 : Nat := 118140960795 + 2231636 * 2 ^ 59
def prefixEnd_2231636 : Nat := 4983230072969 + 3 ^ 40 * 2231636 * 2
def baseEnd_2231636 : Nat := 1145901913877135947586899

theorem tailTrace_2231636 : CollatzResearch.WordTrace tailWord_2231636 prefixEnd_2231636 1145901913877135947586899 := by
  unfold tailWord_2231636
  simp only [CollatzResearch.WordTrace]
  refine ⟨40697225871585689965177381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54262967828780919953569841 40697225871585689965177381)
  ·
    refine ⟨7630729850922316868470759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40697225871585689965177381 7630729850922316868470759)
    ·
      refine ⟨11446094776383475302706139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630729850922316868470759 11446094776383475302706139)
      ·
        refine ⟨17169142164575212954059209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11446094776383475302706139 17169142164575212954059209)
        ·
          refine ⟨12876856623431409715544407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17169142164575212954059209 12876856623431409715544407)
          ·
            refine ⟨19315284935147114573316611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12876856623431409715544407 19315284935147114573316611)
            ·
              refine ⟨28972927402720671859974917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19315284935147114573316611 28972927402720671859974917)
              ·
                refine ⟨5432423888010125973745297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28972927402720671859974917 5432423888010125973745297)
                ·
                  refine ⟨4074317916007594480308973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432423888010125973745297 4074317916007594480308973)
                  ·
                    refine ⟨1527869218502847930115865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4074317916007594480308973 1527869218502847930115865)
                    ·
                      refine ⟨1145901913877135947586899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527869218502847930115865 1145901913877135947586899)
                      ·
                        rfl

theorem cell23_2231636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_2231636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231636 prefixEnd_2231636 := by exact prefixLift 2231636
  have htrace : WordTrace (prefixWord ++ tailWord_2231636) baseStart_2231636 baseEnd_2231636 := by
    simpa [prefixWord, tailWord_2231636, baseEnd_2231636] using wordTrace_append hprefix tailTrace_2231636
  have hstable : (prefixWord ++ tailWord_2231636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231636).length < 2 ^ (prefixWord ++ tailWord_2231636).sum := by decide
  have hdescent : baseEnd_2231636 < baseStart_2231636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231683 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 1, 1, 4]
def baseStart_2231683 : Nat := 118140960795 + 2231683 * 2 ^ 59
def prefixEnd_2231683 : Nat := 4983230072969 + 3 ^ 40 * 2231683 * 2
def baseEnd_2231683 : Nat := 1145926047467897263699183

theorem tailTrace_2231683 : CollatzResearch.WordTrace tailWord_2231683 prefixEnd_2231683 1145926047467897263699183 := by
  unfold tailWord_2231683
  simp only [CollatzResearch.WordTrace]
  refine ⟨81396165974001106957315703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54264110649334071304877135 81396165974001106957315703)
  ·
    refine ⟨122094248961001660435973555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81396165974001106957315703 122094248961001660435973555)
    ·
      refine ⟨183141373441502490653960333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122094248961001660435973555 183141373441502490653960333)
      ·
        refine ⟨68678015040563433995235125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183141373441502490653960333 68678015040563433995235125)
        ·
          refine ⟨6438563910052821937053293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68678015040563433995235125 6438563910052821937053293)
          ·
            refine ⟨2414461466269808226394985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6438563910052821937053293 2414461466269808226394985)
            ·
              refine ⟨1810846099702356169796239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414461466269808226394985 1810846099702356169796239)
              ·
                refine ⟨2716269149553534254694359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810846099702356169796239 2716269149553534254694359)
                ·
                  refine ⟨4074403724330301382041539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716269149553534254694359 4074403724330301382041539)
                  ·
                    refine ⟨6111605586495452073062309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074403724330301382041539 6111605586495452073062309)
                    ·
                      refine ⟨1145926047467897263699183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6111605586495452073062309 1145926047467897263699183)
                      ·
                        rfl

theorem cell23_2231683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_2231683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231683 prefixEnd_2231683 := by exact prefixLift 2231683
  have htrace : WordTrace (prefixWord ++ tailWord_2231683) baseStart_2231683 baseEnd_2231683 := by
    simpa [prefixWord, tailWord_2231683, baseEnd_2231683] using wordTrace_append hprefix tailTrace_2231683
  have hstable : (prefixWord ++ tailWord_2231683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231683).length < 2 ^ (prefixWord ++ tailWord_2231683).sum := by decide
  have hdescent : baseEnd_2231683 < baseStart_2231683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231700 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2231700 : Nat := 118140960795 + 2231700 * 2 ^ 59
def prefixEnd_2231700 : Nat := 4983230072969 + 3 ^ 40 * 2231700 * 2
def baseEnd_2231700 : Nat := 1145934776639023697186605

theorem tailTrace_2231700 : CollatzResearch.WordTrace tailWord_2231700 prefixEnd_2231700 1145934776639023697186605 := by
  unfold tailWord_2231700
  simp only [CollatzResearch.WordTrace]
  refine ⟨40698393007469759430342277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54264524009959679240456369 40698393007469759430342277)
  ·
    refine ⟨7630948688900579893189177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40698393007469759430342277 7630948688900579893189177)
    ·
      refine ⟨5723211516675434919891883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7630948688900579893189177 5723211516675434919891883)
      ·
        refine ⟨8584817275013152379837825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5723211516675434919891883 8584817275013152379837825)
        ·
          refine ⟨6438612956259864284878369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8584817275013152379837825 6438612956259864284878369)
          ·
            refine ⟨4828959717194898213658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438612956259864284878369 4828959717194898213658777)
            ·
              refine ⟨3621719787896173660244083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828959717194898213658777 3621719787896173660244083)
              ·
                refine ⟨5432579681844260490366125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621719787896173660244083 5432579681844260490366125)
                ·
                  refine ⟨2037217380691597683887297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5432579681844260490366125 2037217380691597683887297)
                  ·
                    refine ⟨1527913035518698262915473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2037217380691597683887297 1527913035518698262915473)
                    ·
                      refine ⟨1145934776639023697186605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527913035518698262915473 1145934776639023697186605)
                      ·
                        rfl

theorem cell23_2231700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2231700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231700 prefixEnd_2231700 := by exact prefixLift 2231700
  have htrace : WordTrace (prefixWord ++ tailWord_2231700) baseStart_2231700 baseEnd_2231700 := by
    simpa [prefixWord, tailWord_2231700, baseEnd_2231700] using wordTrace_append hprefix tailTrace_2231700
  have hstable : (prefixWord ++ tailWord_2231700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231700).length < 2 ^ (prefixWord ++ tailWord_2231700).sum := by decide
  have hdescent : baseEnd_2231700 < baseStart_2231700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231710 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2231710 : Nat := 118140960795 + 2231710 * 2 ^ 59
def prefixEnd_2231710 : Nat := 4983230072969 + 3 ^ 40 * 2231710 * 2
def baseEnd_2231710 : Nat := 381979970481856219353853

theorem tailTrace_2231710 : CollatzResearch.WordTrace tailWord_2231710 prefixEnd_2231710 381979970481856219353853 := by
  unfold tailWord_2231710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174643843112911321068573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54264767163268860379032389 10174643843112911321068573)
  ·
    refine ⟨3815491441167341745400715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10174643843112911321068573 3815491441167341745400715)
    ·
      refine ⟨5723237161751012618101073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3815491441167341745400715 5723237161751012618101073)
      ·
        refine ⟨4292427871313259463575805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5723237161751012618101073 4292427871313259463575805)
        ·
          refine ⟨1609660451742472298840927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4292427871313259463575805 1609660451742472298840927)
          ·
            refine ⟨2414490677613708448261391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609660451742472298840927 2414490677613708448261391)
            ·
              refine ⟨3621736016420562672392087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414490677613708448261391 3621736016420562672392087)
              ·
                refine ⟨5432604024630844008588131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621736016420562672392087 5432604024630844008588131)
                ·
                  refine ⟨8148906036946266012882197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432604024630844008588131 8148906036946266012882197)
                  ·
                    refine ⟨381979970481856219353853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8148906036946266012882197 381979970481856219353853)
                    ·
                      rfl

theorem cell23_2231710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2231710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231710 prefixEnd_2231710 := by exact prefixLift 2231710
  have htrace : WordTrace (prefixWord ++ tailWord_2231710) baseStart_2231710 baseEnd_2231710 := by
    simpa [prefixWord, tailWord_2231710, baseEnd_2231710] using wordTrace_append hprefix tailTrace_2231710
  have hstable : (prefixWord ++ tailWord_2231710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231710).length < 2 ^ (prefixWord ++ tailWord_2231710).sum := by decide
  have hdescent : baseEnd_2231710 < baseStart_2231710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231720 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2231720 : Nat := 118140960795 + 2231720 * 2 ^ 59
def prefixEnd_2231720 : Nat := 4983230072969 + 3 ^ 40 * 2231720 * 2
def baseEnd_2231720 : Nat := 1145945046252113618936513

theorem tailTrace_2231720 : CollatzResearch.WordTrace tailWord_2231720 prefixEnd_2231720 1145945046252113618936513 := by
  unfold tailWord_2231720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40698757737433531138206307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54265010316578041517608409 40698757737433531138206307)
  ·
    refine ⟨61048136606150296707309461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40698757737433531138206307 61048136606150296707309461)
    ·
      refine ⟨2861631403413295158155131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61048136606150296707309461 2861631403413295158155131)
      ·
        refine ⟨4292447105119942737232697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861631403413295158155131 4292447105119942737232697)
        ·
          refine ⟨3219335328839957052924523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292447105119942737232697 3219335328839957052924523)
          ·
            refine ⟨4829002993259935579386785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219335328839957052924523 4829002993259935579386785)
            ·
              refine ⟨3621752244944951684540089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829002993259935579386785 3621752244944951684540089)
              ·
                refine ⟨2716314183708713763405067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3621752244944951684540089 2716314183708713763405067)
                ·
                  refine ⟨4074471275563070645107601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716314183708713763405067 4074471275563070645107601)
                  ·
                    refine ⟨3055853456672302983830701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074471275563070645107601 3055853456672302983830701)
                    ·
                      refine ⟨1145945046252113618936513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3055853456672302983830701 1145945046252113618936513)
                      ·
                        rfl

theorem cell23_2231720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2231720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231720 prefixEnd_2231720 := by exact prefixLift 2231720
  have htrace : WordTrace (prefixWord ++ tailWord_2231720) baseStart_2231720 baseEnd_2231720 := by
    simpa [prefixWord, tailWord_2231720, baseEnd_2231720] using wordTrace_append hprefix tailTrace_2231720
  have hstable : (prefixWord ++ tailWord_2231720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231720).length < 2 ^ (prefixWord ++ tailWord_2231720).sum := by decide
  have hdescent : baseEnd_2231720 < baseStart_2231720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231816 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_2231816 : Nat := 118140960795 + 2231816 * 2 ^ 59
def prefixEnd_2231816 : Nat := 4983230072969 + 3 ^ 40 * 2231816 * 2
def baseEnd_2231816 : Nat := 1145994340394945243336071

theorem tailTrace_2231816 : CollatzResearch.WordTrace tailWord_2231816 prefixEnd_2231816 1145994340394945243336071 := by
  unfold tailWord_2231816
  simp only [CollatzResearch.WordTrace]
  refine ⟨40700508441259635335953651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54267344588346180447938201 40700508441259635335953651)
  ·
    refine ⟨61050762661889453003930477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40700508441259635335953651 61050762661889453003930477)
    ·
      refine ⟨22894035998208544876473929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61050762661889453003930477 22894035998208544876473929)
      ·
        refine ⟨17170526998656408657355447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22894035998208544876473929 17170526998656408657355447)
        ·
          refine ⟨25755790497984612986033171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17170526998656408657355447 25755790497984612986033171)
          ·
            refine ⟨38633685746976919479049757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25755790497984612986033171 38633685746976919479049757)
            ·
              refine ⟨14487632155116344804643659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38633685746976919479049757 14487632155116344804643659)
              ·
                refine ⟨21731448232674517206965489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14487632155116344804643659 21731448232674517206965489)
                ·
                  refine ⟨16298586174505887905224117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21731448232674517206965489 16298586174505887905224117)
                  ·
                    refine ⟨1527992453859926991114761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16298586174505887905224117 1527992453859926991114761)
                    ·
                      refine ⟨1145994340394945243336071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1527992453859926991114761 1145994340394945243336071)
                      ·
                        rfl

theorem cell23_2231816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_2231816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231816 prefixEnd_2231816 := by exact prefixLift 2231816
  have htrace : WordTrace (prefixWord ++ tailWord_2231816) baseStart_2231816 baseEnd_2231816 := by
    simpa [prefixWord, tailWord_2231816, baseEnd_2231816] using wordTrace_append hprefix tailTrace_2231816
  have hstable : (prefixWord ++ tailWord_2231816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231816).length < 2 ^ (prefixWord ++ tailWord_2231816).sum := by decide
  have hdescent : baseEnd_2231816 < baseStart_2231816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231843 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 2, 5]
def baseStart_2231843 : Nat := 118140960795 + 2231843 * 2 ^ 59
def prefixEnd_2231843 : Nat := 4983230072969 + 3 ^ 40 * 2231843 * 2
def baseEnd_2231843 : Nat := 382002734790872212566149

theorem tailTrace_2231843 : CollatzResearch.WordTrace tailWord_2231843 prefixEnd_2231843 382002734790872212566149 := by
  unfold tailWord_2231843
  simp only [CollatzResearch.WordTrace]
  refine ⟨81402001653421454283140183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54268001102280969522093455 81402001653421454283140183)
  ·
    refine ⟨122103002480132181424710275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81402001653421454283140183 122103002480132181424710275)
    ·
      refine ⟨183154503720198272137065413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122103002480132181424710275 183154503720198272137065413)
      ·
        refine ⟨34341469447537176025699765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183154503720198272137065413 34341469447537176025699765)
        ·
          refine ⟨3219512760706610252409353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34341469447537176025699765 3219512760706610252409353)
          ·
            refine ⟨2414634570529957689307015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3219512760706610252409353 2414634570529957689307015)
            ·
              refine ⟨3621951855794936533960523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414634570529957689307015 3621951855794936533960523)
              ·
                refine ⟨5432927783692404800940785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621951855794936533960523 5432927783692404800940785)
                ·
                  refine ⟨4074695837769303600705589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432927783692404800940785 4074695837769303600705589)
                  ·
                    refine ⟨382002734790872212566149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4074695837769303600705589 382002734790872212566149)
                    ·
                      rfl

theorem cell23_2231843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 5].length) (baseStart_2231843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231843 prefixEnd_2231843 := by exact prefixLift 2231843
  have htrace : WordTrace (prefixWord ++ tailWord_2231843) baseStart_2231843 baseEnd_2231843 := by
    simpa [prefixWord, tailWord_2231843, baseEnd_2231843] using wordTrace_append hprefix tailTrace_2231843
  have hstable : (prefixWord ++ tailWord_2231843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231843).length < 2 ^ (prefixWord ++ tailWord_2231843).sum := by decide
  have hdescent : baseEnd_2231843 < baseStart_2231843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231859 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_2231859 : Nat := 118140960795 + 2231859 * 2 ^ 59
def prefixEnd_2231859 : Nat := 4983230072969 + 3 ^ 40 * 2231859 * 2
def baseEnd_2231859 : Nat := 1146016420063088575098373

theorem tailTrace_2231859 : CollatzResearch.WordTrace tailWord_2231859 prefixEnd_2231859 1146016420063088575098373 := by
  unfold tailWord_2231859
  simp only [CollatzResearch.WordTrace]
  refine ⟨81402585221363489015722631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54268390147575659343815087 81402585221363489015722631)
  ·
    refine ⟨122103877832045233523583947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81402585221363489015722631 122103877832045233523583947)
    ·
      refine ⟨183155816748067850285375921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122103877832045233523583947 183155816748067850285375921)
      ·
        refine ⟨137366862561050887714031941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183155816748067850285375921 137366862561050887714031941)
        ·
          refine ⟨25756286730197041446380989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137366862561050887714031941 25756286730197041446380989)
          ·
            refine ⟨9658607523823890542392871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25756286730197041446380989 9658607523823890542392871)
            ·
              refine ⟨14487911285735835813589307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9658607523823890542392871 14487911285735835813589307)
              ·
                refine ⟨21731866928603753720383961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14487911285735835813589307 21731866928603753720383961)
                ·
                  refine ⟨16298900196452815290287971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21731866928603753720383961 16298900196452815290287971)
                  ·
                    refine ⟨24448350294679222935431957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16298900196452815290287971 24448350294679222935431957)
                    ·
                      refine ⟨1146016420063088575098373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24448350294679222935431957 1146016420063088575098373)
                      ·
                        rfl

theorem cell23_2231859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_2231859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231859 prefixEnd_2231859 := by exact prefixLift 2231859
  have htrace : WordTrace (prefixWord ++ tailWord_2231859) baseStart_2231859 baseEnd_2231859 := by
    simpa [prefixWord, tailWord_2231859, baseEnd_2231859] using wordTrace_append hprefix tailTrace_2231859
  have hstable : (prefixWord ++ tailWord_2231859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231859).length < 2 ^ (prefixWord ++ tailWord_2231859).sum := by decide
  have hdescent : baseEnd_2231859 < baseStart_2231859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231866 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_2231866 : Nat := 118140960795 + 2231866 * 2 ^ 59
def prefixEnd_2231866 : Nat := 4983230072969 + 3 ^ 40 * 2231866 * 2
def baseEnd_2231866 : Nat := 1146020014427670047710841

theorem tailTrace_2231866 : CollatzResearch.WordTrace tailWord_2231866 prefixEnd_2231866 1146020014427670047710841 := by
  unfold tailWord_2231866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20350710133084532302806863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54268560354892086140818301 20350710133084532302806863)
  ·
    refine ⟨30526065199626798454210295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20350710133084532302806863 30526065199626798454210295)
    ·
      refine ⟨45789097799440197681315443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30526065199626798454210295 45789097799440197681315443)
      ·
        refine ⟨68683646699160296521973165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45789097799440197681315443 68683646699160296521973165)
        ·
          refine ⟨25756367512185111195739937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68683646699160296521973165 25756367512185111195739937)
          ·
            refine ⟨19317275634138833396804953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25756367512185111195739937 19317275634138833396804953)
            ·
              refine ⟨14487956725604125047603715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19317275634138833396804953 14487956725604125047603715)
              ·
                refine ⟨21731935088406187571405573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14487956725604125047603715 21731935088406187571405573)
                ·
                  refine ⟨4074737829076160169638545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21731935088406187571405573 4074737829076160169638545)
                  ·
                    refine ⟨3056053371807120127228909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074737829076160169638545 3056053371807120127228909)
                    ·
                      refine ⟨1146020014427670047710841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056053371807120127228909 1146020014427670047710841)
                      ·
                        rfl

theorem cell23_2231866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_2231866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231866 prefixEnd_2231866 := by exact prefixLift 2231866
  have htrace : WordTrace (prefixWord ++ tailWord_2231866) baseStart_2231866 baseEnd_2231866 := by
    simpa [prefixWord, tailWord_2231866, baseEnd_2231866] using wordTrace_append hprefix tailTrace_2231866
  have hstable : (prefixWord ++ tailWord_2231866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231866).length < 2 ^ (prefixWord ++ tailWord_2231866).sum := by decide
  have hdescent : baseEnd_2231866 < baseStart_2231866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231873 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2231873 : Nat := 118140960795 + 2231873 * 2 ^ 59
def prefixEnd_2231873 : Nat := 4983230072969 + 3 ^ 40 * 2231873 * 2
def baseEnd_2231873 : Nat := 382007869597417173441103

theorem tailTrace_2231873 : CollatzResearch.WordTrace tailWord_2231873 prefixEnd_2231873 382007869597417173441103 := by
  unfold tailWord_2231873
  simp only [CollatzResearch.WordTrace]
  refine ⟨81403095843312769406732273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54268730562208512937821515 81403095843312769406732273)
  ·
    refine ⟨61052321882484577055049205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81403095843312769406732273 61052321882484577055049205)
    ·
      refine ⟨5723655176482929098910863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61052321882484577055049205 5723655176482929098910863)
      ·
        refine ⟨8585482764724393648366295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5723655176482929098910863 8585482764724393648366295)
        ·
          refine ⟨12878224147086590472549443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8585482764724393648366295 12878224147086590472549443)
          ·
            refine ⟨19317336220629885708824165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12878224147086590472549443 19317336220629885708824165)
            ·
              refine ⟨3622000541368103570404531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19317336220629885708824165 3622000541368103570404531)
              ·
                refine ⟨5433000812052155355606797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622000541368103570404531 5433000812052155355606797)
                ·
                  refine ⟨2037375304519558258352549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5433000812052155355606797 2037375304519558258352549)
                  ·
                    refine ⟨382007869597417173441103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2037375304519558258352549 382007869597417173441103)
                    ·
                      rfl

theorem cell23_2231873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2231873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231873 prefixEnd_2231873 := by exact prefixLift 2231873
  have htrace : WordTrace (prefixWord ++ tailWord_2231873) baseStart_2231873 baseEnd_2231873 := by
    simpa [prefixWord, tailWord_2231873, baseEnd_2231873] using wordTrace_append hprefix tailTrace_2231873
  have hstable : (prefixWord ++ tailWord_2231873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231873).length < 2 ^ (prefixWord ++ tailWord_2231873).sum := by decide
  have hdescent : baseEnd_2231873 < baseStart_2231873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231889 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2231889 : Nat := 118140960795 + 2231889 * 2 ^ 59
def prefixEnd_2231889 : Nat := 4983230072969 + 3 ^ 40 * 2231889 * 2
def baseEnd_2231889 : Nat := 1146031824482723457723235

theorem tailTrace_2231889 : CollatzResearch.WordTrace tailWord_2231889 prefixEnd_2231889 1146031824482723457723235 := by
  unfold tailWord_2231889
  simp only [CollatzResearch.WordTrace]
  refine ⟨81403679411254804139314721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54269119607503202759543147 81403679411254804139314721)
  ·
    refine ⟨61052759558441103104486041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81403679411254804139314721 61052759558441103104486041)
    ·
      refine ⟨45789569668830827328364531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61052759558441103104486041 45789569668830827328364531)
      ·
        refine ⟨68684354503246240992546797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45789569668830827328364531 68684354503246240992546797)
        ·
          refine ⟨25756632938717340372205049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68684354503246240992546797 25756632938717340372205049)
          ·
            refine ⟨19317474704038005279153787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25756632938717340372205049 19317474704038005279153787)
            ·
              refine ⟨28976212056057007918730681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19317474704038005279153787 28976212056057007918730681)
              ·
                refine ⟨21732159042042755939048011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28976212056057007918730681 21732159042042755939048011)
                ·
                  refine ⟨32598238563064133908572017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21732159042042755939048011 32598238563064133908572017)
                  ·
                    refine ⟨24448678922298100431429013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32598238563064133908572017 24448678922298100431429013)
                    ·
                      refine ⟨1146031824482723457723235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24448678922298100431429013 1146031824482723457723235)
                      ·
                        rfl

theorem cell23_2231889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2231889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231889 prefixEnd_2231889 := by exact prefixLift 2231889
  have htrace : WordTrace (prefixWord ++ tailWord_2231889) baseStart_2231889 baseEnd_2231889 := by
    simpa [prefixWord, tailWord_2231889, baseEnd_2231889] using wordTrace_append hprefix tailTrace_2231889
  have hstable : (prefixWord ++ tailWord_2231889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231889).length < 2 ^ (prefixWord ++ tailWord_2231889).sum := by decide
  have hdescent : baseEnd_2231889 < baseStart_2231889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231936 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2231936 : Nat := 118140960795 + 2231936 * 2 ^ 59
def prefixEnd_2231936 : Nat := 4983230072969 + 3 ^ 40 * 2231936 * 2
def baseEnd_2231936 : Nat := 1146055958073484773835519

theorem tailTrace_2231936 : CollatzResearch.WordTrace tailWord_2231936 prefixEnd_2231936 1146055958073484773835519 := by
  unfold tailWord_2231936
  simp only [CollatzResearch.WordTrace]
  refine ⟨40702696821042265583137831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54270262428056354110850441 40702696821042265583137831)
  ·
    refine ⟨61054045231563398374706747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40702696821042265583137831 61054045231563398374706747)
    ·
      refine ⟨91581067847345097562060121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61054045231563398374706747 91581067847345097562060121)
      ·
        refine ⟨68685800885508823171545091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91581067847345097562060121 68685800885508823171545091)
        ·
          refine ⟨103028701328263234757317637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68685800885508823171545091 103028701328263234757317637)
          ·
            refine ⟨19317881499049356516997057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103028701328263234757317637 19317881499049356516997057)
            ·
              refine ⟨14488411124287017387747793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19317881499049356516997057 14488411124287017387747793)
              ·
                refine ⟨10866308343215263040810845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14488411124287017387747793 10866308343215263040810845)
                ·
                  refine ⟨4074865628705723640304067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10866308343215263040810845 4074865628705723640304067)
                  ·
                    refine ⟨6112298443058585460456101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074865628705723640304067 6112298443058585460456101)
                    ·
                      refine ⟨1146055958073484773835519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6112298443058585460456101 1146055958073484773835519)
                      ·
                        rfl

theorem cell23_2231936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2231936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231936 prefixEnd_2231936 := by exact prefixLift 2231936
  have htrace : WordTrace (prefixWord ++ tailWord_2231936) baseStart_2231936 baseEnd_2231936 := by
    simpa [prefixWord, tailWord_2231936, baseEnd_2231936] using wordTrace_append hprefix tailTrace_2231936
  have hstable : (prefixWord ++ tailWord_2231936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231936).length < 2 ^ (prefixWord ++ tailWord_2231936).sum := by decide
  have hdescent : baseEnd_2231936 < baseStart_2231936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231950 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2231950 : Nat := 118140960795 + 2231950 * 2 ^ 59
def prefixEnd_2231950 : Nat := 4983230072969 + 3 ^ 40 * 2231950 * 2
def baseEnd_2231950 : Nat := 382021048934215906353485

theorem tailTrace_2231950 : CollatzResearch.WordTrace tailWord_2231950 prefixEnd_2231950 382021048934215906353485 := by
  unfold tailWord_2231950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10175738033004226444660663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54270602842689207704856869 10175738033004226444660663)
  ·
    refine ⟨15263607049506339666990995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10175738033004226444660663 15263607049506339666990995)
    ·
      refine ⟨22895410574259509500486493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15263607049506339666990995 22895410574259509500486493)
      ·
        refine ⟨8585778965347316062682435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22895410574259509500486493 8585778965347316062682435)
        ·
          refine ⟨12878668448020974094023653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8585778965347316062682435 12878668448020974094023653)
          ·
            refine ⟨2414750334003932642629435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12878668448020974094023653 2414750334003932642629435)
            ·
              refine ⟨3622125501005898963944153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414750334003932642629435 3622125501005898963944153)
              ·
                refine ⟨2716594125754424222958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3622125501005898963944153 2716594125754424222958115)
                ·
                  refine ⟨4074891188631636334437173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716594125754424222958115 4074891188631636334437173)
                  ·
                    refine ⟨382021048934215906353485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4074891188631636334437173 382021048934215906353485)
                    ·
                      rfl

theorem cell23_2231950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2231950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231950 prefixEnd_2231950 := by exact prefixLift 2231950
  have htrace : WordTrace (prefixWord ++ tailWord_2231950) baseStart_2231950 baseEnd_2231950 := by
    simpa [prefixWord, tailWord_2231950, baseEnd_2231950] using wordTrace_append hprefix tailTrace_2231950
  have hstable : (prefixWord ++ tailWord_2231950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231950).length < 2 ^ (prefixWord ++ tailWord_2231950).sum := by decide
  have hdescent : baseEnd_2231950 < baseStart_2231950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231967 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 1, 5]
def baseStart_2231967 : Nat := 118140960795 + 2231967 * 2 ^ 59
def prefixEnd_2231967 : Nat := 4983230072969 + 3 ^ 40 * 2231967 * 2
def baseEnd_2231967 : Nat := 382023958657924717515959

theorem tailTrace_2231967 : CollatzResearch.WordTrace tailWord_2231967 prefixEnd_2231967 382023958657924717515959 := by
  unfold tailWord_2231967
  simp only [CollatzResearch.WordTrace]
  refine ⟨81406524304972223460654155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54271016203314815640436103 81406524304972223460654155)
  ·
    refine ⟨122109786457458335190981233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81406524304972223460654155 122109786457458335190981233)
    ·
      refine ⟨91582339843093751393235925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122109786457458335190981233 91582339843093751393235925)
      ·
        refine ⟨2146461090072509798278967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91582339843093751393235925 2146461090072509798278967)
        ·
          refine ⟨3219691635108764697418451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146461090072509798278967 3219691635108764697418451)
          ·
            refine ⟨4829537452663147046127677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219691635108764697418451 4829537452663147046127677)
            ·
              refine ⟨1811076544748680142297879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4829537452663147046127677 1811076544748680142297879)
              ·
                refine ⟨2716614817123020213446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811076544748680142297879 2716614817123020213446819)
                ·
                  refine ⟨4074922225684530320170229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716614817123020213446819 4074922225684530320170229)
                  ·
                    refine ⟨382023958657924717515959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4074922225684530320170229 382023958657924717515959)
                    ·
                      rfl

theorem cell23_2231967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_2231967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231967 prefixEnd_2231967 := by exact prefixLift 2231967
  have htrace : WordTrace (prefixWord ++ tailWord_2231967) baseStart_2231967 baseEnd_2231967 := by
    simpa [prefixWord, tailWord_2231967, baseEnd_2231967] using wordTrace_append hprefix tailTrace_2231967
  have hstable : (prefixWord ++ tailWord_2231967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231967).length < 2 ^ (prefixWord ++ tailWord_2231967).sum := by decide
  have hdescent : baseEnd_2231967 < baseStart_2231967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231973 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_2231973 : Nat := 118140960795 + 2231973 * 2 ^ 59
def prefixEnd_2231973 : Nat := 4983230072969 + 3 ^ 40 * 2231973 * 2
def baseEnd_2231973 : Nat := 1146074956857701129072849

theorem tailTrace_2231973 : CollatzResearch.WordTrace tailWord_2231973 prefixEnd_2231973 1146074956857701129072849 := by
  unfold tailWord_2231973
  simp only [CollatzResearch.WordTrace]
  refine ⟨81406743142950486485372573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54271162095300324323581715 81406743142950486485372573)
  ·
    refine ⟨30527528678606432432014715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81406743142950486485372573 30527528678606432432014715)
    ·
      refine ⟨45791293017909648648022073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30527528678606432432014715 45791293017909648648022073)
      ·
        refine ⟨34343469763432236486016555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45791293017909648648022073 34343469763432236486016555)
        ·
          refine ⟨51515204645148354729024833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34343469763432236486016555 51515204645148354729024833)
          ·
            refine ⟨38636403483861266046768625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51515204645148354729024833 38636403483861266046768625)
            ·
              refine ⟨28977302612895949535076469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38636403483861266046768625 28977302612895949535076469)
              ·
                refine ⟨2716622119958995268913419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28977302612895949535076469 2716622119958995268913419)
                ·
                  refine ⟨4074933179938492903370129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716622119958995268913419 4074933179938492903370129)
                  ·
                    refine ⟨3056199884953869677527597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074933179938492903370129 3056199884953869677527597)
                    ·
                      refine ⟨1146074956857701129072849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056199884953869677527597 1146074956857701129072849)
                      ·
                        rfl

theorem cell23_2231973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_2231973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231973 prefixEnd_2231973 := by exact prefixLift 2231973
  have htrace : WordTrace (prefixWord ++ tailWord_2231973) baseStart_2231973 baseEnd_2231973 := by
    simpa [prefixWord, tailWord_2231973, baseEnd_2231973] using wordTrace_append hprefix tailTrace_2231973
  have hstable : (prefixWord ++ tailWord_2231973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231973).length < 2 ^ (prefixWord ++ tailWord_2231973).sum := by decide
  have hdescent : baseEnd_2231973 < baseStart_2231973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231979 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_2231979 : Nat := 118140960795 + 2231979 * 2 ^ 59
def prefixEnd_2231979 : Nat := 4983230072969 + 3 ^ 40 * 2231979 * 2
def baseEnd_2231979 : Nat := 1146078037741628105597821

theorem tailTrace_2231979 : CollatzResearch.WordTrace tailWord_2231979 prefixEnd_2231979 1146078037741628105597821 := by
  unfold tailWord_2231979
  simp only [CollatzResearch.WordTrace]
  refine ⟨81406961980928749510090991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54271307987285833006727327 81406961980928749510090991)
  ·
    refine ⟨122110442971393124265136487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81406961980928749510090991 122110442971393124265136487)
    ·
      refine ⟨183165664457089686397704731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122110442971393124265136487 183165664457089686397704731)
      ·
        refine ⟨274748496685634529596557097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183165664457089686397704731 274748496685634529596557097)
        ·
          refine ⟨206061372514225897197417823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274748496685634529596557097 206061372514225897197417823)
          ·
            refine ⟨309092058771338845796126735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206061372514225897197417823 309092058771338845796126735)
            ·
              refine ⟨463638088157008268694190103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309092058771338845796126735 463638088157008268694190103)
              ·
                refine ⟨695457132235512403041285155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463638088157008268694190103 695457132235512403041285155)
                ·
                  refine ⟨1043185698353268604561927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695457132235512403041285155 1043185698353268604561927733)
                  ·
                    refine ⟨97798659220618931677680725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1043185698353268604561927733 97798659220618931677680725)
                    ·
                      refine ⟨1146078037741628105597821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 97798659220618931677680725 1146078037741628105597821)
                      ·
                        rfl

theorem cell23_2231979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_2231979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231979 prefixEnd_2231979 := by exact prefixLift 2231979
  have htrace : WordTrace (prefixWord ++ tailWord_2231979) baseStart_2231979 baseEnd_2231979 := by
    simpa [prefixWord, tailWord_2231979, baseEnd_2231979] using wordTrace_append hprefix tailTrace_2231979
  have hstable : (prefixWord ++ tailWord_2231979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231979).length < 2 ^ (prefixWord ++ tailWord_2231979).sum := by decide
  have hdescent : baseEnd_2231979 < baseStart_2231979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231987 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 1, 2, 2]
def baseStart_2231987 : Nat := 118140960795 + 2231987 * 2 ^ 59
def prefixEnd_2231987 : Nat := 4983230072969 + 3 ^ 40 * 2231987 * 2
def baseEnd_2231987 : Nat := 1146082145586864074297785

theorem tailTrace_2231987 : CollatzResearch.WordTrace tailWord_2231987 prefixEnd_2231987 1146082145586864074297785 := by
  unfold tailWord_2231987
  simp only [CollatzResearch.WordTrace]
  refine ⟨81407253764899766876382215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54271502509933177917588143 81407253764899766876382215)
  ·
    refine ⟨122110880647349650314573323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81407253764899766876382215 122110880647349650314573323)
    ·
      refine ⟨183166320971024475471859985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122110880647349650314573323 183166320971024475471859985)
      ·
        refine ⟨137374740728268356603894989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183166320971024475471859985 137374740728268356603894989)
        ·
          refine ⟨51515527773100633726460621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137374740728268356603894989 51515527773100633726460621)
          ·
            refine ⟨19318322914912737647422733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51515527773100633726460621 19318322914912737647422733)
            ·
              refine ⟨7244371093092276617783525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19318322914912737647422733 7244371093092276617783525)
              ·
                refine ⟨1358319579954801865834411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7244371093092276617783525 1358319579954801865834411)
                ·
                  refine ⟨2037479369932202798751617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358319579954801865834411 2037479369932202798751617)
                  ·
                    refine ⟨1528109527449152099063713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2037479369932202798751617 1528109527449152099063713)
                    ·
                      refine ⟨1146082145586864074297785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528109527449152099063713 1146082145586864074297785)
                      ·
                        rfl

theorem cell23_2231987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 2, 2].length) (baseStart_2231987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2231987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2231987 prefixEnd_2231987 := by exact prefixLift 2231987
  have htrace : WordTrace (prefixWord ++ tailWord_2231987) baseStart_2231987 baseEnd_2231987 := by
    simpa [prefixWord, tailWord_2231987, baseEnd_2231987] using wordTrace_append hprefix tailTrace_2231987
  have hstable : (prefixWord ++ tailWord_2231987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231987).length < 2 ^ (prefixWord ++ tailWord_2231987).sum := by decide
  have hdescent : baseEnd_2231987 < baseStart_2231987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232020 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2232020 : Nat := 118140960795 + 2232020 * 2 ^ 59
def prefixEnd_2232020 : Nat := 4983230072969 + 3 ^ 40 * 2232020 * 2
def baseEnd_2232020 : Nat := 1146099090448462445185133

theorem tailTrace_2232020 : CollatzResearch.WordTrace tailWord_2232020 prefixEnd_2232020 1146099090448462445185133 := by
  unfold tailWord_2232020
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704228686890106756166757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54272304915853475674889009 40704228686890106756166757)
  ·
    refine ⟨7632042878791895016781267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40704228686890106756166757 7632042878791895016781267)
    ·
      refine ⟨11448064318187842525171901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632042878791895016781267 11448064318187842525171901)
      ·
        refine ⟨4293024119320440946939463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11448064318187842525171901 4293024119320440946939463)
        ·
          refine ⟨6439536178980661420409195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293024119320440946939463 6439536178980661420409195)
          ·
            refine ⟨9659304268470992130613793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6439536178980661420409195 9659304268470992130613793)
            ·
              refine ⟨7244478201353244097960345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9659304268470992130613793 7244478201353244097960345)
              ·
                refine ⟨5433358651014933073470259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7244478201353244097960345 5433358651014933073470259)
                ·
                  refine ⟨8150037976522399610205389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433358651014933073470259 8150037976522399610205389)
                  ·
                    refine ⟨3056264241195899853827021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8150037976522399610205389 3056264241195899853827021)
                    ·
                      refine ⟨1146099090448462445185133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056264241195899853827021 1146099090448462445185133)
                      ·
                        rfl

theorem cell23_2232020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2232020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232020 prefixEnd_2232020 := by exact prefixLift 2232020
  have htrace : WordTrace (prefixWord ++ tailWord_2232020) baseStart_2232020 baseEnd_2232020 := by
    simpa [prefixWord, tailWord_2232020, baseEnd_2232020] using wordTrace_append hprefix tailTrace_2232020
  have hstable : (prefixWord ++ tailWord_2232020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232020).length < 2 ^ (prefixWord ++ tailWord_2232020).sum := by decide
  have hdescent : baseEnd_2232020 < baseStart_2232020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232036 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_2232036 : Nat := 118140960795 + 2232036 * 2 ^ 59
def prefixEnd_2232036 : Nat := 4983230072969 + 3 ^ 40 * 2232036 * 2
def baseEnd_2232036 : Nat := 382035768712978127528353

theorem tailTrace_2232036 : CollatzResearch.WordTrace tailWord_2232036 prefixEnd_2232036 382035768712978127528353 := by
  unfold tailWord_2232036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704520470861124122457981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54272693961148165496610641 40704520470861124122457981)
  ·
    refine ⟨15264195176572921545921743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40704520470861124122457981 15264195176572921545921743)
    ·
      refine ⟨22896292764859382318882615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15264195176572921545921743 22896292764859382318882615)
      ·
        refine ⟨34344439147289073478323923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22896292764859382318882615 34344439147289073478323923)
        ·
          refine ⟨51516658720933610217485885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34344439147289073478323923 51516658720933610217485885)
          ·
            refine ⟨19318747020350103831557207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51516658720933610217485885 19318747020350103831557207)
            ·
              refine ⟨28978120530525155747335811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19318747020350103831557207 28978120530525155747335811)
              ·
                refine ⟨43467180795787733621003717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28978120530525155747335811 43467180795787733621003717)
                ·
                  refine ⟨8150096399210200053938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43467180795787733621003717 8150096399210200053938197)
                  ·
                    refine ⟨382035768712978127528353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8150096399210200053938197 382035768712978127528353)
                    ·
                      rfl

theorem cell23_2232036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_2232036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232036 prefixEnd_2232036 := by exact prefixLift 2232036
  have htrace : WordTrace (prefixWord ++ tailWord_2232036) baseStart_2232036 baseEnd_2232036 := by
    simpa [prefixWord, tailWord_2232036, baseEnd_2232036] using wordTrace_append hprefix tailTrace_2232036
  have hstable : (prefixWord ++ tailWord_2232036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232036).length < 2 ^ (prefixWord ++ tailWord_2232036).sum := by decide
  have hdescent : baseEnd_2232036 < baseStart_2232036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232043 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 4, 2]
def baseStart_2232043 : Nat := 118140960795 + 2232043 * 2 ^ 59
def prefixEnd_2232043 : Nat := 4983230072969 + 3 ^ 40 * 2232043 * 2
def baseEnd_2232043 : Nat := 1146110900503515855197527

theorem tailTrace_2232043 : CollatzResearch.WordTrace tailWord_2232043 prefixEnd_2232043 1146110900503515855197527 := by
  unfold tailWord_2232043
  simp only [CollatzResearch.WordTrace]
  refine ⟨81409296252696888440420783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54272864168464592293613855 81409296252696888440420783)
  ·
    refine ⟨122113944379045332660631175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81409296252696888440420783 122113944379045332660631175)
    ·
      refine ⟨183170916568567998990946763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122113944379045332660631175 183170916568567998990946763)
      ·
        refine ⟨274756374852851998486420145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183170916568567998990946763 274756374852851998486420145)
        ·
          refine ⟨206067281139638998864815109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274756374852851998486420145 206067281139638998864815109)
          ·
            refine ⟨38637615213682312287152833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206067281139638998864815109 38637615213682312287152833)
            ·
              refine ⟨28978211410261734215364625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38637615213682312287152833 28978211410261734215364625)
              ·
                refine ⟨21733658557696300661523469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28978211410261734215364625 21733658557696300661523469)
                ·
                  refine ⟨8150121959136112748071301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21733658557696300661523469 8150121959136112748071301)
                  ·
                    refine ⟨1528147867338021140263369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8150121959136112748071301 1528147867338021140263369)
                    ·
                      refine ⟨1146110900503515855197527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528147867338021140263369 1146110900503515855197527)
                      ·
                        rfl

theorem cell23_2232043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4, 2].length) (baseStart_2232043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232043 prefixEnd_2232043 := by exact prefixLift 2232043
  have htrace : WordTrace (prefixWord ++ tailWord_2232043) baseStart_2232043 baseEnd_2232043 := by
    simpa [prefixWord, tailWord_2232043, baseEnd_2232043] using wordTrace_append hprefix tailTrace_2232043
  have hstable : (prefixWord ++ tailWord_2232043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232043).length < 2 ^ (prefixWord ++ tailWord_2232043).sum := by decide
  have hdescent : baseEnd_2232043 < baseStart_2232043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232054 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2232054 : Nat := 118140960795 + 2232054 * 2 ^ 59
def prefixEnd_2232054 : Nat := 4983230072969 + 3 ^ 40 * 2232054 * 2
def baseEnd_2232054 : Nat := 1146116548790715312159977

theorem tailTrace_2232054 : CollatzResearch.WordTrace tailWord_2232054 prefixEnd_2232054 1146116548790715312159977 := by
  unfold tailWord_2232054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088106090978564832441951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54273131637104691546047477 5088106090978564832441951)
  ·
    refine ⟨7632159136467847248662927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088106090978564832441951 7632159136467847248662927)
    ·
      refine ⟨11448238704701770872994391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632159136467847248662927 11448238704701770872994391)
      ·
        refine ⟨17172358057052656309491587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11448238704701770872994391 17172358057052656309491587)
        ·
          refine ⟨25758537085578984464237381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17172358057052656309491587 25758537085578984464237381)
          ·
            refine ⟨4829725703546059587044509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25758537085578984464237381 4829725703546059587044509)
            ·
              refine ⟨1811147138829772345141691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4829725703546059587044509 1811147138829772345141691)
              ·
                refine ⟨2716720708244658517712537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811147138829772345141691 2716720708244658517712537)
                ·
                  refine ⟨2037540531183493888284403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2716720708244658517712537 2037540531183493888284403)
                  ·
                    refine ⟨3056310796775240832426605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2037540531183493888284403 3056310796775240832426605)
                    ·
                      refine ⟨1146116548790715312159977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056310796775240832426605 1146116548790715312159977)
                      ·
                        rfl

theorem cell23_2232054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2232054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232054 prefixEnd_2232054 := by exact prefixLift 2232054
  have htrace : WordTrace (prefixWord ++ tailWord_2232054) baseStart_2232054 baseEnd_2232054 := by
    simpa [prefixWord, tailWord_2232054, baseEnd_2232054] using wordTrace_append hprefix tailTrace_2232054
  have hstable : (prefixWord ++ tailWord_2232054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232054).length < 2 ^ (prefixWord ++ tailWord_2232054).sum := by decide
  have hdescent : baseEnd_2232054 < baseStart_2232054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232056 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2232056 : Nat := 118140960795 + 2232056 * 2 ^ 59
def prefixEnd_2232056 : Nat := 4983230072969 + 3 ^ 40 * 2232056 * 2
def baseEnd_2232056 : Nat := 1146117575752024304334967

theorem tailTrace_2232056 : CollatzResearch.WordTrace tailWord_2232056 prefixEnd_2232056 1146117575752024304334967 := by
  unfold tailWord_2232056
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704885200824895830322011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54273180267766527773762681 40704885200824895830322011)
  ·
    refine ⟨61057327801237343745483017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40704885200824895830322011 61057327801237343745483017)
    ·
      refine ⟨45792995850928007809112263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61057327801237343745483017 45792995850928007809112263)
      ·
        refine ⟨68689493776392011713668395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45792995850928007809112263 68689493776392011713668395)
        ·
          refine ⟨103034240664588017570502593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68689493776392011713668395 103034240664588017570502593)
          ·
            refine ⟨77275680498441013177876945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103034240664588017570502593 77275680498441013177876945)
            ·
              refine ⟨57956760373830759883407709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77275680498441013177876945 57956760373830759883407709)
              ·
                refine ⟨21733785140186534956277891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57956760373830759883407709 21733785140186534956277891)
                ·
                  refine ⟨32600677710279802434416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21733785140186534956277891 32600677710279802434416837)
                  ·
                    refine ⟨6112627070677462956453157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32600677710279802434416837 6112627070677462956453157)
                    ·
                      refine ⟨1146117575752024304334967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6112627070677462956453157 1146117575752024304334967)
                      ·
                        rfl

theorem cell23_2232056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2232056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232056 prefixEnd_2232056 := by exact prefixLift 2232056
  have htrace : WordTrace (prefixWord ++ tailWord_2232056) baseStart_2232056 baseEnd_2232056 := by
    simpa [prefixWord, tailWord_2232056, baseEnd_2232056] using wordTrace_append hprefix tailTrace_2232056
  have hstable : (prefixWord ++ tailWord_2232056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232056).length < 2 ^ (prefixWord ++ tailWord_2232056).sum := by decide
  have hdescent : baseEnd_2232056 < baseStart_2232056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232083 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 5]
def baseStart_2232083 : Nat := 118140960795 + 2232083 * 2 ^ 59
def prefixEnd_2232083 : Nat := 4983230072969 + 3 ^ 40 * 2232083 * 2
def baseEnd_2232083 : Nat := 127347937747743966521927

theorem tailTrace_2232083 : CollatzResearch.WordTrace tailWord_2232083 prefixEnd_2232083 127347937747743966521927 := by
  unfold tailWord_2232083
  simp only [CollatzResearch.WordTrace]
  refine ⟨81410755172551975271876903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54273836781701316847917935 81410755172551975271876903)
  ·
    refine ⟨122116132758827962907815355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81410755172551975271876903 122116132758827962907815355)
    ·
      refine ⟨183174199138241944361723033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122116132758827962907815355 183174199138241944361723033)
      ·
        refine ⟨137380649353681458271292275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183174199138241944361723033 137380649353681458271292275)
        ·
          refine ⟨206070974030522187406938413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137380649353681458271292275 206070974030522187406938413)
          ·
            refine ⟨77276615261445820277601905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206070974030522187406938413 77276615261445820277601905)
            ·
              refine ⟨57957461446084365208201429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77276615261445820277601905 57957461446084365208201429)
              ·
                refine ⟨1358378002642602309567221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57957461446084365208201429 1358378002642602309567221)
                ·
                  refine ⟨127347937747743966521927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1358378002642602309567221 127347937747743966521927)
                  ·
                    rfl

theorem cell23_2232083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 5].length) (baseStart_2232083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232083 prefixEnd_2232083 := by exact prefixLift 2232083
  have htrace : WordTrace (prefixWord ++ tailWord_2232083) baseStart_2232083 baseEnd_2232083 := by
    simpa [prefixWord, tailWord_2232083, baseEnd_2232083] using wordTrace_append hprefix tailTrace_2232083
  have hstable : (prefixWord ++ tailWord_2232083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232083).length < 2 ^ (prefixWord ++ tailWord_2232083).sum := by decide
  have hdescent : baseEnd_2232083 < baseStart_2232083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232100 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 7]
def baseStart_2232100 : Nat := 118140960795 + 2232100 * 2 ^ 59
def prefixEnd_2232100 : Nat := 4983230072969 + 3 ^ 40 * 2232100 * 2
def baseEnd_2232100 : Nat := 127348907655646903576085

theorem tailTrace_2232100 : CollatzResearch.WordTrace tailWord_2232100 prefixEnd_2232100 127348907655646903576085 := by
  unfold tailWord_2232100
  simp only [CollatzResearch.WordTrace]
  refine ⟨40705687606745193587622877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54274250142326924783497169 40705687606745193587622877)
  ·
    refine ⟨15264632852529447595358579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40705687606745193587622877 15264632852529447595358579)
    ·
      refine ⟨22896949278794171393037869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15264632852529447595358579 22896949278794171393037869)
      ·
        refine ⟨8586355979547814272389201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22896949278794171393037869 8586355979547814272389201)
        ·
          refine ⟨6439766984660860704291901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8586355979547814272389201 6439766984660860704291901)
          ·
            refine ⟨2414912619247822764109463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6439766984660860704291901 2414912619247822764109463)
            ·
              refine ⟨3622368928871734146164195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414912619247822764109463 3622368928871734146164195)
              ·
                refine ⟨5433553393307601219246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622368928871734146164195 5433553393307601219246293)
                ·
                  refine ⟨127348907655646903576085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5433553393307601219246293 127348907655646903576085)
                  ·
                    rfl

theorem cell23_2232100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_2232100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232100 prefixEnd_2232100 := by exact prefixLift 2232100
  have htrace : WordTrace (prefixWord ++ tailWord_2232100) baseStart_2232100 baseEnd_2232100 := by
    simpa [prefixWord, tailWord_2232100, baseEnd_2232100] using wordTrace_append hprefix tailTrace_2232100
  have hstable : (prefixWord ++ tailWord_2232100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232100).length < 2 ^ (prefixWord ++ tailWord_2232100).sum := by decide
  have hdescent : baseEnd_2232100 < baseStart_2232100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232210 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2232210 : Nat := 118140960795 + 2232210 * 2 ^ 59
def prefixEnd_2232210 : Nat := 4983230072969 + 3 ^ 40 * 2232210 * 2
def baseEnd_2232210 : Nat := 1146196651772816701809259

theorem tailTrace_2232210 : CollatzResearch.WordTrace tailWord_2232210 prefixEnd_2232210 1146196651772816701809259 := by
  unfold tailWord_2232210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20353846810772968990437521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54276924828727917307833389 20353846810772968990437521)
  ·
    refine ⟨15265385108079726742828141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20353846810772968990437521 15265385108079726742828141)
    ·
      refine ⟨5724519415529897528560553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15265385108079726742828141 5724519415529897528560553)
      ·
        refine ⟨4293389561647423146420415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5724519415529897528560553 4293389561647423146420415)
        ·
          refine ⟨6440084342471134719630623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293389561647423146420415 6440084342471134719630623)
          ·
            refine ⟨9660126513706702079445935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440084342471134719630623 9660126513706702079445935)
            ·
              refine ⟨14490189770560053119168903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9660126513706702079445935 14490189770560053119168903)
              ·
                refine ⟨21735284655840079678753355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14490189770560053119168903 21735284655840079678753355)
                ·
                  refine ⟨32602926983760119518130033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21735284655840079678753355 32602926983760119518130033)
                  ·
                    refine ⟨24452195237820089638597525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32602926983760119518130033 24452195237820089638597525)
                    ·
                      refine ⟨1146196651772816701809259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24452195237820089638597525 1146196651772816701809259)
                      ·
                        rfl

theorem cell23_2232210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2232210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232210 prefixEnd_2232210 := by exact prefixLift 2232210
  have htrace : WordTrace (prefixWord ++ tailWord_2232210) baseStart_2232210 baseEnd_2232210 := by
    simpa [prefixWord, tailWord_2232210, baseEnd_2232210] using wordTrace_append hprefix tailTrace_2232210
  have hstable : (prefixWord ++ tailWord_2232210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232210).length < 2 ^ (prefixWord ++ tailWord_2232210).sum := by decide
  have hdescent : baseEnd_2232210 < baseStart_2232210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232233 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_2232233 : Nat := 118140960795 + 2232233 * 2 ^ 59
def prefixEnd_2232233 : Nat := 4983230072969 + 3 ^ 40 * 2232233 * 2
def baseEnd_2232233 : Nat := 382069487275956703940551

theorem tailTrace_2232233 : CollatzResearch.WordTrace tailWord_2232233 prefixEnd_2232233 382069487275956703940551 := by
  unfold tailWord_2232233
  simp only [CollatzResearch.WordTrace]
  refine ⟨81416226122008550889837353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54277484081339033926558235 81416226122008550889837353)
  ·
    refine ⟨61062169591506413167378015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81416226122008550889837353 61062169591506413167378015)
    ·
      refine ⟨91593254387259619751067023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61062169591506413167378015 91593254387259619751067023)
      ·
        refine ⟨137389881580889429626600535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91593254387259619751067023 137389881580889429626600535)
        ·
          refine ⟨206084822371334144439900803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137389881580889429626600535 206084822371334144439900803)
          ·
            refine ⟨309127233557001216659851205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206084822371334144439900803 309127233557001216659851205)
            ·
              refine ⟨57961356291937728123722101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309127233557001216659851205 57961356291937728123722101)
              ·
                refine ⟨5433877152369162011598947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57961356291937728123722101 5433877152369162011598947)
                ·
                  refine ⟨8150815728553743017398421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433877152369162011598947 8150815728553743017398421)
                  ·
                    refine ⟨382069487275956703940551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8150815728553743017398421 382069487275956703940551)
                    ·
                      rfl

theorem cell23_2232233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_2232233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232233 prefixEnd_2232233 := by exact prefixLift 2232233
  have htrace : WordTrace (prefixWord ++ tailWord_2232233) baseStart_2232233 baseEnd_2232233 := by
    simpa [prefixWord, tailWord_2232233, baseEnd_2232233] using wordTrace_append hprefix tailTrace_2232233
  have hstable : (prefixWord ++ tailWord_2232233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232233).length < 2 ^ (prefixWord ++ tailWord_2232233).sum := by decide
  have hdescent : baseEnd_2232233 < baseStart_2232233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232243 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_2232243 : Nat := 118140960795 + 2232243 * 2 ^ 59
def prefixEnd_2232243 : Nat := 4983230072969 + 3 ^ 40 * 2232243 * 2
def baseEnd_2232243 : Nat := 1146213596634415072696607

theorem tailTrace_2232243 : CollatzResearch.WordTrace tailWord_2232243 prefixEnd_2232243 1146213596634415072696607 := by
  unfold tailWord_2232243
  simp only [CollatzResearch.WordTrace]
  refine ⟨81416590851972322597701383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54277727234648215065134255 81416590851972322597701383)
  ·
    refine ⟨122124886277958483896552075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81416590851972322597701383 122124886277958483896552075)
    ·
      refine ⟨183187329416937725844828113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122124886277958483896552075 183187329416937725844828113)
      ·
        refine ⟨137390497062703294383621085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183187329416937725844828113 137390497062703294383621085)
        ·
          refine ⟨51521436398513735393857907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137390497062703294383621085 51521436398513735393857907)
          ·
            refine ⟨77282154597770603090786861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51521436398513735393857907 77282154597770603090786861)
            ·
              refine ⟨28980807974163976159045073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77282154597770603090786861 28980807974163976159045073)
              ·
                refine ⟨21735605980622982119283805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28980807974163976159045073 21735605980622982119283805)
                ·
                  refine ⟨8150852242733618294731427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21735605980622982119283805 8150852242733618294731427)
                  ·
                    refine ⟨12226278364100427442097141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8150852242733618294731427 12226278364100427442097141)
                    ·
                      refine ⟨1146213596634415072696607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12226278364100427442097141 1146213596634415072696607)
                      ·
                        rfl

theorem cell23_2232243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_2232243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232243 prefixEnd_2232243 := by exact prefixLift 2232243
  have htrace : WordTrace (prefixWord ++ tailWord_2232243) baseStart_2232243 baseEnd_2232243 := by
    simpa [prefixWord, tailWord_2232243, baseEnd_2232243] using wordTrace_append hprefix tailTrace_2232243
  have hstable : (prefixWord ++ tailWord_2232243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232243).length < 2 ^ (prefixWord ++ tailWord_2232243).sum := by decide
  have hdescent : baseEnd_2232243 < baseStart_2232243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232323 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 8]
def baseStart_2232323 : Nat := 118140960795 + 2232323 * 2 ^ 59
def prefixEnd_2232323 : Nat := 4983230072969 + 3 ^ 40 * 2232323 * 2
def baseEnd_2232323 : Nat := 382084891695591586565413

theorem tailTrace_2232323 : CollatzResearch.WordTrace tailWord_2232323 prefixEnd_2232323 382084891695591586565413 := by
  unfold tailWord_2232323
  simp only [CollatzResearch.WordTrace]
  refine ⟨81419508691682496260613623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54279672461121664173742415 81419508691682496260613623)
  ·
    refine ⟨122129263037523744390920435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81419508691682496260613623 122129263037523744390920435)
    ·
      refine ⟨183193894556285616586380653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122129263037523744390920435 183193894556285616586380653)
      ·
        refine ⟨68697710458607106219892745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183193894556285616586380653 68697710458607106219892745)
        ·
          refine ⟨51523282843955329664919559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68697710458607106219892745 51523282843955329664919559)
          ·
            refine ⟨77284924265932994497379339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51523282843955329664919559 77284924265932994497379339)
            ·
              refine ⟨115927386398899491746069009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77284924265932994497379339 115927386398899491746069009)
              ·
                refine ⟨86945539799174618809551757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115927386398899491746069009 86945539799174618809551757)
                ·
                  refine ⟨32604577424690482053581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86945539799174618809551757 32604577424690482053581909)
                  ·
                    refine ⟨382084891695591586565413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32604577424690482053581909 382084891695591586565413)
                    ·
                      rfl

theorem cell23_2232323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_2232323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232323 prefixEnd_2232323 := by exact prefixLift 2232323
  have htrace : WordTrace (prefixWord ++ tailWord_2232323) baseStart_2232323 baseEnd_2232323 := by
    simpa [prefixWord, tailWord_2232323, baseEnd_2232323] using wordTrace_append hprefix tailTrace_2232323
  have hstable : (prefixWord ++ tailWord_2232323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232323).length < 2 ^ (prefixWord ++ tailWord_2232323).sum := by decide
  have hdescent : baseEnd_2232323 < baseStart_2232323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232398 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_2232398 : Nat := 118140960795 + 2232398 * 2 ^ 59
def prefixEnd_2232398 : Nat := 4983230072969 + 3 ^ 40 * 2232398 * 2
def baseEnd_2232398 : Nat := 1146293186135861966258395

theorem tailTrace_2232398 : CollatzResearch.WordTrace tailWord_2232398 prefixEnd_2232398 1146293186135861966258395 := by
  unfold tailWord_2232398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177780520801348008699231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54281496110940522713062565 10177780520801348008699231)
  ·
    refine ⟨15266670781202022013048847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10177780520801348008699231 15266670781202022013048847)
    ·
      refine ⟨22900006171803033019573271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15266670781202022013048847 22900006171803033019573271)
      ·
        refine ⟨34350009257704549529359907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22900006171803033019573271 34350009257704549529359907)
        ·
          refine ⟨51525013886556824294039861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34350009257704549529359907 51525013886556824294039861)
          ·
            refine ⟨4830470051864702277566237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51525013886556824294039861 4830470051864702277566237)
            ·
              refine ⟨1811426269449263354087339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830470051864702277566237 1811426269449263354087339)
              ·
                refine ⟨2717139404173895031131009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811426269449263354087339 2717139404173895031131009)
                ·
                  refine ⟨2037854553130421273348257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717139404173895031131009 2037854553130421273348257)
                  ·
                    refine ⟨1528390914847815955011193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2037854553130421273348257 1528390914847815955011193)
                    ·
                      refine ⟨1146293186135861966258395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528390914847815955011193 1146293186135861966258395)
                      ·
                        rfl

theorem cell23_2232398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_2232398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232398 prefixEnd_2232398 := by exact prefixLift 2232398
  have htrace : WordTrace (prefixWord ++ tailWord_2232398) baseStart_2232398 baseEnd_2232398 := by
    simpa [prefixWord, tailWord_2232398, baseEnd_2232398] using wordTrace_append hprefix tailTrace_2232398
  have hstable : (prefixWord ++ tailWord_2232398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232398).length < 2 ^ (prefixWord ++ tailWord_2232398).sum := by decide
  have hdescent : baseEnd_2232398 < baseStart_2232398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232407 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_2232407 : Nat := 118140960795 + 2232407 * 2 ^ 59
def prefixEnd_2232407 : Nat := 4983230072969 + 3 ^ 40 * 2232407 * 2
def baseEnd_2232407 : Nat := 1146297807461752431045853

theorem tailTrace_2232407 : CollatzResearch.WordTrace tailWord_2232407 prefixEnd_2232407 1146297807461752431045853 := by
  unfold tailWord_2232407
  simp only [CollatzResearch.WordTrace]
  refine ⟨81422572423378178606671475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54281714948918785737780983 81422572423378178606671475)
  ·
    refine ⟨122133858635067267910007213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81422572423378178606671475 122133858635067267910007213)
    ·
      refine ⟨45800196988150225466252705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122133858635067267910007213 45800196988150225466252705)
      ·
        refine ⟨34350147741112669099689529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45800196988150225466252705 34350147741112669099689529)
        ·
          refine ⟨25762610805834501824767147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34350147741112669099689529 25762610805834501824767147)
          ·
            refine ⟨38643916208751752737150721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25762610805834501824767147 38643916208751752737150721)
            ·
              refine ⟨28982937156563814552863041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38643916208751752737150721 28982937156563814552863041)
              ·
                refine ⟨21737202867422860914647281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28982937156563814552863041 21737202867422860914647281)
                ·
                  refine ⟨16302902150567145685985461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21737202867422860914647281 16302902150567145685985461)
                  ·
                    refine ⟨1528397076615669908061137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16302902150567145685985461 1528397076615669908061137)
                    ·
                      refine ⟨1146297807461752431045853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528397076615669908061137 1146297807461752431045853)
                      ·
                        rfl

theorem cell23_2232407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_2232407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232407 prefixEnd_2232407 := by exact prefixLift 2232407
  have htrace : WordTrace (prefixWord ++ tailWord_2232407) baseStart_2232407 baseEnd_2232407 := by
    simpa [prefixWord, tailWord_2232407, baseEnd_2232407] using wordTrace_append hprefix tailTrace_2232407
  have hstable : (prefixWord ++ tailWord_2232407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232407).length < 2 ^ (prefixWord ++ tailWord_2232407).sum := by decide
  have hdescent : baseEnd_2232407 < baseStart_2232407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232457 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_2232457 : Nat := 118140960795 + 2232457 * 2 ^ 59
def prefixEnd_2232457 : Nat := 4983230072969 + 3 ^ 40 * 2232457 * 2
def baseEnd_2232457 : Nat := 1146323481494477235420623

theorem tailTrace_2232457 : CollatzResearch.WordTrace tailWord_2232457 prefixEnd_2232457 1146323481494477235420623 := by
  unfold tailWord_2232457
  simp only [CollatzResearch.WordTrace]
  refine ⟨81424396073197037145991625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54282930715464691430661083 81424396073197037145991625)
  ·
    refine ⟨61068297054897777859493719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81424396073197037145991625 61068297054897777859493719)
    ·
      refine ⟨91602445582346666789240579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61068297054897777859493719 91602445582346666789240579)
      ·
        refine ⟨137403668373520000183860869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91602445582346666789240579 137403668373520000183860869)
        ·
          refine ⟨25763187820035000034473913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137403668373520000183860869 25763187820035000034473913)
          ·
            refine ⟨19322390865026250025855435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25763187820035000034473913 19322390865026250025855435)
            ·
              refine ⟨28983586297539375038783153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19322390865026250025855435 28983586297539375038783153)
              ·
                refine ⟨21737689723154531279087365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28983586297539375038783153 21737689723154531279087365)
                ·
                  refine ⟨4075816823091474614828881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21737689723154531279087365 4075816823091474614828881)
                  ·
                    refine ⟨3056862617318605961121661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075816823091474614828881 3056862617318605961121661)
                    ·
                      refine ⟨1146323481494477235420623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056862617318605961121661 1146323481494477235420623)
                      ·
                        rfl

theorem cell23_2232457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_2232457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232457 prefixEnd_2232457 := by exact prefixLift 2232457
  have htrace : WordTrace (prefixWord ++ tailWord_2232457) baseStart_2232457 baseEnd_2232457 := by
    simpa [prefixWord, tailWord_2232457, baseEnd_2232457] using wordTrace_append hprefix tailTrace_2232457
  have hstable : (prefixWord ++ tailWord_2232457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232457).length < 2 ^ (prefixWord ++ tailWord_2232457).sum := by decide
  have hdescent : baseEnd_2232457 < baseStart_2232457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232504 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2232504 : Nat := 118140960795 + 2232504 * 2 ^ 59
def prefixEnd_2232504 : Nat := 4983230072969 + 3 ^ 40 * 2232504 * 2
def baseEnd_2232504 : Nat := 1146347615085238551532907

theorem tailTrace_2232504 : CollatzResearch.WordTrace tailWord_2232504 prefixEnd_2232504 1146347615085238551532907 := by
  unfold tailWord_2232504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40713055152013382086476283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54284073536017842781968377 40713055152013382086476283)
  ·
    refine ⟨61069582728020073129714425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40713055152013382086476283 61069582728020073129714425)
    ·
      refine ⟨45802187046015054847285819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61069582728020073129714425 45802187046015054847285819)
      ·
        refine ⟨68703280569022582270928729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45802187046015054847285819 68703280569022582270928729)
        ·
          refine ⟨51527460426766936703196547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68703280569022582270928729 51527460426766936703196547)
          ·
            refine ⟨77291190640150405054794821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51527460426766936703196547 77291190640150405054794821)
            ·
              refine ⟨14492098245028200947774029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77291190640150405054794821 14492098245028200947774029)
              ·
                refine ⟨5434536841885575355415261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14492098245028200947774029 5434536841885575355415261)
                ·
                  refine ⟨2037951315707090758280723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5434536841885575355415261 2037951315707090758280723)
                  ·
                    refine ⟨3056926973560636137421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2037951315707090758280723 3056926973560636137421085)
                    ·
                      refine ⟨1146347615085238551532907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3056926973560636137421085 1146347615085238551532907)
                      ·
                        rfl

theorem cell23_2232504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2232504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232504 prefixEnd_2232504 := by exact prefixLift 2232504
  have htrace : WordTrace (prefixWord ++ tailWord_2232504) baseStart_2232504 baseEnd_2232504 := by
    simpa [prefixWord, tailWord_2232504, baseEnd_2232504] using wordTrace_append hprefix tailTrace_2232504
  have hstable : (prefixWord ++ tailWord_2232504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232504).length < 2 ^ (prefixWord ++ tailWord_2232504).sum := by decide
  have hdescent : baseEnd_2232504 < baseStart_2232504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232527 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_2232527 : Nat := 118140960795 + 2232527 * 2 ^ 59
def prefixEnd_2232527 : Nat := 4983230072969 + 3 ^ 40 * 2232527 * 2
def baseEnd_2232527 : Nat := 1146359425140291961545301

theorem tailTrace_2232527 : CollatzResearch.WordTrace tailWord_2232527 prefixEnd_2232527 1146359425140291961545301 := by
  unfold tailWord_2232527
  simp only [CollatzResearch.WordTrace]
  refine ⟨81426949182943439101039835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54284632788628959400693223 81426949182943439101039835)
  ·
    refine ⟨122140423774415158651559753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81426949182943439101039835 122140423774415158651559753)
    ·
      refine ⟨91605317830811368988669815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122140423774415158651559753 91605317830811368988669815)
      ·
        refine ⟨137407976746217053483004723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91605317830811368988669815 137407976746217053483004723)
        ·
          refine ⟨206111965119325580224507085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137407976746217053483004723 206111965119325580224507085)
          ·
            refine ⟨77291986919747092584190157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206111965119325580224507085 77291986919747092584190157)
            ·
              refine ⟨28984495094905159719071309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77291986919747092584190157 28984495094905159719071309)
              ·
                refine ⟨10869185660589434894651741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28984495094905159719071309 10869185660589434894651741)
                ·
                  refine ⟨4075944622721038085494403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10869185660589434894651741 4075944622721038085494403)
                  ·
                    refine ⟨6113916934081557128241605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4075944622721038085494403 6113916934081557128241605)
                    ·
                      refine ⟨1146359425140291961545301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6113916934081557128241605 1146359425140291961545301)
                      ·
                        rfl

theorem cell23_2232527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_2232527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232527 prefixEnd_2232527 := by exact prefixLift 2232527
  have htrace : WordTrace (prefixWord ++ tailWord_2232527) baseStart_2232527 baseEnd_2232527 := by
    simpa [prefixWord, tailWord_2232527, baseEnd_2232527] using wordTrace_append hprefix tailTrace_2232527
  have hstable : (prefixWord ++ tailWord_2232527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232527).length < 2 ^ (prefixWord ++ tailWord_2232527).sum := by decide
  have hdescent : baseEnd_2232527 < baseStart_2232527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232537 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_2232537 : Nat := 118140960795 + 2232537 * 2 ^ 59
def prefixEnd_2232537 : Nat := 4983230072969 + 3 ^ 40 * 2232537 * 2
def baseEnd_2232537 : Nat := 382121519982278974140085

theorem tailTrace_2232537 : CollatzResearch.WordTrace tailWord_2232537 prefixEnd_2232537 382121519982278974140085 := by
  unfold tailWord_2232537
  simp only [CollatzResearch.WordTrace]
  refine ⟨81427313912907210808903865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54284875941938140539269243 81427313912907210808903865)
  ·
    refine ⟨61070485434680408106677899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81427313912907210808903865 61070485434680408106677899)
    ·
      refine ⟨91605728152020612160016849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61070485434680408106677899 91605728152020612160016849)
      ·
        refine ⟨68704296114015459120012637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91605728152020612160016849 68704296114015459120012637)
        ·
          refine ⟨25764111042755797170004739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68704296114015459120012637 25764111042755797170004739)
          ·
            refine ⟨38646166564133695755007109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25764111042755797170004739 38646166564133695755007109)
            ·
              refine ⟨7246156230775067954063833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38646166564133695755007109 7246156230775067954063833)
              ·
                refine ⟨5434617173081300965547875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7246156230775067954063833 5434617173081300965547875)
                ·
                  refine ⟨8151925759621951448321813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5434617173081300965547875 8151925759621951448321813)
                  ·
                    refine ⟨382121519982278974140085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8151925759621951448321813 382121519982278974140085)
                    ·
                      rfl

theorem cell23_2232537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_2232537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232537 prefixEnd_2232537 := by exact prefixLift 2232537
  have htrace : WordTrace (prefixWord ++ tailWord_2232537) baseStart_2232537 baseEnd_2232537 := by
    simpa [prefixWord, tailWord_2232537, baseEnd_2232537] using wordTrace_append hprefix tailTrace_2232537
  have hstable : (prefixWord ++ tailWord_2232537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232537).length < 2 ^ (prefixWord ++ tailWord_2232537).sum := by decide
  have hdescent : baseEnd_2232537 < baseStart_2232537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232541 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2232541 : Nat := 118140960795 + 2232541 * 2 ^ 59
def prefixEnd_2232541 : Nat := 4983230072969 + 3 ^ 40 * 2232541 * 2
def baseEnd_2232541 : Nat := 382122204623151635590079

theorem tailTrace_2232541 : CollatzResearch.WordTrace tailWord_2232541 prefixEnd_2232541 382122204623151635590079 := by
  unfold tailWord_2232541
  simp only [CollatzResearch.WordTrace]
  refine ⟨81427459804892719492049477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54284973203261812994699651 81427459804892719492049477)
  ·
    refine ⟨15267648713417384904759277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81427459804892719492049477 15267648713417384904759277)
    ·
      refine ⟨5725368267531519339284729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15267648713417384904759277 5725368267531519339284729)
      ·
        refine ⟨4294026200648639504463547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5725368267531519339284729 4294026200648639504463547)
        ·
          refine ⟨6441039300972959256695321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294026200648639504463547 6441039300972959256695321)
          ·
            refine ⟨4830779475729719442521491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6441039300972959256695321 4830779475729719442521491)
            ·
              refine ⟨7246169213594579163782237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830779475729719442521491 7246169213594579163782237)
              ·
                refine ⟨2717313455097967186418339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7246169213594579163782237 2717313455097967186418339)
                ·
                  refine ⟨4075970182646950779627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717313455097967186418339 4075970182646950779627509)
                  ·
                    refine ⟨382122204623151635590079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4075970182646950779627509 382122204623151635590079)
                    ·
                      rfl

theorem cell23_2232541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2232541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232541 prefixEnd_2232541 := by exact prefixLift 2232541
  have htrace : WordTrace (prefixWord ++ tailWord_2232541) baseStart_2232541 baseEnd_2232541 := by
    simpa [prefixWord, tailWord_2232541, baseEnd_2232541] using wordTrace_append hprefix tailTrace_2232541
  have hstable : (prefixWord ++ tailWord_2232541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232541).length < 2 ^ (prefixWord ++ tailWord_2232541).sum := by decide
  have hdescent : baseEnd_2232541 < baseStart_2232541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232544 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2232544 : Nat := 118140960795 + 2232544 * 2 ^ 59
def prefixEnd_2232544 : Nat := 4983230072969 + 3 ^ 40 * 2232544 * 2
def baseEnd_2232544 : Nat := 1146368154311418395032723

theorem tailTrace_2232544 : CollatzResearch.WordTrace tailWord_2232544 prefixEnd_2232544 1146368154311418395032723 := by
  unfold tailWord_2232544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40713784611940925502204343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54285046149254567336272457 40713784611940925502204343)
  ·
    refine ⟨61070676917911388253306515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40713784611940925502204343 61070676917911388253306515)
    ·
      refine ⟨91606015376867082379959773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61070676917911388253306515 91606015376867082379959773)
      ·
        refine ⟨34352255766325155892484915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91606015376867082379959773 34352255766325155892484915)
        ·
          refine ⟨51528383649487733838727373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34352255766325155892484915 51528383649487733838727373)
          ·
            refine ⟨19323143868557900189522765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51528383649487733838727373 19323143868557900189522765)
            ·
              refine ⟨7246178950709212571071037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19323143868557900189522765 7246178950709212571071037)
              ·
                refine ⟨2717317106515954714151639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7246178950709212571071037 2717317106515954714151639)
                ·
                  refine ⟨4075975659773932071227459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717317106515954714151639 4075975659773932071227459)
                  ·
                    refine ⟨6113963489660898106841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4075975659773932071227459 6113963489660898106841189)
                    ·
                      refine ⟨1146368154311418395032723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6113963489660898106841189 1146368154311418395032723)
                      ·
                        rfl

theorem cell23_2232544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2232544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232544 prefixEnd_2232544 := by exact prefixLift 2232544
  have htrace : WordTrace (prefixWord ++ tailWord_2232544) baseStart_2232544 baseEnd_2232544 := by
    simpa [prefixWord, tailWord_2232544, baseEnd_2232544] using wordTrace_append hprefix tailTrace_2232544
  have hstable : (prefixWord ++ tailWord_2232544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232544).length < 2 ^ (prefixWord ++ tailWord_2232544).sum := by decide
  have hdescent : baseEnd_2232544 < baseStart_2232544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232554 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2232554 : Nat := 118140960795 + 2232554 * 2 ^ 59
def prefixEnd_2232554 : Nat := 4983230072969 + 3 ^ 40 * 2232554 * 2
def baseEnd_2232554 : Nat := 382124429705987785302559

theorem tailTrace_2232554 : CollatzResearch.WordTrace tailWord_2232554 prefixEnd_2232554 382124429705987785302559 := by
  unfold tailWord_2232554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356983488461405678068179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54285289302563748474848477 20356983488461405678068179)
  ·
    refine ⟨30535475232692108517102269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20356983488461405678068179 30535475232692108517102269)
    ·
      refine ⟨11450803212259540693913351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30535475232692108517102269 11450803212259540693913351)
      ·
        refine ⟨17176204818389311040870027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450803212259540693913351 17176204818389311040870027)
        ·
          refine ⟨25764307227583966561305041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17176204818389311040870027 25764307227583966561305041)
          ·
            refine ⟨19323230420687974920978781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25764307227583966561305041 19323230420687974920978781)
            ·
              refine ⟨7246211407757990595367043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19323230420687974920978781 7246211407757990595367043)
              ·
                refine ⟨10869317111636985893050565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246211407757990595367043 10869317111636985893050565)
                ·
                  refine ⟨2037996958431934854946981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10869317111636985893050565 2037996958431934854946981)
                  ·
                    refine ⟨382124429705987785302559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2037996958431934854946981 382124429705987785302559)
                    ·
                      rfl

theorem cell23_2232554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2232554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232554 prefixEnd_2232554 := by exact prefixLift 2232554
  have htrace : WordTrace (prefixWord ++ tailWord_2232554) baseStart_2232554 baseEnd_2232554 := by
    simpa [prefixWord, tailWord_2232554, baseEnd_2232554] using wordTrace_append hprefix tailTrace_2232554
  have hstable : (prefixWord ++ tailWord_2232554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232554).length < 2 ^ (prefixWord ++ tailWord_2232554).sum := by decide
  have hdescent : baseEnd_2232554 < baseStart_2232554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232561 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_2232561 : Nat := 118140960795 + 2232561 * 2 ^ 59
def prefixEnd_2232561 : Nat := 4983230072969 + 3 ^ 40 * 2232561 * 2
def baseEnd_2232561 : Nat := 1146376883482544828520145

theorem tailTrace_2232561 : CollatzResearch.WordTrace tailWord_2232561 prefixEnd_2232561 1146376883482544828520145 := by
  unfold tailWord_2232561
  simp only [CollatzResearch.WordTrace]
  refine ⟨81428189264820262907777537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54285459509880175271851691 81428189264820262907777537)
  ·
    refine ⟨61071141948615197180833153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81428189264820262907777537 61071141948615197180833153)
    ·
      refine ⟨45803356461461397885624865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61071141948615197180833153 45803356461461397885624865)
      ·
        refine ⟨34352517346096048414218649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45803356461461397885624865 34352517346096048414218649)
        ·
          refine ⟨25764388009572036310663987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34352517346096048414218649 25764388009572036310663987)
          ·
            refine ⟨38646582014358054465995981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25764388009572036310663987 38646582014358054465995981)
            ·
              refine ⟨14492468255384270424748493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38646582014358054465995981 14492468255384270424748493)
              ·
                refine ⟨5434675595769101409280685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14492468255384270424748493 5434675595769101409280685)
                ·
                  refine ⟨2038003348413413028480257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5434675595769101409280685 2038003348413413028480257)
                  ·
                    refine ⟨1528502511310059771360193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038003348413413028480257 1528502511310059771360193)
                    ·
                      refine ⟨1146376883482544828520145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528502511310059771360193 1146376883482544828520145)
                      ·
                        rfl

theorem cell23_2232561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_2232561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232561 prefixEnd_2232561 := by exact prefixLift 2232561
  have htrace : WordTrace (prefixWord ++ tailWord_2232561) baseStart_2232561 baseEnd_2232561 := by
    simpa [prefixWord, tailWord_2232561, baseEnd_2232561] using wordTrace_append hprefix tailTrace_2232561
  have hstable : (prefixWord ++ tailWord_2232561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232561).length < 2 ^ (prefixWord ++ tailWord_2232561).sum := by decide
  have hdescent : baseEnd_2232561 < baseStart_2232561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232574 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2232574 : Nat := 118140960795 + 2232574 * 2 ^ 59
def prefixEnd_2232574 : Nat := 4983230072969 + 3 ^ 40 * 2232574 * 2
def baseEnd_2232574 : Nat := 1146383558731053277657585

theorem tailTrace_2232574 : CollatzResearch.WordTrace tailWord_2232574 prefixEnd_2232574 1146383558731053277657585 := by
  unfold tailWord_2232574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178582926721645766000097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54285775609182110752000517 10178582926721645766000097)
  ·
    refine ⟨7633937195041234324500073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10178582926721645766000097 7633937195041234324500073)
    ·
      refine ⟨5725452896280925743375055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7633937195041234324500073 5725452896280925743375055)
      ·
        refine ⟨8588179344421388615062583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5725452896280925743375055 8588179344421388615062583)
        ·
          refine ⟨12882269016632082922593875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588179344421388615062583 12882269016632082922593875)
          ·
            refine ⟨19323403524948124383890813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12882269016632082922593875 19323403524948124383890813)
            ·
              refine ⟨7246276321855546643959055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19323403524948124383890813 7246276321855546643959055)
              ·
                refine ⟨10869414482783319965938583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246276321855546643959055 10869414482783319965938583)
                ·
                  refine ⟨16304121724174979948907875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10869414482783319965938583 16304121724174979948907875)
                  ·
                    refine ⟨24456182586262469923361813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16304121724174979948907875 24456182586262469923361813)
                    ·
                      refine ⟨1146383558731053277657585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24456182586262469923361813 1146383558731053277657585)
                      ·
                        rfl

theorem cell23_2232574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2232574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232574 prefixEnd_2232574 := by exact prefixLift 2232574
  have htrace : WordTrace (prefixWord ++ tailWord_2232574) baseStart_2232574 baseEnd_2232574 := by
    simpa [prefixWord, tailWord_2232574, baseEnd_2232574] using wordTrace_append hprefix tailTrace_2232574
  have hstable : (prefixWord ++ tailWord_2232574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232574).length < 2 ^ (prefixWord ++ tailWord_2232574).sum := by decide
  have hdescent : baseEnd_2232574 < baseStart_2232574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232578 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2232578 : Nat := 118140960795 + 2232578 * 2 ^ 59
def prefixEnd_2232578 : Nat := 4983230072969 + 3 ^ 40 * 2232578 * 2
def baseEnd_2232578 : Nat := 1146385612653671262007567

theorem tailTrace_2232578 : CollatzResearch.WordTrace tailWord_2232578 prefixEnd_2232578 1146385612653671262007567 := by
  unfold tailWord_2232578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357202326439668702786597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54285872870505783207430925 20357202326439668702786597)
  ·
    refine ⟨3816975436207437881772487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20357202326439668702786597 3816975436207437881772487)
    ·
      refine ⟨5725463154311156822658731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816975436207437881772487 5725463154311156822658731)
      ·
        refine ⟨8588194731466735233988097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5725463154311156822658731 8588194731466735233988097)
        ·
          refine ⟨6441146048600051425491073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8588194731466735233988097 6441146048600051425491073)
          ·
            refine ⟨4830859536450038569118305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6441146048600051425491073 4830859536450038569118305)
            ·
              refine ⟨3623144652337528926838729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830859536450038569118305 3623144652337528926838729)
              ·
                refine ⟨2717358489253146695129047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623144652337528926838729 2717358489253146695129047)
                ·
                  refine ⟨4076037733879720042693571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717358489253146695129047 4076037733879720042693571)
                  ·
                    refine ⟨6114056600819580064040357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4076037733879720042693571 6114056600819580064040357)
                    ·
                      refine ⟨1146385612653671262007567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6114056600819580064040357 1146385612653671262007567)
                      ·
                        rfl

theorem cell23_2232578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2232578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232578 prefixEnd_2232578 := by exact prefixLift 2232578
  have htrace : WordTrace (prefixWord ++ tailWord_2232578) baseStart_2232578 baseEnd_2232578 := by
    simpa [prefixWord, tailWord_2232578, baseEnd_2232578] using wordTrace_append hprefix tailTrace_2232578
  have hstable : (prefixWord ++ tailWord_2232578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232578).length < 2 ^ (prefixWord ++ tailWord_2232578).sum := by decide
  have hdescent : baseEnd_2232578 < baseStart_2232578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232584 : List Nat := [2, 1, 3, 2, 3, 1, 4, 7]
def baseStart_2232584 : Nat := 118140960795 + 2232584 * 2 ^ 59
def prefixEnd_2232584 : Nat := 4983230072969 + 3 ^ 40 * 2232584 * 2
def baseEnd_2232584 : Nat := 42458840501392527353057

theorem tailTrace_2232584 : CollatzResearch.WordTrace tailWord_2232584 prefixEnd_2232584 42458840501392527353057 := by
  unfold tailWord_2232584
  simp only [CollatzResearch.WordTrace]
  refine ⟨40714514071868468917932403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54286018762491291890576537 40714514071868468917932403)
  ·
    refine ⟨61071771107802703376898605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40714514071868468917932403 61071771107802703376898605)
    ·
      refine ⟨22901914165426013766336977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61071771107802703376898605 22901914165426013766336977)
      ·
        refine ⟨17176435624069510324752733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22901914165426013766336977 17176435624069510324752733)
        ·
          refine ⟨6441163359026066371782275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17176435624069510324752733 6441163359026066371782275)
          ·
            refine ⟨9661745038539099557673413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6441163359026066371782275 9661745038539099557673413)
            ·
              refine ⟨1811577194726081167063765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9661745038539099557673413 1811577194726081167063765)
              ·
                refine ⟨42458840501392527353057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1811577194726081167063765 42458840501392527353057)
                ·
                  rfl

theorem cell23_2232584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 7].length) (baseStart_2232584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232584 prefixEnd_2232584 := by exact prefixLift 2232584
  have htrace : WordTrace (prefixWord ++ tailWord_2232584) baseStart_2232584 baseEnd_2232584 := by
    simpa [prefixWord, tailWord_2232584, baseEnd_2232584] using wordTrace_append hprefix tailTrace_2232584
  have hstable : (prefixWord ++ tailWord_2232584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232584).length < 2 ^ (prefixWord ++ tailWord_2232584).sum := by decide
  have hdescent : baseEnd_2232584 < baseStart_2232584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232611 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2232611 : Nat := 118140960795 + 2232611 * 2 ^ 59
def prefixEnd_2232611 : Nat := 4983230072969 + 3 ^ 40 * 2232611 * 2
def baseEnd_2232611 : Nat := 1146402557515269632894915

theorem tailTrace_2232611 : CollatzResearch.WordTrace tailWord_2232611 prefixEnd_2232611 1146402557515269632894915 := by
  unfold tailWord_2232611
  simp only [CollatzResearch.WordTrace]
  refine ⟨81430012914639121447097687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54286675276426080964731791 81430012914639121447097687)
  ·
    refine ⟨122145019371958682170646531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81430012914639121447097687 122145019371958682170646531)
    ·
      refine ⟨183217529057938023255969797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122145019371958682170646531 183217529057938023255969797)
      ·
        refine ⟨34353286698363379360494337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183217529057938023255969797 34353286698363379360494337)
        ·
          refine ⟨25764965023772534520370753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34353286698363379360494337 25764965023772534520370753)
          ·
            refine ⟨19323723767829400890278065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25764965023772534520370753 19323723767829400890278065)
            ·
              refine ⟨14492792825872050667708549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19323723767829400890278065 14492792825872050667708549)
              ·
                refine ⟨2717398654851009500195353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14492792825872050667708549 2717398654851009500195353)
                ·
                  refine ⟨2038048991138257125146515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717398654851009500195353 2038048991138257125146515)
                  ·
                    refine ⟨3057073486707385687719773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2038048991138257125146515 3057073486707385687719773)
                    ·
                      refine ⟨1146402557515269632894915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3057073486707385687719773 1146402557515269632894915)
                      ·
                        rfl

theorem cell23_2232611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2232611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232611 prefixEnd_2232611 := by exact prefixLift 2232611
  have htrace : WordTrace (prefixWord ++ tailWord_2232611) baseStart_2232611 baseEnd_2232611 := by
    simpa [prefixWord, tailWord_2232611, baseEnd_2232611] using wordTrace_append hprefix tailTrace_2232611
  have hstable : (prefixWord ++ tailWord_2232611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232611).length < 2 ^ (prefixWord ++ tailWord_2232611).sum := by decide
  have hdescent : baseEnd_2232611 < baseStart_2232611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232612 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_2232612 : Nat := 118140960795 + 2232612 * 2 ^ 59
def prefixEnd_2232612 : Nat := 4983230072969 + 3 ^ 40 * 2232612 * 2
def baseEnd_2232612 : Nat := 1146403070995924128982411

theorem tailTrace_2232612 : CollatzResearch.WordTrace tailWord_2232612 prefixEnd_2232612 1146403070995924128982411 := by
  unfold tailWord_2232612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40715024693817749308942045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54286699591756999078589393 40715024693817749308942045)
  ·
    refine ⟨15268134260181655990853267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40715024693817749308942045 15268134260181655990853267)
    ·
      refine ⟨22902201390272483986279901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15268134260181655990853267 22902201390272483986279901)
      ·
        refine ⟨8588325521352181494854963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22902201390272483986279901 8588325521352181494854963)
        ·
          refine ⟨12882488282028272242282445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588325521352181494854963 12882488282028272242282445)
          ·
            refine ⟨4830933105760602090855917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12882488282028272242282445 4830933105760602090855917)
            ·
              refine ⟨1811599914660225784070969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830933105760602090855917 1811599914660225784070969)
              ·
                refine ⟨1358699935995169338053227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811599914660225784070969 1358699935995169338053227)
                ·
                  refine ⟨2038049903992754007079841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358699935995169338053227 2038049903992754007079841)
                  ·
                    refine ⟨1528537427994565505309881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038049903992754007079841 1528537427994565505309881)
                    ·
                      refine ⟨1146403070995924128982411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528537427994565505309881 1146403070995924128982411)
                      ·
                        rfl

theorem cell23_2232612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_2232612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232612 prefixEnd_2232612 := by exact prefixLift 2232612
  have htrace : WordTrace (prefixWord ++ tailWord_2232612) baseStart_2232612 baseEnd_2232612 := by
    simpa [prefixWord, tailWord_2232612, baseEnd_2232612] using wordTrace_append hprefix tailTrace_2232612
  have hstable : (prefixWord ++ tailWord_2232612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232612).length < 2 ^ (prefixWord ++ tailWord_2232612).sum := by decide
  have hdescent : baseEnd_2232612 < baseStart_2232612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232622 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2232622 : Nat := 118140960795 + 2232622 * 2 ^ 59
def prefixEnd_2232622 : Nat := 4983230072969 + 3 ^ 40 * 2232622 * 2
def baseEnd_2232622 : Nat := 382136068600823029952455

theorem tailTrace_2232622 : CollatzResearch.WordTrace tailWord_2232622 prefixEnd_2232622 382136068600823029952455 := by
  unfold tailWord_2232622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178801764699908790718515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54286942745066180217165413 10178801764699908790718515)
  ·
    refine ⟨15268202647049863186077773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10178801764699908790718515 15268202647049863186077773)
    ·
      refine ⟨5725575992643698694779165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15268202647049863186077773 5725575992643698694779165)
      ·
        refine ⟨2147090997241387010542187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5725575992643698694779165 2147090997241387010542187)
        ·
          refine ⟨3220636495862080515813281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147090997241387010542187 3220636495862080515813281)
          ·
            refine ⟨2415477371896560386859961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3220636495862080515813281 2415477371896560386859961)
            ·
              refine ⟨1811608028922420290144971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415477371896560386859961 1811608028922420290144971)
              ·
                refine ⟨2717412043383630435217457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811608028922420290144971 2717412043383630435217457)
                ·
                  refine ⟨2038059032537722826413093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717412043383630435217457 2038059032537722826413093)
                  ·
                    refine ⟨382136068600823029952455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038059032537722826413093 382136068600823029952455)
                    ·
                      rfl

theorem cell23_2232622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2232622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232622 prefixEnd_2232622 := by exact prefixLift 2232622
  have htrace : WordTrace (prefixWord ++ tailWord_2232622) baseStart_2232622 baseEnd_2232622 := by
    simpa [prefixWord, tailWord_2232622, baseEnd_2232622] using wordTrace_append hprefix tailTrace_2232622
  have hstable : (prefixWord ++ tailWord_2232622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232622).length < 2 ^ (prefixWord ++ tailWord_2232622).sum := by decide
  have hdescent : baseEnd_2232622 < baseStart_2232622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232627 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 8]
def baseStart_2232627 : Nat := 118140960795 + 2232627 * 2 ^ 59
def prefixEnd_2232627 : Nat := 4983230072969 + 3 ^ 40 * 2232627 * 2
def baseEnd_2232627 : Nat := 382136924401913856764947

theorem tailTrace_2232627 : CollatzResearch.WordTrace tailWord_2232627 prefixEnd_2232627 382136924401913856764947 := by
  unfold tailWord_2232627
  simp only [CollatzResearch.WordTrace]
  refine ⟨81430596482581156179680135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54287064321720770786453423 81430596482581156179680135)
  ·
    refine ⟨122145894723871734269520203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81430596482581156179680135 122145894723871734269520203)
    ·
      refine ⟨183218842085807601404280305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122145894723871734269520203 183218842085807601404280305)
      ·
        refine ⟨137414131564355701053210229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183218842085807601404280305 137414131564355701053210229)
        ·
          refine ⟨12882574834158346973738459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137414131564355701053210229 12882574834158346973738459)
          ·
            refine ⟨19323862251237520460607689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12882574834158346973738459 19323862251237520460607689)
            ·
              refine ⟨14492896688428140345455767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19323862251237520460607689 14492896688428140345455767)
              ·
                refine ⟨21739345032642210518183651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14492896688428140345455767 21739345032642210518183651)
                ·
                  refine ⟨32609017548963315777275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21739345032642210518183651 32609017548963315777275477)
                  ·
                    refine ⟨382136924401913856764947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32609017548963315777275477 382136924401913856764947)
                    ·
                      rfl

theorem cell23_2232627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_2232627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232627 prefixEnd_2232627 := by exact prefixLift 2232627
  have htrace : WordTrace (prefixWord ++ tailWord_2232627) baseStart_2232627 baseEnd_2232627 := by
    simpa [prefixWord, tailWord_2232627, baseEnd_2232627] using wordTrace_append hprefix tailTrace_2232627
  have hstable : (prefixWord ++ tailWord_2232627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232627).length < 2 ^ (prefixWord ++ tailWord_2232627).sum := by decide
  have hdescent : baseEnd_2232627 < baseStart_2232627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232638 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_2232638 : Nat := 118140960795 + 2232638 * 2 ^ 59
def prefixEnd_2232638 : Nat := 4983230072969 + 3 ^ 40 * 2232638 * 2
def baseEnd_2232638 : Nat := 1146416421492941027257291

theorem tailTrace_2232638 : CollatzResearch.WordTrace tailWord_2232638 prefixEnd_2232638 1146416421492941027257291 := by
  unfold tailWord_2232638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178874710692663132291321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54287331790360870038887045 10178874710692663132291321)
  ·
    refine ⟨7634156033019497349218491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10178874710692663132291321 7634156033019497349218491)
    ·
      refine ⟨11451234049529246023827737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634156033019497349218491 11451234049529246023827737)
      ·
        refine ⟨8588425537146934517870803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11451234049529246023827737 8588425537146934517870803)
        ·
          refine ⟨12882638305720401776806205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588425537146934517870803 12882638305720401776806205)
          ·
            refine ⟨4830989364645150666302327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12882638305720401776806205 4830989364645150666302327)
            ·
              refine ⟨7246484046967725999453491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830989364645150666302327 7246484046967725999453491)
              ·
                refine ⟨10869726070451588999180237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246484046967725999453491 10869726070451588999180237)
                ·
                  refine ⟨4076147276419345874692589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10869726070451588999180237 4076147276419345874692589)
                  ·
                    refine ⟨1528555228657254703009721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4076147276419345874692589 1528555228657254703009721)
                    ·
                      refine ⟨1146416421492941027257291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528555228657254703009721 1146416421492941027257291)
                      ·
                        rfl

theorem cell23_2232638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_2232638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232638 prefixEnd_2232638 := by exact prefixLift 2232638
  have htrace : WordTrace (prefixWord ++ tailWord_2232638) baseStart_2232638 baseEnd_2232638 := by
    simpa [prefixWord, tailWord_2232638, baseEnd_2232638] using wordTrace_append hprefix tailTrace_2232638
  have hstable : (prefixWord ++ tailWord_2232638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232638).length < 2 ^ (prefixWord ++ tailWord_2232638).sum := by decide
  have hdescent : baseEnd_2232638 < baseStart_2232638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 4, 2, 2]
def baseStart_2232651 : Nat := 118140960795 + 2232651 * 2 ^ 59
def prefixEnd_2232651 : Nat := 4983230072969 + 3 ^ 40 * 2232651 * 2
def baseEnd_2232651 : Nat := 1146423096741449476394731

theorem tailTrace_2232651 : CollatzResearch.WordTrace tailWord_2232651 prefixEnd_2232651 1146423096741449476394731 := by
  unfold tailWord_2232651
  simp only [CollatzResearch.WordTrace]
  refine ⟨81431471834494208278553807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54287647889662805519035871 81431471834494208278553807)
  ·
    refine ⟨122147207751741312417830711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81431471834494208278553807 122147207751741312417830711)
    ·
      refine ⟨183220811627611968626746067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122147207751741312417830711 183220811627611968626746067)
      ·
        refine ⟨274831217441417952940119101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183220811627611968626746067 274831217441417952940119101)
        ·
          refine ⟨103061706540531732352544663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274831217441417952940119101 103061706540531732352544663)
          ·
            refine ⟨154592559810797598528816995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103061706540531732352544663 154592559810797598528816995)
            ·
              refine ⟨231888839716196397793225493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154592559810797598528816995 231888839716196397793225493)
              ·
                refine ⟨10869789361696706146557445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231888839716196397793225493 10869789361696706146557445)
                ·
                  refine ⟨2038085505318132402479521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10869789361696706146557445 2038085505318132402479521)
                  ·
                    refine ⟨1528564128988599301859641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038085505318132402479521 1528564128988599301859641)
                    ·
                      refine ⟨1146423096741449476394731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528564128988599301859641 1146423096741449476394731)
                      ·
                        rfl

theorem cell23_2232651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2, 2].length) (baseStart_2232651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232651 prefixEnd_2232651 := by exact prefixLift 2232651
  have htrace : WordTrace (prefixWord ++ tailWord_2232651) baseStart_2232651 baseEnd_2232651 := by
    simpa [prefixWord, tailWord_2232651, baseEnd_2232651] using wordTrace_append hprefix tailTrace_2232651
  have hstable : (prefixWord ++ tailWord_2232651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232651).length < 2 ^ (prefixWord ++ tailWord_2232651).sum := by decide
  have hdescent : baseEnd_2232651 < baseStart_2232651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232706 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2232706 : Nat := 118140960795 + 2232706 * 2 ^ 59
def prefixEnd_2232706 : Nat := 4983230072969 + 3 ^ 40 * 2232706 * 2
def baseEnd_2232706 : Nat := 1146451338177446761206979

theorem tailTrace_2232706 : CollatzResearch.WordTrace tailWord_2232706 prefixEnd_2232706 1146451338177446761206979 := by
  unfold tailWord_2232706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358369462323738167951493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54288985232863301781203981 20358369462323738167951493)
  ·
    refine ⟨3817194274185700906490905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20358369462323738167951493 3817194274185700906490905)
    ·
      refine ⟨2862895705639275679868179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3817194274185700906490905 2862895705639275679868179)
      ·
        refine ⟨4294343558458913519802269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862895705639275679868179 4294343558458913519802269)
        ·
          refine ⟨1610378834422092569925851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4294343558458913519802269 1610378834422092569925851)
          ·
            refine ⟨2415568251633138854888777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610378834422092569925851 2415568251633138854888777)
            ·
              refine ⟨1811676188724854141166583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415568251633138854888777 1811676188724854141166583)
              ·
                refine ⟨2717514283087281211749875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811676188724854141166583 2717514283087281211749875)
                ·
                  refine ⟨4076271424630921817624813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717514283087281211749875 4076271424630921817624813)
                  ·
                    refine ⟨1528601784236595681609305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4076271424630921817624813 1528601784236595681609305)
                    ·
                      refine ⟨1146451338177446761206979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528601784236595681609305 1146451338177446761206979)
                      ·
                        rfl

theorem cell23_2232706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2232706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232706 prefixEnd_2232706 := by exact prefixLift 2232706
  have htrace : WordTrace (prefixWord ++ tailWord_2232706) baseStart_2232706 baseEnd_2232706 := by
    simpa [prefixWord, tailWord_2232706, baseEnd_2232706] using wordTrace_append hprefix tailTrace_2232706
  have hstable : (prefixWord ++ tailWord_2232706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232706).length < 2 ^ (prefixWord ++ tailWord_2232706).sum := by decide
  have hdescent : baseEnd_2232706 < baseStart_2232706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232741 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_2232741 : Nat := 118140960795 + 2232741 * 2 ^ 59
def prefixEnd_2232741 : Nat := 4983230072969 + 3 ^ 40 * 2232741 * 2
def baseEnd_2232741 : Nat := 1146469310000354124269317

theorem tailTrace_2232741 : CollatzResearch.WordTrace tailWord_2232741 prefixEnd_2232741 1146469310000354124269317 := by
  unfold tailWord_2232741
  simp only [CollatzResearch.WordTrace]
  refine ⟨81434754404168153649330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54289836269445435766220051 81434754404168153649330077)
  ·
    refine ⟨30538032901563057618498779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81434754404168153649330077 30538032901563057618498779)
    ·
      refine ⟨45807049352344586427748169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30538032901563057618498779 45807049352344586427748169)
      ·
        refine ⟨34355287014258439820811127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45807049352344586427748169 34355287014258439820811127)
        ·
          refine ⟨51532930521387659731216691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34355287014258439820811127 51532930521387659731216691)
          ·
            refine ⟨77299395782081489596825037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51532930521387659731216691 77299395782081489596825037)
            ·
              refine ⟨28987273418280558598809389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77299395782081489596825037 28987273418280558598809389)
              ·
                refine ⟨10870227531855209474553521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28987273418280558598809389 10870227531855209474553521)
                ·
                  refine ⟨8152670648891407105915141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10870227531855209474553521 8152670648891407105915141)
                  ·
                    refine ⟨1528625746667138832359089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8152670648891407105915141 1528625746667138832359089)
                    ·
                      refine ⟨1146469310000354124269317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528625746667138832359089 1146469310000354124269317)
                      ·
                        rfl

theorem cell23_2232741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_2232741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232741 prefixEnd_2232741 := by exact prefixLift 2232741
  have htrace : WordTrace (prefixWord ++ tailWord_2232741) baseStart_2232741 baseEnd_2232741 := by
    simpa [prefixWord, tailWord_2232741, baseEnd_2232741] using wordTrace_append hprefix tailTrace_2232741
  have hstable : (prefixWord ++ tailWord_2232741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232741).length < 2 ^ (prefixWord ++ tailWord_2232741).sum := by decide
  have hdescent : baseEnd_2232741 < baseStart_2232741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232754 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2232754 : Nat := 118140960795 + 2232754 * 2 ^ 59
def prefixEnd_2232754 : Nat := 4983230072969 + 3 ^ 40 * 2232754 * 2
def baseEnd_2232754 : Nat := 1146475985248862573406757

theorem tailTrace_2232754 : CollatzResearch.WordTrace tailWord_2232754 prefixEnd_2232754 1146475985248862573406757 := by
  unfold tailWord_2232754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358807138280264217388329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54290152368747371246368877 20358807138280264217388329)
  ·
    refine ⟨15269105353710198163041247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20358807138280264217388329 15269105353710198163041247)
    ·
      refine ⟨22903658030565297244561871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15269105353710198163041247 22903658030565297244561871)
      ·
        refine ⟨34355487045847945866842807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22903658030565297244561871 34355487045847945866842807)
        ·
          refine ⟨51533230568771918800264211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34355487045847945866842807 51533230568771918800264211)
          ·
            refine ⟨77299845853157878200396317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51533230568771918800264211 77299845853157878200396317)
            ·
              refine ⟨28987442194934204325148619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77299845853157878200396317 28987442194934204325148619)
              ·
                refine ⟨43481163292401306487722929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28987442194934204325148619 43481163292401306487722929)
                ·
                  refine ⟨32610872469300979865792197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43481163292401306487722929 32610872469300979865792197)
                  ·
                    refine ⟨6114538587993933724836037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32610872469300979865792197 6114538587993933724836037)
                    ·
                      refine ⟨1146475985248862573406757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6114538587993933724836037 1146475985248862573406757)
                      ·
                        rfl

theorem cell23_2232754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2232754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232754 prefixEnd_2232754 := by exact prefixLift 2232754
  have htrace : WordTrace (prefixWord ++ tailWord_2232754) baseStart_2232754 baseEnd_2232754 := by
    simpa [prefixWord, tailWord_2232754, baseEnd_2232754] using wordTrace_append hprefix tailTrace_2232754
  have hstable : (prefixWord ++ tailWord_2232754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232754).length < 2 ^ (prefixWord ++ tailWord_2232754).sum := by decide
  have hdescent : baseEnd_2232754 < baseStart_2232754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232761 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2232761 : Nat := 118140960795 + 2232761 * 2 ^ 59
def prefixEnd_2232761 : Nat := 4983230072969 + 3 ^ 40 * 2232761 * 2
def baseEnd_2232761 : Nat := 1146479579613444046019225

theorem tailTrace_2232761 : CollatzResearch.WordTrace tailWord_2232761 prefixEnd_2232761 1146479579613444046019225 := by
  unfold tailWord_2232761
  simp only [CollatzResearch.WordTrace]
  refine ⟨81435483864095697065058137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54290322576063798043372091 81435483864095697065058137)
  ·
    refine ⟨61076612898071772798793603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81435483864095697065058137 61076612898071772798793603)
    ·
      refine ⟨91614919347107659198190405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61076612898071772798793603 91614919347107659198190405)
      ·
        refine ⟨17177797377582686099660701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91614919347107659198190405 17177797377582686099660701)
        ·
          refine ⟨6441674016593507287372763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17177797377582686099660701 6441674016593507287372763)
          ·
            refine ⟨9662511024890260931059145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6441674016593507287372763 9662511024890260931059145)
            ·
              refine ⟨7246883268667695698294359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9662511024890260931059145 7246883268667695698294359)
              ·
                refine ⟨10870324903001543547441539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246883268667695698294359 10870324903001543547441539)
                ·
                  refine ⟨16305487354502315321162309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10870324903001543547441539 16305487354502315321162309)
                  ·
                    refine ⟨3057278878969184122717933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16305487354502315321162309 3057278878969184122717933)
                    ·
                      refine ⟨1146479579613444046019225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3057278878969184122717933 1146479579613444046019225)
                      ·
                        rfl

theorem cell23_2232761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2232761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232761 prefixEnd_2232761 := by exact prefixLift 2232761
  have htrace : WordTrace (prefixWord ++ tailWord_2232761) baseStart_2232761 baseEnd_2232761 := by
    simpa [prefixWord, tailWord_2232761, baseEnd_2232761] using wordTrace_append hprefix tailTrace_2232761
  have hstable : (prefixWord ++ tailWord_2232761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232761).length < 2 ^ (prefixWord ++ tailWord_2232761).sum := by decide
  have hdescent : baseEnd_2232761 < baseStart_2232761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232845 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2232845 : Nat := 118140960795 + 2232845 * 2 ^ 59
def prefixEnd_2232845 : Nat := 4983230072969 + 3 ^ 40 * 2232845 * 2
def baseEnd_2232845 : Nat := 382174237329473905789613

theorem tailTrace_2232845 : CollatzResearch.WordTrace tailWord_2232845 prefixEnd_2232845 382174237329473905789613 := by
  unfold tailWord_2232845
  simp only [CollatzResearch.WordTrace]
  refine ⟨81438547595791379411115989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54292365063860919607410659 81438547595791379411115989)
  ·
    refine ⟨1908715959276360454948031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81438547595791379411115989 1908715959276360454948031)
    ·
      refine ⟨2863073938914540682422047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908715959276360454948031 2863073938914540682422047)
      ·
        refine ⟨4294610908371811023633071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863073938914540682422047 4294610908371811023633071)
        ·
          refine ⟨6441916362557716535449607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294610908371811023633071 6441916362557716535449607)
          ·
            refine ⟨9662874543836574803174411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6441916362557716535449607 9662874543836574803174411)
            ·
              refine ⟨14494311815754862204761617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9662874543836574803174411 14494311815754862204761617)
              ·
                refine ⟨10870733861816146653571213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14494311815754862204761617 10870733861816146653571213)
                ·
                  refine ⟨4076525198181054995089205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10870733861816146653571213 4076525198181054995089205)
                  ·
                    refine ⟨382174237329473905789613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4076525198181054995089205 382174237329473905789613)
                    ·
                      rfl

theorem cell23_2232845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2232845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232845 prefixEnd_2232845 := by exact prefixLift 2232845
  have htrace : WordTrace (prefixWord ++ tailWord_2232845) baseStart_2232845 baseEnd_2232845 := by
    simpa [prefixWord, tailWord_2232845, baseEnd_2232845] using wordTrace_append hprefix tailTrace_2232845
  have hstable : (prefixWord ++ tailWord_2232845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232845).length < 2 ^ (prefixWord ++ tailWord_2232845).sum := by decide
  have hdescent : baseEnd_2232845 < baseStart_2232845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232851 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3]
def baseStart_2232851 : Nat := 118140960795 + 2232851 * 2 ^ 59
def prefixEnd_2232851 : Nat := 4983230072969 + 3 ^ 40 * 2232851 * 2
def baseEnd_2232851 : Nat := 1146525792872348693893811

theorem tailTrace_2232851 : CollatzResearch.WordTrace tailWord_2232851 prefixEnd_2232851 1146525792872348693893811 := by
  unfold tailWord_2232851
  simp only [CollatzResearch.WordTrace]
  refine ⟨81438766433769642435834407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54292510955846428290556271 81438766433769642435834407)
  ·
    refine ⟨122158149650654463653751611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81438766433769642435834407 122158149650654463653751611)
    ·
      refine ⟨183237224475981695480627417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122158149650654463653751611 183237224475981695480627417)
      ·
        refine ⟨137427918356986271610470563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183237224475981695480627417 137427918356986271610470563)
        ·
          refine ⟨206141877535479407415705845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137427918356986271610470563 206141877535479407415705845)
          ·
            refine ⟨19325801018951194445222423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206141877535479407415705845 19325801018951194445222423)
            ·
              refine ⟨28988701528426791667833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19325801018951194445222423 28988701528426791667833635)
              ·
                refine ⟨43483052292640187501750453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28988701528426791667833635 43483052292640187501750453)
                ·
                  refine ⟨4076536152435017578289105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43483052292640187501750453 4076536152435017578289105)
                  ·
                    refine ⟨3057402114326263183716829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076536152435017578289105 3057402114326263183716829)
                    ·
                      refine ⟨1146525792872348693893811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3057402114326263183716829 1146525792872348693893811)
                      ·
                        rfl

theorem cell23_2232851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_2232851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232851 prefixEnd_2232851 := by exact prefixLift 2232851
  have htrace : WordTrace (prefixWord ++ tailWord_2232851) baseStart_2232851 baseEnd_2232851 := by
    simpa [prefixWord, tailWord_2232851, baseEnd_2232851] using wordTrace_append hprefix tailTrace_2232851
  have hstable : (prefixWord ++ tailWord_2232851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232851).length < 2 ^ (prefixWord ++ tailWord_2232851).sum := by decide
  have hdescent : baseEnd_2232851 < baseStart_2232851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232858 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_2232858 : Nat := 118140960795 + 2232858 * 2 ^ 59
def prefixEnd_2232858 : Nat := 4983230072969 + 3 ^ 40 * 2232858 * 2
def baseEnd_2232858 : Nat := 382176462412310055502093

theorem tailTrace_2232858 : CollatzResearch.WordTrace tailWord_2232858 prefixEnd_2232858 382176462412310055502093 := by
  unfold tailWord_2232858
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359755436186070657834807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54292681163162855087559485 20359755436186070657834807)
  ·
    refine ⟨30539633154279105986752211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20359755436186070657834807 30539633154279105986752211)
    ·
      refine ⟨45809449731418658980128317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30539633154279105986752211 45809449731418658980128317)
      ·
        refine ⟨17178543649281997117548119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45809449731418658980128317 17178543649281997117548119)
        ·
          refine ⟨25767815473922995676322179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178543649281997117548119 25767815473922995676322179)
          ·
            refine ⟨38651723210884493514483269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25767815473922995676322179 38651723210884493514483269)
            ·
              refine ⟨7247198102040842533965613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38651723210884493514483269 7247198102040842533965613)
              ·
                refine ⟨2717699288265315950237105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7247198102040842533965613 2717699288265315950237105)
                ·
                  refine ⟨2038274466198986962677829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717699288265315950237105 2038274466198986962677829)
                  ·
                    refine ⟨382176462412310055502093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038274466198986962677829 382176462412310055502093)
                    ·
                      rfl

theorem cell23_2232858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_2232858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232858 prefixEnd_2232858 := by exact prefixLift 2232858
  have htrace : WordTrace (prefixWord ++ tailWord_2232858) baseStart_2232858 baseEnd_2232858 := by
    simpa [prefixWord, tailWord_2232858, baseEnd_2232858] using wordTrace_append hprefix tailTrace_2232858
  have hstable : (prefixWord ++ tailWord_2232858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232858).length < 2 ^ (prefixWord ++ tailWord_2232858).sum := by decide
  have hdescent : baseEnd_2232858 < baseStart_2232858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232865 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2232865 : Nat := 118140960795 + 2232865 * 2 ^ 59
def prefixEnd_2232865 : Nat := 4983230072969 + 3 ^ 40 * 2232865 * 2
def baseEnd_2232865 : Nat := 1146532981601511639118747

theorem tailTrace_2232865 : CollatzResearch.WordTrace tailWord_2232865 prefixEnd_2232865 1146532981601511639118747 := by
  unfold tailWord_2232865
  simp only [CollatzResearch.WordTrace]
  refine ⟨81439277055718922826844049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54292851370479281884562699 81439277055718922826844049)
  ·
    refine ⟨61079457791789192120133037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81439277055718922826844049 61079457791789192120133037)
    ·
      refine ⟨22904796671920947045049889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61079457791789192120133037 22904796671920947045049889)
      ·
        refine ⟨17178597503940710283787417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22904796671920947045049889 17178597503940710283787417)
        ·
          refine ⟨12883948127955532712840563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17178597503940710283787417 12883948127955532712840563)
          ·
            refine ⟨19325922191933299069260845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12883948127955532712840563 19325922191933299069260845)
            ·
              refine ⟨7247220821974987150972817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19325922191933299069260845 7247220821974987150972817)
              ·
                refine ⟨5435415616481240363229613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7247220821974987150972817 5435415616481240363229613)
                ·
                  refine ⟨2038280856180465136211105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5435415616481240363229613 2038280856180465136211105)
                  ·
                    refine ⟨1528710642135348852158329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038280856180465136211105 1528710642135348852158329)
                    ·
                      refine ⟨1146532981601511639118747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528710642135348852158329 1146532981601511639118747)
                      ·
                        rfl

theorem cell23_2232865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2232865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232865 prefixEnd_2232865 := by exact prefixLift 2232865
  have htrace : WordTrace (prefixWord ++ tailWord_2232865) baseStart_2232865 baseEnd_2232865 := by
    simpa [prefixWord, tailWord_2232865, baseEnd_2232865] using wordTrace_append hprefix tailTrace_2232865
  have hstable : (prefixWord ++ tailWord_2232865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232865).length < 2 ^ (prefixWord ++ tailWord_2232865).sum := by decide
  have hdescent : baseEnd_2232865 < baseStart_2232865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232882 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_2232882 : Nat := 118140960795 + 2232882 * 2 ^ 59
def prefixEnd_2232882 : Nat := 4983230072969 + 3 ^ 40 * 2232882 * 2
def baseEnd_2232882 : Nat := 1146541710772638072606169

theorem tailTrace_2232882 : CollatzResearch.WordTrace tailWord_2232882 prefixEnd_2232882 1146541710772638072606169 := by
  unfold tailWord_2232882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359974274164333682553225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54293264731104889820141933 20359974274164333682553225)
  ·
    refine ⟨15269980705623250261914919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20359974274164333682553225 15269980705623250261914919)
    ·
      refine ⟨22904971058434875392872379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15269980705623250261914919 22904971058434875392872379)
      ·
        refine ⟨34357456587652313089308569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22904971058434875392872379 34357456587652313089308569)
        ·
          refine ⟨25768092440739234816981427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34357456587652313089308569 25768092440739234816981427)
          ·
            refine ⟨38652138661108852225472141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25768092440739234816981427 38652138661108852225472141)
            ·
              refine ⟨14494551997915819584552053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38652138661108852225472141 14494551997915819584552053)
              ·
                refine ⟨1358864249804608086051755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14494551997915819584552053 1358864249804608086051755)
                ·
                  refine ⟨2038296374706912129077633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358864249804608086051755 2038296374706912129077633)
                  ·
                    refine ⟨1528722281030184096808225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038296374706912129077633 1528722281030184096808225)
                    ·
                      refine ⟨1146541710772638072606169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528722281030184096808225 1146541710772638072606169)
                      ·
                        rfl

theorem cell23_2232882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_2232882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232882 prefixEnd_2232882 := by exact prefixLift 2232882
  have htrace : WordTrace (prefixWord ++ tailWord_2232882) baseStart_2232882 baseEnd_2232882 := by
    simpa [prefixWord, tailWord_2232882, baseEnd_2232882] using wordTrace_append hprefix tailTrace_2232882
  have hstable : (prefixWord ++ tailWord_2232882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232882).length < 2 ^ (prefixWord ++ tailWord_2232882).sum := by decide
  have hdescent : baseEnd_2232882 < baseStart_2232882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232942 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_2232942 : Nat := 118140960795 + 2232942 * 2 ^ 59
def prefixEnd_2232942 : Nat := 4983230072969 + 3 ^ 40 * 2232942 * 2
def baseEnd_2232942 : Nat := 1146572519611907837855893

theorem tailTrace_2232942 : CollatzResearch.WordTrace tailWord_2232942 prefixEnd_2232942 1146572519611907837855893 := by
  unfold tailWord_2232942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180260684554995622174635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54294723650959976651598053 10180260684554995622174635)
  ·
    refine ⟨15270391026832493433261953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180260684554995622174635 15270391026832493433261953)
    ·
      refine ⟨11452793270124370074946465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15270391026832493433261953 11452793270124370074946465)
      ·
        refine ⟨8589594952593277556209849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11452793270124370074946465 8589594952593277556209849)
        ·
          refine ⟨6442196214444958167157387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8589594952593277556209849 6442196214444958167157387)
          ·
            refine ⟨9663294321667437250736081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442196214444958167157387 9663294321667437250736081)
            ·
              refine ⟨7247470741250577938052061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9663294321667437250736081 7247470741250577938052061)
              ·
                refine ⟨2717801527968966726769523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7247470741250577938052061 2717801527968966726769523)
                ·
                  refine ⟨4076702291953450090154285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717801527968966726769523 4076702291953450090154285)
                  ·
                    refine ⟨1528763359482543783807857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4076702291953450090154285 1528763359482543783807857)
                    ·
                      refine ⟨1146572519611907837855893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528763359482543783807857 1146572519611907837855893)
                      ·
                        rfl

theorem cell23_2232942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_2232942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232942 prefixEnd_2232942 := by exact prefixLift 2232942
  have htrace : WordTrace (prefixWord ++ tailWord_2232942) baseStart_2232942 baseEnd_2232942 := by
    simpa [prefixWord, tailWord_2232942, baseEnd_2232942] using wordTrace_append hprefix tailTrace_2232942
  have hstable : (prefixWord ++ tailWord_2232942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232942).length < 2 ^ (prefixWord ++ tailWord_2232942).sum := by decide
  have hdescent : baseEnd_2232942 < baseStart_2232942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232951 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_2232951 : Nat := 118140960795 + 2232951 * 2 ^ 59
def prefixEnd_2232951 : Nat := 4983230072969 + 3 ^ 40 * 2232951 * 2
def baseEnd_2232951 : Nat := 1146577140937798302643351

theorem tailTrace_2232951 : CollatzResearch.WordTrace tailWord_2232951 prefixEnd_2232951 1146577140937798302643351 := by
  unfold tailWord_2232951
  simp only [CollatzResearch.WordTrace]
  refine ⟨81442413733407359514474707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54294942488938239676316471 81442413733407359514474707)
  ·
    refine ⟨122163620600111039271712061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81442413733407359514474707 122163620600111039271712061)
    ·
      refine ⟨45811357725041639726892023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122163620600111039271712061 45811357725041639726892023)
      ·
        refine ⟨68717036587562459590338035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45811357725041639726892023 68717036587562459590338035)
        ·
          refine ⟨103075554881343689385507053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68717036587562459590338035 103075554881343689385507053)
          ·
            refine ⟨38653333080503883519565145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103075554881343689385507053 38653333080503883519565145)
            ·
              refine ⟨28989999810377912639673859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38653333080503883519565145 28989999810377912639673859)
              ·
                refine ⟨43484999715566868959510789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28989999810377912639673859 43484999715566868959510789)
                ·
                  refine ⟨8153437446668787929908273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43484999715566868959510789 8153437446668787929908273)
                  ·
                    refine ⟨6115078085001590947431205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8153437446668787929908273 6115078085001590947431205)
                    ·
                      refine ⟨1146577140937798302643351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6115078085001590947431205 1146577140937798302643351)
                      ·
                        rfl

theorem cell23_2232951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_2232951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2232951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2232951 prefixEnd_2232951 := by exact prefixLift 2232951
  have htrace : WordTrace (prefixWord ++ tailWord_2232951) baseStart_2232951 baseEnd_2232951 := by
    simpa [prefixWord, tailWord_2232951, baseEnd_2232951] using wordTrace_append hprefix tailTrace_2232951
  have hstable : (prefixWord ++ tailWord_2232951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232951).length < 2 ^ (prefixWord ++ tailWord_2232951).sum := by decide
  have hdescent : baseEnd_2232951 < baseStart_2232951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233001 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_2233001 : Nat := 118140960795 + 2233001 * 2 ^ 59
def prefixEnd_2233001 : Nat := 4983230072969 + 3 ^ 40 * 2233001 * 2
def baseEnd_2233001 : Nat := 1146602814970523107018121

theorem tailTrace_2233001 : CollatzResearch.WordTrace tailWord_2233001 prefixEnd_2233001 1146602814970523107018121 := by
  unfold tailWord_2233001
  simp only [CollatzResearch.WordTrace]
  refine ⟨81444237383226218053794857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54296158255484145369196571 81444237383226218053794857)
  ·
    refine ⟨61083178037419663540346143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81444237383226218053794857 61083178037419663540346143)
    ·
      refine ⟨91624767056129495310519215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61083178037419663540346143 91624767056129495310519215)
      ·
        refine ⟨137437150584194242965778823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91624767056129495310519215 137437150584194242965778823)
        ·
          refine ⟨206155725876291364448668235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137437150584194242965778823 206155725876291364448668235)
          ·
            refine ⟨309233588814437046673002353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206155725876291364448668235 309233588814437046673002353)
            ·
              refine ⟨231925191610827785004751765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309233588814437046673002353 231925191610827785004751765)
              ·
                refine ⟨10871493356757552422097739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231925191610827785004751765 10871493356757552422097739)
                ·
                  refine ⟨16307240035136328633146609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10871493356757552422097739 16307240035136328633146609)
                  ·
                    refine ⟨12230430026352246474859957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16307240035136328633146609 12230430026352246474859957)
                    ·
                      refine ⟨1146602814970523107018121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12230430026352246474859957 1146602814970523107018121)
                      ·
                        rfl

theorem cell23_2233001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_2233001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233001 prefixEnd_2233001 := by exact prefixLift 2233001
  have htrace : WordTrace (prefixWord ++ tailWord_2233001) baseStart_2233001 baseEnd_2233001 := by
    simpa [prefixWord, tailWord_2233001, baseEnd_2233001] using wordTrace_append hprefix tailTrace_2233001
  have hstable : (prefixWord ++ tailWord_2233001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233001).length < 2 ^ (prefixWord ++ tailWord_2233001).sum := by decide
  have hdescent : baseEnd_2233001 < baseStart_2233001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233006 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2233006 : Nat := 118140960795 + 2233006 * 2 ^ 59
def prefixEnd_2233006 : Nat := 4983230072969 + 3 ^ 40 * 2233006 * 2
def baseEnd_2233006 : Nat := 1146605382373795587455599

theorem tailTrace_2233006 : CollatzResearch.WordTrace tailWord_2233006 prefixEnd_2233006 1146605382373795587455599 := by
  unfold tailWord_2233006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180552468526012988465859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54296279832138735938484581 10180552468526012988465859)
  ·
    refine ⟨15270828702789019482698789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180552468526012988465859 15270828702789019482698789)
    ·
      refine ⟨2863280381772941153006023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15270828702789019482698789 2863280381772941153006023)
      ·
        refine ⟨4294920572659411729509035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863280381772941153006023 4294920572659411729509035)
        ·
          refine ⟨6442380858989117594263553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294920572659411729509035 6442380858989117594263553)
          ·
            refine ⟨4831785644241838195697665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442380858989117594263553 4831785644241838195697665)
            ·
              refine ⟨3623839233181378646773249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831785644241838195697665 3623839233181378646773249)
              ·
                refine ⟨2717879424886033985079937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623839233181378646773249 2717879424886033985079937)
                ·
                  refine ⟨2038409568664525488809953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717879424886033985079937 2038409568664525488809953)
                  ·
                    refine ⟨1528807176498394116607465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038409568664525488809953 1528807176498394116607465)
                    ·
                      refine ⟨1146605382373795587455599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528807176498394116607465 1146605382373795587455599)
                      ·
                        rfl

theorem cell23_2233006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2233006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233006 prefixEnd_2233006 := by exact prefixLift 2233006
  have htrace : WordTrace (prefixWord ++ tailWord_2233006) baseStart_2233006 baseEnd_2233006 := by
    simpa [prefixWord, tailWord_2233006, baseEnd_2233006] using wordTrace_append hprefix tailTrace_2233006
  have hstable : (prefixWord ++ tailWord_2233006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233006).length < 2 ^ (prefixWord ++ tailWord_2233006).sum := by decide
  have hdescent : baseEnd_2233006 < baseStart_2233006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233042 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2233042 : Nat := 118140960795 + 2233042 * 2 ^ 59
def prefixEnd_2233042 : Nat := 4983230072969 + 3 ^ 40 * 2233042 * 2
def baseEnd_2233042 : Nat := 382207955892452482201811

theorem tailTrace_2233042 : CollatzResearch.WordTrace tailWord_2233042 prefixEnd_2233042 382207955892452482201811 := by
  unfold tailWord_2233042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361433194019420514009345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54297155184051788037358253 20361433194019420514009345)
  ·
    refine ⟨15271074895514565385507009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20361433194019420514009345 15271074895514565385507009)
    ·
      refine ⟨11453306171635924039130257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15271074895514565385507009 11453306171635924039130257)
      ·
        refine ⟨8589979628726943029347693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11453306171635924039130257 8589979628726943029347693)
        ·
          refine ⟨3221242360772603636005385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8589979628726943029347693 3221242360772603636005385)
          ·
            refine ⟨2415931770579452727004039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221242360772603636005385 2415931770579452727004039)
            ·
              refine ⟨3623897655869179090506059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415931770579452727004039 3623897655869179090506059)
              ·
                refine ⟨5435846483803768635759089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623897655869179090506059 5435846483803768635759089)
                ·
                  refine ⟨4076884862852826476819317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435846483803768635759089 4076884862852826476819317)
                  ·
                    refine ⟨382207955892452482201811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4076884862852826476819317 382207955892452482201811)
                    ·
                      rfl

theorem cell23_2233042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2233042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233042 prefixEnd_2233042 := by exact prefixLift 2233042
  have htrace : WordTrace (prefixWord ++ tailWord_2233042) baseStart_2233042 baseEnd_2233042 := by
    simpa [prefixWord, tailWord_2233042, baseEnd_2233042] using wordTrace_append hprefix tailTrace_2233042
  have hstable : (prefixWord ++ tailWord_2233042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233042).length < 2 ^ (prefixWord ++ tailWord_2233042).sum := by decide
  have hdescent : baseEnd_2233042 < baseStart_2233042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233085 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 6]
def baseStart_2233085 : Nat := 118140960795 + 2233085 * 2 ^ 59
def prefixEnd_2233085 : Nat := 4983230072969 + 3 ^ 40 * 2233085 * 2
def baseEnd_2233085 : Nat := 127405105260611197596415

theorem tailTrace_2233085 : CollatzResearch.WordTrace tailWord_2233085 prefixEnd_2233085 127405105260611197596415 := by
  unfold tailWord_2233085
  simp only [CollatzResearch.WordTrace]
  refine ⟨81447301114921900399852709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54298200743281266933235139 81447301114921900399852709)
  ·
    refine ⟨15271368959047856324972383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81447301114921900399852709 15271368959047856324972383)
    ·
      refine ⟨22907053438571784487458575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15271368959047856324972383 22907053438571784487458575)
      ·
        refine ⟨34360580157857676731187863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22907053438571784487458575 34360580157857676731187863)
        ·
          refine ⟨51540870236786515096781795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34360580157857676731187863 51540870236786515096781795)
          ·
            refine ⟨77311305355179772645172693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51540870236786515096781795 77311305355179772645172693)
            ·
              refine ⟨1811983719262025921371235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77311305355179772645172693 1811983719262025921371235)
              ·
                refine ⟨2717975578893038882056853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811983719262025921371235 2717975578893038882056853)
                ·
                  refine ⟨127405105260611197596415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2717975578893038882056853 127405105260611197596415)
                  ·
                    rfl

theorem cell23_2233085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_2233085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233085 prefixEnd_2233085 := by exact prefixLift 2233085
  have htrace : WordTrace (prefixWord ++ tailWord_2233085) baseStart_2233085 baseEnd_2233085 := by
    simpa [prefixWord, tailWord_2233085, baseEnd_2233085] using wordTrace_append hprefix tailTrace_2233085
  have hstable : (prefixWord ++ tailWord_2233085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233085).length < 2 ^ (prefixWord ++ tailWord_2233085).sum := by decide
  have hdescent : baseEnd_2233085 < baseStart_2233085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233105 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_2233105 : Nat := 118140960795 + 2233105 * 2 ^ 59
def prefixEnd_2233105 : Nat := 4983230072969 + 3 ^ 40 * 2233105 * 2
def baseEnd_2233105 : Nat := 1146656216958590700117643

theorem tailTrace_2233105 : CollatzResearch.WordTrace tailWord_2233105 prefixEnd_2233105 1146656216958590700117643 := by
  unfold tailWord_2233105
  simp only [CollatzResearch.WordTrace]
  refine ⟨81448030574849443815580769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54298687049899629210387179 81448030574849443815580769)
  ·
    refine ⟨61086022931137082861685577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81448030574849443815580769 61086022931137082861685577)
    ·
      refine ⟨45814517198352812146264183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61086022931137082861685577 45814517198352812146264183)
      ·
        refine ⟨68721775797529218219396275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45814517198352812146264183 68721775797529218219396275)
        ·
          refine ⟨103082663696293827329094413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68721775797529218219396275 103082663696293827329094413)
          ·
            refine ⟨38655998886110185248410405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103082663696293827329094413 38655998886110185248410405)
            ·
              refine ⟨7247999791145659734076951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38655998886110185248410405 7247999791145659734076951)
              ·
                refine ⟨10871999686718489601115427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7247999791145659734076951 10871999686718489601115427)
                ·
                  refine ⟨16307999530077734401673141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10871999686718489601115427 16307999530077734401673141)
                  ·
                    refine ⟨1528874955944787600156857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16307999530077734401673141 1528874955944787600156857)
                    ·
                      refine ⟨1146656216958590700117643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528874955944787600156857 1146656216958590700117643)
                      ·
                        rfl

theorem cell23_2233105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_2233105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233105 prefixEnd_2233105 := by exact prefixLift 2233105
  have htrace : WordTrace (prefixWord ++ tailWord_2233105) baseStart_2233105 baseEnd_2233105 := by
    simpa [prefixWord, tailWord_2233105, baseEnd_2233105] using wordTrace_append hprefix tailTrace_2233105
  have hstable : (prefixWord ++ tailWord_2233105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233105).length < 2 ^ (prefixWord ++ tailWord_2233105).sum := by decide
  have hdescent : baseEnd_2233105 < baseStart_2233105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233122 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2233122 : Nat := 118140960795 + 2233122 * 2 ^ 59
def prefixEnd_2233122 : Nat := 4983230072969 + 3 ^ 40 * 2233122 * 2
def baseEnd_2233122 : Nat := 1146664946129717133605065

theorem tailTrace_2233122 : CollatzResearch.WordTrace tailWord_2233122 prefixEnd_2233122 1146664946129717133605065 := by
  unfold tailWord_2233122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20362162653946963929737405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54299100410525237145966413 20362162653946963929737405)
  ·
    refine ⟨7635810995230111473651527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20362162653946963929737405 7635810995230111473651527)
    ·
      refine ⟨11453716492845167210477291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635810995230111473651527 11453716492845167210477291)
      ·
        refine ⟨17180574739267750815715937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11453716492845167210477291 17180574739267750815715937)
        ·
          refine ⟨12885431054450813111786953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17180574739267750815715937 12885431054450813111786953)
          ·
            refine ⟨9664073290838109833840215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12885431054450813111786953 9664073290838109833840215)
            ·
              refine ⟨14496109936257164750760323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664073290838109833840215 14496109936257164750760323)
              ·
                refine ⟨21744164904385747126140485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14496109936257164750760323 21744164904385747126140485)
                ·
                  refine ⟨4077030919572327586151341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21744164904385747126140485 4077030919572327586151341)
                  ·
                    refine ⟨1528886594839622844806753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4077030919572327586151341 1528886594839622844806753)
                    ·
                      refine ⟨1146664946129717133605065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528886594839622844806753 1146664946129717133605065)
                      ·
                        rfl

theorem cell23_2233122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2233122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233122 prefixEnd_2233122 := by exact prefixLift 2233122
  have htrace : WordTrace (prefixWord ++ tailWord_2233122) baseStart_2233122 baseEnd_2233122 := by
    simpa [prefixWord, tailWord_2233122, baseEnd_2233122] using wordTrace_append hprefix tailTrace_2233122
  have hstable : (prefixWord ++ tailWord_2233122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233122).length < 2 ^ (prefixWord ++ tailWord_2233122).sum := by decide
  have hdescent : baseEnd_2233122 < baseStart_2233122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233149 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2233149 : Nat := 118140960795 + 2233149 * 2 ^ 59
def prefixEnd_2233149 : Nat := 4983230072969 + 3 ^ 40 * 2233149 * 2
def baseEnd_2233149 : Nat := 382226270035796175989147

theorem tailTrace_2233149 : CollatzResearch.WordTrace tailWord_2233149 prefixEnd_2233149 382226270035796175989147 := by
  unfold tailWord_2233149
  simp only [CollatzResearch.WordTrace]
  refine ⟨81449635386690039330182501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54299756924460026220121667 81449635386690039330182501)
  ·
    refine ⟨15271806635004382374409219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81449635386690039330182501 15271806635004382374409219)
    ·
      refine ⟨22907709952506573561613829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15271806635004382374409219 22907709952506573561613829)
      ·
        refine ⟨4295195616094982542802593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22907709952506573561613829 4295195616094982542802593)
        ·
          refine ⟨3221396712071236907101945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4295195616094982542802593 3221396712071236907101945)
          ·
            refine ⟨2416047534053427680326459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221396712071236907101945 2416047534053427680326459)
            ·
              refine ⟨3624071301080141520489689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416047534053427680326459 3624071301080141520489689)
              ·
                refine ⟨2718053475810106140367267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624071301080141520489689 2718053475810106140367267)
                ·
                  refine ⟨4077080213715159210550901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718053475810106140367267 4077080213715159210550901)
                  ·
                    refine ⟨382226270035796175989147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4077080213715159210550901 382226270035796175989147)
                    ·
                      rfl

theorem cell23_2233149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2233149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233149 prefixEnd_2233149 := by exact prefixLift 2233149
  have htrace : WordTrace (prefixWord ++ tailWord_2233149) baseStart_2233149 baseEnd_2233149 := by
    simpa [prefixWord, tailWord_2233149, baseEnd_2233149] using wordTrace_append hprefix tailTrace_2233149
  have hstable : (prefixWord ++ tailWord_2233149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233149).length < 2 ^ (prefixWord ++ tailWord_2233149).sum := by decide
  have hdescent : baseEnd_2233149 < baseStart_2233149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233152 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2]
def baseStart_2233152 : Nat := 118140960795 + 2233152 * 2 ^ 59
def prefixEnd_2233152 : Nat := 4983230072969 + 3 ^ 40 * 2233152 * 2
def baseEnd_2233152 : Nat := 1146680350549352016229927

theorem tailTrace_2233152 : CollatzResearch.WordTrace tailWord_2233152 prefixEnd_2233152 1146680350549352016229927 := by
  unfold tailWord_2233152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40724872402839585421270855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54299829870452780561694473 40724872402839585421270855)
  ·
    refine ⟨61087308604259378131906283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40724872402839585421270855 61087308604259378131906283)
    ·
      refine ⟨91630962906389067197859425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61087308604259378131906283 91630962906389067197859425)
      ·
        refine ⟨68723222179791800398394569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91630962906389067197859425 68723222179791800398394569)
        ·
          refine ⟨51542416634843850298795927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68723222179791800398394569 51542416634843850298795927)
          ·
            refine ⟨77313624952265775448193891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51542416634843850298795927 77313624952265775448193891)
            ·
              refine ⟨115970437428398663172290837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77313624952265775448193891 115970437428398663172290837)
              ·
                refine ⟨5436114254456187336201133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115970437428398663172290837 5436114254456187336201133)
                ·
                  refine ⟨2038542845421070251075425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5436114254456187336201133 2038542845421070251075425)
                  ·
                    refine ⟨1528907134065802688306569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038542845421070251075425 1528907134065802688306569)
                    ·
                      refine ⟨1146680350549352016229927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1528907134065802688306569 1146680350549352016229927)
                      ·
                        rfl

theorem cell23_2233152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_2233152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233152 prefixEnd_2233152 := by exact prefixLift 2233152
  have htrace : WordTrace (prefixWord ++ tailWord_2233152) baseStart_2233152 baseEnd_2233152 := by
    simpa [prefixWord, tailWord_2233152, baseEnd_2233152] using wordTrace_append hprefix tailTrace_2233152
  have hstable : (prefixWord ++ tailWord_2233152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233152).length < 2 ^ (prefixWord ++ tailWord_2233152).sum := by decide
  have hdescent : baseEnd_2233152 < baseStart_2233152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233155 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3]
def baseStart_2233155 : Nat := 118140960795 + 2233155 * 2 ^ 59
def prefixEnd_2233155 : Nat := 4983230072969 + 3 ^ 40 * 2233155 * 2
def baseEnd_2233155 : Nat := 1146681890991315504492413

theorem tailTrace_2233155 : CollatzResearch.WordTrace tailWord_2233155 prefixEnd_2233155 1146681890991315504492413 := by
  unfold tailWord_2233155
  simp only [CollatzResearch.WordTrace]
  refine ⟨81449854224668302354900919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54299902816445534903267279 81449854224668302354900919)
  ·
    refine ⟨122174781337002453532351379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81449854224668302354900919 122174781337002453532351379)
    ·
      refine ⟨183262172005503680298527069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122174781337002453532351379 183262172005503680298527069)
      ·
        refine ⟨68723314502063880111947651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183262172005503680298527069 68723314502063880111947651)
        ·
          refine ⟨103084971753095820167921477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68723314502063880111947651 103084971753095820167921477)
          ·
            refine ⟨19328432203705466281485277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103084971753095820167921477 19328432203705466281485277)
            ·
              refine ⟨7248162076389549855556979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19328432203705466281485277 7248162076389549855556979)
              ·
                refine ⟨10872243114584324783335469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248162076389549855556979 10872243114584324783335469)
                ·
                  refine ⟨4077091167969121793750801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10872243114584324783335469 4077091167969121793750801)
                  ·
                    refine ⟨3057818375976841345313101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077091167969121793750801 3057818375976841345313101)
                    ·
                      refine ⟨1146681890991315504492413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3057818375976841345313101 1146681890991315504492413)
                      ·
                        rfl

theorem cell23_2233155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_2233155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233155 prefixEnd_2233155 := by exact prefixLift 2233155
  have htrace : WordTrace (prefixWord ++ tailWord_2233155) baseStart_2233155 baseEnd_2233155 := by
    simpa [prefixWord, tailWord_2233155, baseEnd_2233155] using wordTrace_append hprefix tailTrace_2233155
  have hstable : (prefixWord ++ tailWord_2233155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233155).length < 2 ^ (prefixWord ++ tailWord_2233155).sum := by decide
  have hdescent : baseEnd_2233155 < baseStart_2233155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233169 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_2233169 : Nat := 118140960795 + 2233169 * 2 ^ 59
def prefixEnd_2233169 : Nat := 4983230072969 + 3 ^ 40 * 2233169 * 2
def baseEnd_2233169 : Nat := 1146689079720478449717349

theorem tailTrace_2233169 : CollatzResearch.WordTrace tailWord_2233169 prefixEnd_2233169 1146689079720478449717349 := by
  unfold tailWord_2233169
  simp only [CollatzResearch.WordTrace]
  refine ⟨81450364846617582745910561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54300243231078388497273707 81450364846617582745910561)
  ·
    refine ⟨61087773634963187059432921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81450364846617582745910561 61087773634963187059432921)
    ·
      refine ⟨45815830226222390294574691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61087773634963187059432921 45815830226222390294574691)
      ·
        refine ⟨68723745339333585441862037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45815830226222390294574691 68723745339333585441862037)
        ·
          refine ⟨3221425562781261817587283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68723745339333585441862037 3221425562781261817587283)
          ·
            refine ⟨4832138344171892726380925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221425562781261817587283 4832138344171892726380925)
            ·
              refine ⟨1812051879064459772392847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4832138344171892726380925 1812051879064459772392847)
              ·
                refine ⟨2718077818596689658589271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812051879064459772392847 2718077818596689658589271)
                ·
                  refine ⟨4077116727895034487883907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718077818596689658589271 4077116727895034487883907)
                  ·
                    refine ⟨6115675091842551731825861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077116727895034487883907 6115675091842551731825861)
                    ·
                      refine ⟨1146689079720478449717349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6115675091842551731825861 1146689079720478449717349)
                      ·
                        rfl

theorem cell23_2233169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_2233169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233169 prefixEnd_2233169 := by exact prefixLift 2233169
  have htrace : WordTrace (prefixWord ++ tailWord_2233169) baseStart_2233169 baseEnd_2233169 := by
    simpa [prefixWord, tailWord_2233169, baseEnd_2233169] using wordTrace_append hprefix tailTrace_2233169
  have hstable : (prefixWord ++ tailWord_2233169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233169).length < 2 ^ (prefixWord ++ tailWord_2233169).sum := by decide
  have hdescent : baseEnd_2233169 < baseStart_2233169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233295 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 4, 5]
def baseStart_2233295 : Nat := 118140960795 + 2233295 * 2 ^ 59
def prefixEnd_2233295 : Nat := 4983230072969 + 3 ^ 40 * 2233295 * 2
def baseEnd_2233295 : Nat := 382251259427648318913923

theorem tailTrace_2233295 : CollatzResearch.WordTrace tailWord_2233295 prefixEnd_2233295 382251259427648318913923 := by
  unfold tailWord_2233295
  simp only [CollatzResearch.WordTrace]
  refine ⟨81454960444161106264997339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54303306962774070843331559 81454960444161106264997339)
  ·
    refine ⟨122182440666241659397496009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81454960444161106264997339 122182440666241659397496009)
    ·
      refine ⟨91636830499681244548122007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122182440666241659397496009 91636830499681244548122007)
      ·
        refine ⟨137455245749521866822183011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91636830499681244548122007 137455245749521866822183011)
        ·
          refine ⟨206182868624282800233274517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137455245749521866822183011 206182868624282800233274517)
          ·
            refine ⟨9664821966763256260934743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206182868624282800233274517 9664821966763256260934743)
            ·
              refine ⟨14497232950144884391402115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664821966763256260934743 14497232950144884391402115)
              ·
                refine ⟨21745849425217326587103173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14497232950144884391402115 21745849425217326587103173)
                ·
                  refine ⟨4077346767228248735081845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21745849425217326587103173 4077346767228248735081845)
                  ·
                    refine ⟨382251259427648318913923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4077346767228248735081845 382251259427648318913923)
                    ·
                      rfl

theorem cell23_2233295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_2233295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233295 prefixEnd_2233295 := by exact prefixLift 2233295
  have htrace : WordTrace (prefixWord ++ tailWord_2233295) baseStart_2233295 baseEnd_2233295 := by
    simpa [prefixWord, tailWord_2233295, baseEnd_2233295] using wordTrace_append hprefix tailTrace_2233295
  have hstable : (prefixWord ++ tailWord_2233295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233295).length < 2 ^ (prefixWord ++ tailWord_2233295).sum := by decide
  have hdescent : baseEnd_2233295 < baseStart_2233295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233305 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_2233305 : Nat := 118140960795 + 2233305 * 2 ^ 59
def prefixEnd_2233305 : Nat := 4983230072969 + 3 ^ 40 * 2233305 * 2
def baseEnd_2233305 : Nat := 1146758913089489917616723

theorem tailTrace_2233305 : CollatzResearch.WordTrace tailWord_2233305 prefixEnd_2233305 1146758913089489917616723 := by
  unfold tailWord_2233305
  simp only [CollatzResearch.WordTrace]
  refine ⟨81455325174124877972861369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54303550116083251981907579 81455325174124877972861369)
  ·
    refine ⟨61091493880593658479646027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81455325174124877972861369 61091493880593658479646027)
    ·
      refine ⟨91637240820890487719469041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61091493880593658479646027 91637240820890487719469041)
      ·
        refine ⟨68727930615667865789601781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91637240820890487719469041 68727930615667865789601781)
        ·
          refine ⟨6443243495218862417775167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68727930615667865789601781 6443243495218862417775167)
          ·
            refine ⟨9664865242828293626662751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443243495218862417775167 9664865242828293626662751)
            ·
              refine ⟨14497297864242440439994127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664865242828293626662751 14497297864242440439994127)
              ·
                refine ⟨21745946796363660659991191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14497297864242440439994127 21745946796363660659991191)
                ·
                  refine ⟨32618920194545490989986787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21745946796363660659991191 32618920194545490989986787)
                  ·
                    refine ⟨48928380291818236484980181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32618920194545490989986787 48928380291818236484980181)
                    ·
                      refine ⟨1146758913089489917616723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48928380291818236484980181 1146758913089489917616723)
                      ·
                        rfl

theorem cell23_2233305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_2233305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233305 prefixEnd_2233305 := by exact prefixLift 2233305
  have htrace : WordTrace (prefixWord ++ tailWord_2233305) baseStart_2233305 baseEnd_2233305 := by
    simpa [prefixWord, tailWord_2233305, baseEnd_2233305] using wordTrace_append hprefix tailTrace_2233305
  have hstable : (prefixWord ++ tailWord_2233305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233305).length < 2 ^ (prefixWord ++ tailWord_2233305).sum := by decide
  have hdescent : baseEnd_2233305 < baseStart_2233305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233376 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_2233376 : Nat := 118140960795 + 2233376 * 2 ^ 59
def prefixEnd_2233376 : Nat := 4983230072969 + 3 ^ 40 * 2233376 * 2
def baseEnd_2233376 : Nat := 382265123405319713276299

theorem tailTrace_2233376 : CollatzResearch.WordTrace tailWord_2233376 prefixEnd_2233376 382265123405319713276299 := by
  unfold tailWord_2233376
  simp only [CollatzResearch.WordTrace]
  refine ⟨40728957378433828549347991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54305276504578438065797321 40728957378433828549347991)
  ·
    refine ⟨61093436067650742824021987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40728957378433828549347991 61093436067650742824021987)
    ·
      refine ⟨91640154101476114236032981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61093436067650742824021987 91640154101476114236032981)
      ·
        refine ⟨2147816111753346427407023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91640154101476114236032981 2147816111753346427407023)
        ·
          refine ⟨3221724167630019641110535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147816111753346427407023 3221724167630019641110535)
          ·
            refine ⟨4832586251445029461665803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221724167630019641110535 4832586251445029461665803)
            ·
              refine ⟨7248879377167544192498705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832586251445029461665803 7248879377167544192498705)
              ·
                refine ⟨5436659532875658144374029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7248879377167544192498705 5436659532875658144374029)
                ·
                  refine ⟨2038747324828371804140261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5436659532875658144374029 2038747324828371804140261)
                  ·
                    refine ⟨382265123405319713276299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038747324828371804140261 382265123405319713276299)
                    ·
                      rfl

theorem cell23_2233376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_2233376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233376 prefixEnd_2233376 := by exact prefixLift 2233376
  have htrace : WordTrace (prefixWord ++ tailWord_2233376) baseStart_2233376 baseEnd_2233376 := by
    simpa [prefixWord, tailWord_2233376, baseEnd_2233376] using wordTrace_append hprefix tailTrace_2233376
  have hstable : (prefixWord ++ tailWord_2233376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233376).length < 2 ^ (prefixWord ++ tailWord_2233376).sum := by decide
  have hdescent : baseEnd_2233376 < baseStart_2233376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233395 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_2233395 : Nat := 118140960795 + 2233395 * 2 ^ 59
def prefixEnd_2233395 : Nat := 4983230072969 + 3 ^ 40 * 2233395 * 2
def baseEnd_2233395 : Nat := 1146805126348394565491309

theorem tailTrace_2233395 : CollatzResearch.WordTrace tailWord_2233395 prefixEnd_2233395 1146805126348394565491309 := by
  unfold tailWord_2233395
  simp only [CollatzResearch.WordTrace]
  refine ⟨81458607743798823343637639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54305738495865882229091759 81458607743798823343637639)
  ·
    refine ⟨122187911615698235015456459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81458607743798823343637639 122187911615698235015456459)
    ·
      refine ⟨183281867423547352523184689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122187911615698235015456459 183281867423547352523184689)
      ·
        refine ⟨137461400567660514392388517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183281867423547352523184689 137461400567660514392388517)
        ·
          refine ⟨25774012606436346448572847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137461400567660514392388517 25774012606436346448572847)
          ·
            refine ⟨38661018909654519672859271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25774012606436346448572847 38661018909654519672859271)
            ·
              refine ⟨57991528364481779509288907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38661018909654519672859271 57991528364481779509288907)
              ·
                refine ⟨86987292546722669263933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57991528364481779509288907 86987292546722669263933361)
                ·
                  refine ⟨65240469410042001947950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86987292546722669263933361 65240469410042001947950021)
                  ·
                    refine ⟨12232588014382875365240629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65240469410042001947950021 12232588014382875365240629)
                    ·
                      refine ⟨1146805126348394565491309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12232588014382875365240629 1146805126348394565491309)
                      ·
                        rfl

theorem cell23_2233395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_2233395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233395 prefixEnd_2233395 := by exact prefixLift 2233395
  have htrace : WordTrace (prefixWord ++ tailWord_2233395) baseStart_2233395 baseEnd_2233395 := by
    simpa [prefixWord, tailWord_2233395, baseEnd_2233395] using wordTrace_append hprefix tailTrace_2233395
  have hstable : (prefixWord ++ tailWord_2233395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233395).length < 2 ^ (prefixWord ++ tailWord_2233395).sum := by decide
  have hdescent : baseEnd_2233395 < baseStart_2233395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233406 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2233406 : Nat := 118140960795 + 2233406 * 2 ^ 59
def prefixEnd_2233406 : Nat := 4983230072969 + 3 ^ 40 * 2233406 * 2
def baseEnd_2233406 : Nat := 127423419403954891383751

theorem tailTrace_2233406 : CollatzResearch.WordTrace tailWord_2233406 prefixEnd_2233406 127423419403954891383751 := by
  unfold tailWord_2233406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182376118344871527786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54306005964505981481525381 10182376118344871527786009)
  ·
    refine ⟨7636782088758653645839507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10182376118344871527786009 7636782088758653645839507)
    ·
      refine ⟨11455173133137980468759261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636782088758653645839507 11455173133137980468759261)
      ·
        refine ⟨4295689924926742675784723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11455173133137980468759261 4295689924926742675784723)
        ·
          refine ⟨6443534887390114013677085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295689924926742675784723 6443534887390114013677085)
          ·
            refine ⟨2416325582771292755128907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6443534887390114013677085 2416325582771292755128907)
            ·
              refine ⟨3624488374156939132693361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416325582771292755128907 3624488374156939132693361)
              ·
                refine ⟨2718366280617704349520021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624488374156939132693361 2718366280617704349520021)
                ·
                  refine ⟨127423419403954891383751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2718366280617704349520021 127423419403954891383751)
                  ·
                    rfl

theorem cell23_2233406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2233406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233406 prefixEnd_2233406 := by exact prefixLift 2233406
  have htrace : WordTrace (prefixWord ++ tailWord_2233406) baseStart_2233406 baseEnd_2233406 := by
    simpa [prefixWord, tailWord_2233406, baseEnd_2233406] using wordTrace_append hprefix tailTrace_2233406
  have hstable : (prefixWord ++ tailWord_2233406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233406).length < 2 ^ (prefixWord ++ tailWord_2233406).sum := by decide
  have hdescent : baseEnd_2233406 < baseStart_2233406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233416 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_2233416 : Nat := 118140960795 + 2233416 * 2 ^ 59
def prefixEnd_2233416 : Nat := 4983230072969 + 3 ^ 40 * 2233416 * 2
def baseEnd_2233416 : Nat := 1146815909442138983328713

theorem tailTrace_2233416 : CollatzResearch.WordTrace tailWord_2233416 prefixEnd_2233416 1146815909442138983328713 := by
  unfold tailWord_2233416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40729686838361371965076051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54306249117815162620101401 40729686838361371965076051)
  ·
    refine ⟨61094530257542057947614077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40729686838361371965076051 61094530257542057947614077)
    ·
      refine ⟨22910448846578271730355279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61094530257542057947614077 22910448846578271730355279)
      ·
        refine ⟨34365673269867407595532919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22910448846578271730355279 34365673269867407595532919)
        ·
          refine ⟨51548509904801111393299379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34365673269867407595532919 51548509904801111393299379)
          ·
            refine ⟨77322764857201667089949069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51548509904801111393299379 77322764857201667089949069)
            ·
              refine ⟨28996036821450625158730901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77322764857201667089949069 28996036821450625158730901)
              ·
                refine ⟨1359189226005498054315511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28996036821450625158730901 1359189226005498054315511)
                ·
                  refine ⟨2038783839008247081473267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359189226005498054315511 2038783839008247081473267)
                  ·
                    refine ⟨3058175758512370622209901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2038783839008247081473267 3058175758512370622209901)
                    ·
                      refine ⟨1146815909442138983328713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058175758512370622209901 1146815909442138983328713)
                      ·
                        rfl

theorem cell23_2233416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_2233416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233416 prefixEnd_2233416 := by exact prefixLift 2233416
  have htrace : WordTrace (prefixWord ++ tailWord_2233416) baseStart_2233416 baseEnd_2233416 := by
    simpa [prefixWord, tailWord_2233416, baseEnd_2233416] using wordTrace_append hprefix tailTrace_2233416
  have hstable : (prefixWord ++ tailWord_2233416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233416).length < 2 ^ (prefixWord ++ tailWord_2233416).sum := by decide
  have hdescent : baseEnd_2233416 < baseStart_2233416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233439 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2233439 : Nat := 118140960795 + 2233439 * 2 ^ 59
def prefixEnd_2233439 : Nat := 4983230072969 + 3 ^ 40 * 2233439 * 2
def baseEnd_2233439 : Nat := 1146827719497192393341107

theorem tailTrace_2233439 : CollatzResearch.WordTrace tailWord_2233439 prefixEnd_2233439 1146827719497192393341107 := by
  unfold tailWord_2233439
  simp only [CollatzResearch.WordTrace]
  refine ⟨81460212555639418858239371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54306808370426279238826247 81460212555639418858239371)
  ·
    refine ⟨122190318833459128287359057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81460212555639418858239371 122190318833459128287359057)
    ·
      refine ⟨91642739125094346215519293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122190318833459128287359057 91642739125094346215519293)
      ·
        refine ⟨34366027171910379830819735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91642739125094346215519293 34366027171910379830819735)
        ·
          refine ⟨51549040757865569746229603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34366027171910379830819735 51549040757865569746229603)
          ·
            refine ⟨77323561136798354619344405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51549040757865569746229603 77323561136798354619344405)
            ·
              refine ⟨3624541928287422872781769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77323561136798354619344405 3624541928287422872781769)
              ·
                refine ⟨2718406446215567154586327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624541928287422872781769 2718406446215567154586327)
                ·
                  refine ⟨4077609669323350731879491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718406446215567154586327 4077609669323350731879491)
                  ·
                    refine ⟨6116414503985026097819237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077609669323350731879491 6116414503985026097819237)
                    ·
                      refine ⟨1146827719497192393341107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6116414503985026097819237 1146827719497192393341107)
                      ·
                        rfl

theorem cell23_2233439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2233439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233439 prefixEnd_2233439 := by exact prefixLift 2233439
  have htrace : WordTrace (prefixWord ++ tailWord_2233439) baseStart_2233439 baseEnd_2233439 := by
    simpa [prefixWord, tailWord_2233439, baseEnd_2233439] using wordTrace_append hprefix tailTrace_2233439
  have hstable : (prefixWord ++ tailWord_2233439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233439).length < 2 ^ (prefixWord ++ tailWord_2233439).sum := by decide
  have hdescent : baseEnd_2233439 < baseStart_2233439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233450 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2233450 : Nat := 118140960795 + 2233450 * 2 ^ 59
def prefixEnd_2233450 : Nat := 4983230072969 + 3 ^ 40 * 2233450 * 2
def baseEnd_2233450 : Nat := 1146833367784391850303557

theorem tailTrace_2233450 : CollatzResearch.WordTrace tailWord_2233450 prefixEnd_2233450 1146833367784391850303557 := by
  unfold tailWord_2233450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365153439649891934222451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54307075839066378491259869 20365153439649891934222451)
  ·
    refine ⟨30547730159474837901333677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365153439649891934222451 30547730159474837901333677)
    ·
      refine ⟨11455398809803064213000129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30547730159474837901333677 11455398809803064213000129)
      ·
        refine ⟨8591549107352298159750097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11455398809803064213000129 8591549107352298159750097)
        ·
          refine ⟨6443661830514223619812573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8591549107352298159750097 6443661830514223619812573)
          ·
            refine ⟨2416373186442833857429715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6443661830514223619812573 2416373186442833857429715)
            ·
              refine ⟨3624559779664250786144573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416373186442833857429715 3624559779664250786144573)
              ·
                refine ⟨1359209917374094044804215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624559779664250786144573 1359209917374094044804215)
                ·
                  refine ⟨2038814876061141067206323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359209917374094044804215 2038814876061141067206323)
                  ·
                    refine ⟨3058222314091711600809485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2038814876061141067206323 3058222314091711600809485)
                    ·
                      refine ⟨1146833367784391850303557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058222314091711600809485 1146833367784391850303557)
                      ·
                        rfl

theorem cell23_2233450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2233450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233450 prefixEnd_2233450 := by exact prefixLift 2233450
  have htrace : WordTrace (prefixWord ++ tailWord_2233450) baseStart_2233450 baseEnd_2233450 := by
    simpa [prefixWord, tailWord_2233450, baseEnd_2233450] using wordTrace_append hprefix tailTrace_2233450
  have hstable : (prefixWord ++ tailWord_2233450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233450).length < 2 ^ (prefixWord ++ tailWord_2233450).sum := by decide
  have hdescent : baseEnd_2233450 < baseStart_2233450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233452 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2233452 : Nat := 118140960795 + 2233452 * 2 ^ 59
def prefixEnd_2233452 : Nat := 4983230072969 + 3 ^ 40 * 2233452 * 2
def baseEnd_2233452 : Nat := 1146834394745700842478547

theorem tailTrace_2233452 : CollatzResearch.WordTrace tailWord_2233452 prefixEnd_2233452 1146834394745700842478547 := by
  unfold tailWord_2233452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40730343352296161039231305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54307124469728214718975073 40730343352296161039231305)
  ·
    refine ⟨30547757514222120779423479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40730343352296161039231305 30547757514222120779423479)
    ·
      refine ⟨45821636271333181169135219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30547757514222120779423479 45821636271333181169135219)
      ·
        refine ⟨68732454406999771753702829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45821636271333181169135219 68732454406999771753702829)
        ·
          refine ⟨25774670402624914407638561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68732454406999771753702829 25774670402624914407638561)
          ·
            refine ⟨19331002801968685805728921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25774670402624914407638561 19331002801968685805728921)
            ·
              refine ⟨14498252101476514354296691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19331002801968685805728921 14498252101476514354296691)
              ·
                refine ⟨21747378152214771531445037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14498252101476514354296691 21747378152214771531445037)
                ·
                  refine ⟨8155266807080539324291889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21747378152214771531445037 8155266807080539324291889)
                  ·
                    refine ⟨6116450105310404493218917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8155266807080539324291889 6116450105310404493218917)
                    ·
                      refine ⟨1146834394745700842478547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6116450105310404493218917 1146834394745700842478547)
                      ·
                        rfl

theorem cell23_2233452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2233452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233452 prefixEnd_2233452 := by exact prefixLift 2233452
  have htrace : WordTrace (prefixWord ++ tailWord_2233452) baseStart_2233452 baseEnd_2233452 := by
    simpa [prefixWord, tailWord_2233452, baseEnd_2233452] using wordTrace_append hprefix tailTrace_2233452
  have hstable : (prefixWord ++ tailWord_2233452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233452).length < 2 ^ (prefixWord ++ tailWord_2233452).sum := by decide
  have hdescent : baseEnd_2233452 < baseStart_2233452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233473 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_2233473 : Nat := 118140960795 + 2233473 * 2 ^ 59
def prefixEnd_2233473 : Nat := 4983230072969 + 3 ^ 40 * 2233473 * 2
def baseEnd_2233473 : Nat := 1146845177839445260315951

theorem tailTrace_2233473 : CollatzResearch.WordTrace tailWord_2233473 prefixEnd_2233473 1146845177839445260315951 := by
  unfold tailWord_2233473
  simp only [CollatzResearch.WordTrace]
  refine ⟨81461452637516242664977073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54307635091677495109984715 81461452637516242664977073)
  ·
    refine ⟨61096089478137181998732805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81461452637516242664977073 61096089478137181998732805)
    ·
      refine ⟨11455516777150721624762401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61096089478137181998732805 11455516777150721624762401)
      ·
        refine ⟨8591637582863041218571801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11455516777150721624762401 8591637582863041218571801)
        ·
          refine ⟨6443728187147280913928851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8591637582863041218571801 6443728187147280913928851)
          ·
            refine ⟨9665592280720921370893277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443728187147280913928851 9665592280720921370893277)
            ·
              refine ⟨3624597105270345514084979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9665592280720921370893277 3624597105270345514084979)
              ·
                refine ⟨5436895657905518271127469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624597105270345514084979 5436895657905518271127469)
                ·
                  refine ⟨2038835871714569351672801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5436895657905518271127469 2038835871714569351672801)
                  ·
                    refine ⟨1529126903785927013754601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038835871714569351672801 1529126903785927013754601)
                    ·
                      refine ⟨1146845177839445260315951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529126903785927013754601 1146845177839445260315951)
                      ·
                        rfl

theorem cell23_2233473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_2233473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233473 prefixEnd_2233473 := by exact prefixLift 2233473
  have htrace : WordTrace (prefixWord ++ tailWord_2233473) baseStart_2233473 baseEnd_2233473 := by
    simpa [prefixWord, tailWord_2233473, baseEnd_2233473] using wordTrace_append hprefix tailTrace_2233473
  have hstable : (prefixWord ++ tailWord_2233473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233473).length < 2 ^ (prefixWord ++ tailWord_2233473).sum := by decide
  have hdescent : baseEnd_2233473 < baseStart_2233473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233482 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2233482 : Nat := 118140960795 + 2233482 * 2 ^ 59
def prefixEnd_2233482 : Nat := 4983230072969 + 3 ^ 40 * 2233482 * 2
def baseEnd_2233482 : Nat := 1146849799165335725103409

theorem tailTrace_2233482 : CollatzResearch.WordTrace tailWord_2233482 prefixEnd_2233482 1146849799165335725103409 := by
  unfold tailWord_2233482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365445223620909300513675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54307853929655758134703133 20365445223620909300513675)
  ·
    refine ⟨30548167835431363950770513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365445223620909300513675 30548167835431363950770513)
    ·
      refine ⟨22911125876573522963077885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30548167835431363950770513 22911125876573522963077885)
      ·
        refine ⟨8591672203715071111154207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22911125876573522963077885 8591672203715071111154207)
        ·
          refine ⟨12887508305572606666731311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8591672203715071111154207 12887508305572606666731311)
          ·
            refine ⟨19331262458358910000096967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12887508305572606666731311 19331262458358910000096967)
            ·
              refine ⟨28996893687538365000145451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19331262458358910000096967 28996893687538365000145451)
              ·
                refine ⟨43495340531307547500218177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28996893687538365000145451 43495340531307547500218177)
                ·
                  refine ⟨32621505398480660625163633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43495340531307547500218177 32621505398480660625163633)
                  ·
                    refine ⟨24466129048860495468872725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32621505398480660625163633 24466129048860495468872725)
                    ·
                      refine ⟨1146849799165335725103409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24466129048860495468872725 1146849799165335725103409)
                      ·
                        rfl

theorem cell23_2233482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2233482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233482 prefixEnd_2233482 := by exact prefixLift 2233482
  have htrace : WordTrace (prefixWord ++ tailWord_2233482) baseStart_2233482 baseEnd_2233482 := by
    simpa [prefixWord, tailWord_2233482, baseEnd_2233482] using wordTrace_append hprefix tailTrace_2233482
  have hstable : (prefixWord ++ tailWord_2233482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233482).length < 2 ^ (prefixWord ++ tailWord_2233482).sum := by decide
  have hdescent : baseEnd_2233482 < baseStart_2233482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233546 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_2233546 : Nat := 118140960795 + 2233546 * 2 ^ 59
def prefixEnd_2233546 : Nat := 4983230072969 + 3 ^ 40 * 2233546 * 2
def baseEnd_2233546 : Nat := 1146882661927223474703115

theorem tailTrace_2233546 : CollatzResearch.WordTrace tailWord_2233546 prefixEnd_2233546 1146882661927223474703115 := by
  unfold tailWord_2233546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366028791562944033096123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54309410110834517421589661 20366028791562944033096123)
  ·
    refine ⟨30549043187344416049644185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20366028791562944033096123 30549043187344416049644185)
    ·
      refine ⟨22911782390508312037233139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30549043187344416049644185 22911782390508312037233139)
      ·
        refine ⟨34367673585762468055849709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22911782390508312037233139 34367673585762468055849709)
        ·
          refine ⟨12887877594660925520943641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34367673585762468055849709 12887877594660925520943641)
          ·
            refine ⟨9665908195995694140707731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12887877594660925520943641 9665908195995694140707731)
            ·
              refine ⟨14498862293993541211061597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9665908195995694140707731 14498862293993541211061597)
              ·
                refine ⟨5437073360247577954148099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14498862293993541211061597 5437073360247577954148099)
                ·
                  refine ⟨8155610040371366931222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437073360247577954148099 8155610040371366931222149)
                  ·
                    refine ⟨1529176882569631299604153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8155610040371366931222149 1529176882569631299604153)
                    ·
                      refine ⟨1146882661927223474703115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529176882569631299604153 1146882661927223474703115)
                      ·
                        rfl

theorem cell23_2233546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_2233546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233546 prefixEnd_2233546 := by exact prefixLift 2233546
  have htrace : WordTrace (prefixWord ++ tailWord_2233546) baseStart_2233546 baseEnd_2233546 := by
    simpa [prefixWord, tailWord_2233546, baseEnd_2233546] using wordTrace_append hprefix tailTrace_2233546
  have hstable : (prefixWord ++ tailWord_2233546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233546).length < 2 ^ (prefixWord ++ tailWord_2233546).sum := by decide
  have hdescent : baseEnd_2233546 < baseStart_2233546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2233562 : Nat := 118140960795 + 2233562 * 2 ^ 59
def prefixEnd_2233562 : Nat := 4983230072969 + 3 ^ 40 * 2233562 * 2
def baseEnd_2233562 : Nat := 1146890877617695412103041

theorem tailTrace_2233562 : CollatzResearch.WordTrace tailWord_2233562 prefixEnd_2233562 1146890877617695412103041 := by
  unfold tailWord_2233562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366174683548452716241735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54309799156129207243311293 20366174683548452716241735)
  ·
    refine ⟨30549262025322679074362603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20366174683548452716241735 30549262025322679074362603)
    ·
      refine ⟨45823893037984018611543905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30549262025322679074362603 45823893037984018611543905)
      ·
        refine ⟨34367919778488013958657929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45823893037984018611543905 34367919778488013958657929)
        ·
          refine ⟨25775939833866010468993447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34367919778488013958657929 25775939833866010468993447)
          ·
            refine ⟨38663909750799015703490171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25775939833866010468993447 38663909750799015703490171)
            ·
              refine ⟨57995864626198523555235257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38663909750799015703490171 57995864626198523555235257)
              ·
                refine ⟨43496898469648892666426443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57995864626198523555235257 43496898469648892666426443)
                ·
                  refine ⟨65245347704473338999639665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43496898469648892666426443 65245347704473338999639665)
                  ·
                    refine ⟨48934010778355004249729749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65245347704473338999639665 48934010778355004249729749)
                    ·
                      refine ⟨1146890877617695412103041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48934010778355004249729749 1146890877617695412103041)
                      ·
                        rfl

theorem cell23_2233562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2233562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233562 prefixEnd_2233562 := by exact prefixLift 2233562
  have htrace : WordTrace (prefixWord ++ tailWord_2233562) baseStart_2233562 baseEnd_2233562 := by
    simpa [prefixWord, tailWord_2233562, baseEnd_2233562] using wordTrace_append hprefix tailTrace_2233562
  have hstable : (prefixWord ++ tailWord_2233562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233562).length < 2 ^ (prefixWord ++ tailWord_2233562).sum := by decide
  have hdescent : baseEnd_2233562 < baseStart_2233562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233579 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3]
def baseStart_2233579 : Nat := 118140960795 + 2233579 * 2 ^ 59
def prefixEnd_2233579 : Nat := 4983230072969 + 3 ^ 40 * 2233579 * 2
def baseEnd_2233579 : Nat := 1146899606788821845590463

theorem tailTrace_2233579 : CollatzResearch.WordTrace tailWord_2233579 prefixEnd_2233579 1146899606788821845590463 := by
  unfold tailWord_2233579
  simp only [CollatzResearch.WordTrace]
  refine ⟨81465318775132222768335791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54310212516754815178890527 81465318775132222768335791)
  ·
    refine ⟨122197978162698334152503687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81465318775132222768335791 122197978162698334152503687)
    ·
      refine ⟨183296967244047501228755531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122197978162698334152503687 183296967244047501228755531)
      ·
        refine ⟨274945450866071251843133297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183296967244047501228755531 274945450866071251843133297)
        ·
          refine ⟨206209088149553438882349973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274945450866071251843133297 206209088149553438882349973)
          ·
            refine ⟨9666051007010317447610155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206209088149553438882349973 9666051007010317447610155)
            ·
              refine ⟨14499076510515476171415233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666051007010317447610155 14499076510515476171415233)
              ·
                refine ⟨10874307382886607128561425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14499076510515476171415233 10874307382886607128561425)
                ·
                  refine ⟨8155730537164955346421069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10874307382886607128561425 8155730537164955346421069)
                  ·
                    refine ⟨3058398951436858254907901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8155730537164955346421069 3058398951436858254907901)
                    ·
                      refine ⟨1146899606788821845590463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058398951436858254907901 1146899606788821845590463)
                      ·
                        rfl

theorem cell23_2233579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].length) (baseStart_2233579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233579 prefixEnd_2233579 := by exact prefixLift 2233579
  have htrace : WordTrace (prefixWord ++ tailWord_2233579) baseStart_2233579 baseEnd_2233579 := by
    simpa [prefixWord, tailWord_2233579, baseEnd_2233579] using wordTrace_append hprefix tailTrace_2233579
  have hstable : (prefixWord ++ tailWord_2233579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233579).length < 2 ^ (prefixWord ++ tailWord_2233579).sum := by decide
  have hdescent : baseEnd_2233579 < baseStart_2233579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233580 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_2233580 : Nat := 118140960795 + 2233580 * 2 ^ 59
def prefixEnd_2233580 : Nat := 4983230072969 + 3 ^ 40 * 2233580 * 2
def baseEnd_2233580 : Nat := 1146900120269476341677959

theorem tailTrace_2233580 : CollatzResearch.WordTrace tailWord_2233580 prefixEnd_2233580 1146900120269476341677959 := by
  unfold tailWord_2233580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40732677624064299969561097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54310236832085733292748129 40732677624064299969561097)
  ·
    refine ⟨30549508218048224977170823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40732677624064299969561097 30549508218048224977170823)
    ·
      refine ⟨45824262327072337465756235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30549508218048224977170823 45824262327072337465756235)
      ·
        refine ⟨68736393490608506198634353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45824262327072337465756235 68736393490608506198634353)
        ·
          refine ⟨51552295117956379648975765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68736393490608506198634353 51552295117956379648975765)
          ·
            refine ⟨2416513833654205296045739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51552295117956379648975765 2416513833654205296045739)
            ·
              refine ⟨3624770750481307944068609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416513833654205296045739 3624770750481307944068609)
              ·
                refine ⟨2718578062860980958051457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624770750481307944068609 2718578062860980958051457)
                ·
                  refine ⟨2038933547145735718538593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2718578062860980958051457 2038933547145735718538593)
                  ·
                    refine ⟨1529200160359301788903945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2038933547145735718538593 1529200160359301788903945)
                    ·
                      refine ⟨1146900120269476341677959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529200160359301788903945 1146900120269476341677959)
                      ·
                        rfl

theorem cell23_2233580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_2233580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233580 prefixEnd_2233580 := by exact prefixLift 2233580
  have htrace : WordTrace (prefixWord ++ tailWord_2233580) baseStart_2233580 baseEnd_2233580 := by
    simpa [prefixWord, tailWord_2233580, baseEnd_2233580] using wordTrace_append hprefix tailTrace_2233580
  have hstable : (prefixWord ++ tailWord_2233580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233580).length < 2 ^ (prefixWord ++ tailWord_2233580).sum := by decide
  have hdescent : baseEnd_2233580 < baseStart_2233580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233586 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_2233586 : Nat := 118140960795 + 2233586 * 2 ^ 59
def prefixEnd_2233586 : Nat := 4983230072969 + 3 ^ 40 * 2233586 * 2
def baseEnd_2233586 : Nat := 127433689017044813133659

theorem tailTrace_2233586 : CollatzResearch.WordTrace tailWord_2233586 prefixEnd_2233586 127433689017044813133659 := by
  unfold tailWord_2233586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366393521526715740960153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54310382724071241975893741 20366393521526715740960153)
  ·
    refine ⟨15274795141145036805720115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20366393521526715740960153 15274795141145036805720115)
    ·
      refine ⟨22912192711717555208580173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274795141145036805720115 22912192711717555208580173)
      ·
        refine ⟨8592072266894083203217565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22912192711717555208580173 8592072266894083203217565)
        ·
          refine ⟨3222027100085281201206587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8592072266894083203217565 3222027100085281201206587)
          ·
            refine ⟨4833040650127921801809881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222027100085281201206587 4833040650127921801809881)
            ·
              refine ⟨3624780487595941351357411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833040650127921801809881 3624780487595941351357411)
              ·
                refine ⟨5437170731393912027036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624780487595941351357411 5437170731393912027036117)
                ·
                  refine ⟨127433689017044813133659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5437170731393912027036117 127433689017044813133659)
                  ·
                    rfl

theorem cell23_2233586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_2233586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233586 prefixEnd_2233586 := by exact prefixLift 2233586
  have htrace : WordTrace (prefixWord ++ tailWord_2233586) baseStart_2233586 baseEnd_2233586 := by
    simpa [prefixWord, tailWord_2233586, baseEnd_2233586] using wordTrace_append hprefix tailTrace_2233586
  have hstable : (prefixWord ++ tailWord_2233586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233586).length < 2 ^ (prefixWord ++ tailWord_2233586).sum := by decide
  have hdescent : baseEnd_2233586 < baseStart_2233586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233636 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2233636 : Nat := 118140960795 + 2233636 * 2 ^ 59
def prefixEnd_2233636 : Nat := 4983230072969 + 3 ^ 40 * 2233636 * 2
def baseEnd_2233636 : Nat := 1146928875186128122577701

theorem tailTrace_2233636 : CollatzResearch.WordTrace tailWord_2233636 prefixEnd_2233636 1146928875186128122577701 := by
  unfold tailWord_2233636
  simp only [CollatzResearch.WordTrace]
  refine ⟨40733698867962860751580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54311598490617147668773841 40733698867962860751580381)
  ·
    refine ⟨15275137075486072781842643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40733698867962860751580381 15275137075486072781842643)
    ·
      refine ⟨22912705613229109172763965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15275137075486072781842643 22912705613229109172763965)
      ·
        refine ⟨8592264604960915939786487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22912705613229109172763965 8592264604960915939786487)
        ·
          refine ⟨12888396907441373909679731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592264604960915939786487 12888396907441373909679731)
          ·
            refine ⟨19332595361162060864519597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888396907441373909679731 19332595361162060864519597)
            ·
              refine ⟨7249723260435772824194849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19332595361162060864519597 7249723260435772824194849)
              ·
                refine ⟨5437292445326829618146137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7249723260435772824194849 5437292445326829618146137)
                ·
                  refine ⟨4077969333995122213609603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437292445326829618146137 4077969333995122213609603)
                  ·
                    refine ⟨6116954000992683320414405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077969333995122213609603 6116954000992683320414405)
                    ·
                      refine ⟨1146928875186128122577701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6116954000992683320414405 1146928875186128122577701)
                      ·
                        rfl

theorem cell23_2233636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2233636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233636 prefixEnd_2233636 := by exact prefixLift 2233636
  have htrace : WordTrace (prefixWord ++ tailWord_2233636) baseStart_2233636 baseEnd_2233636 := by
    simpa [prefixWord, tailWord_2233636, baseEnd_2233636] using wordTrace_append hprefix tailTrace_2233636
  have hstable : (prefixWord ++ tailWord_2233636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233636).length < 2 ^ (prefixWord ++ tailWord_2233636).sum := by decide
  have hdescent : baseEnd_2233636 < baseStart_2233636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233669 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_2233669 : Nat := 118140960795 + 2233669 * 2 ^ 59
def prefixEnd_2233669 : Nat := 4983230072969 + 3 ^ 40 * 2233669 * 2
def baseEnd_2233669 : Nat := 1146945820047726493465049

theorem tailTrace_2233669 : CollatzResearch.WordTrace tailWord_2233669 prefixEnd_2233669 1146945820047726493465049 := by
  unfold tailWord_2233669
  simp only [CollatzResearch.WordTrace]
  refine ⟨81468601344806168139112061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54312400896537445426074707 81468601344806168139112061)
  ·
    refine ⟨30550725504302313052167023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81468601344806168139112061 30550725504302313052167023)
    ·
      refine ⟨45826088256453469578250535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30550725504302313052167023 45826088256453469578250535)
      ·
        refine ⟨68739132384680204367375803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45826088256453469578250535 68739132384680204367375803)
        ·
          refine ⟨103108698577020306551063705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68739132384680204367375803 103108698577020306551063705)
          ·
            refine ⟨77331523932765229913297779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103108698577020306551063705 77331523932765229913297779)
            ·
              refine ⟨115997285899147844869946669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77331523932765229913297779 115997285899147844869946669)
              ·
                refine ⟨43498982212180441826230001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115997285899147844869946669 43498982212180441826230001)
                ·
                  refine ⟨32624236659135331369672501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43498982212180441826230001 32624236659135331369672501)
                  ·
                    refine ⟨3058522186793937315906797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32624236659135331369672501 3058522186793937315906797)
                    ·
                      refine ⟨1146945820047726493465049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058522186793937315906797 1146945820047726493465049)
                      ·
                        rfl

theorem cell23_2233669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_2233669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233669 prefixEnd_2233669 := by exact prefixLift 2233669
  have htrace : WordTrace (prefixWord ++ tailWord_2233669) baseStart_2233669 baseEnd_2233669 := by
    simpa [prefixWord, tailWord_2233669, baseEnd_2233669] using wordTrace_append hprefix tailTrace_2233669
  have hstable : (prefixWord ++ tailWord_2233669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233669).length < 2 ^ (prefixWord ++ tailWord_2233669).sum := by decide
  have hdescent : baseEnd_2233669 < baseStart_2233669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233736 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2233736 : Nat := 118140960795 + 2233736 * 2 ^ 59
def prefixEnd_2233736 : Nat := 4983230072969 + 3 ^ 40 * 2233736 * 2
def baseEnd_2233736 : Nat := 382326741083859243775747

theorem tailTrace_2233736 : CollatzResearch.WordTrace tailWord_2233736 prefixEnd_2233736 382326741083859243775747 := by
  unfold tailWord_2233736
  simp only [CollatzResearch.WordTrace]
  refine ⟨40735522517781719290900531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54314030023708959054534041 40735522517781719290900531)
  ·
    refine ⟨61103283776672578936350797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40735522517781719290900531 61103283776672578936350797)
    ·
      refine ⟨22913731416252217101131549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61103283776672578936350797 22913731416252217101131549)
      ·
        refine ⟨8592649281094581412924331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22913731416252217101131549 8592649281094581412924331)
        ·
          refine ⟨12888973921641872119386497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592649281094581412924331 12888973921641872119386497)
          ·
            refine ⟨9666730441231404089539873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12888973921641872119386497 9666730441231404089539873)
            ·
              refine ⟨7250047830923553067154905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9666730441231404089539873 7250047830923553067154905)
              ·
                refine ⟨5437535873192664800366179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7250047830923553067154905 5437535873192664800366179)
                ·
                  refine ⟨8156303809788997200549269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437535873192664800366179 8156303809788997200549269)
                  ·
                    refine ⟨382326741083859243775747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8156303809788997200549269 382326741083859243775747)
                    ·
                      rfl

theorem cell23_2233736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2233736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233736 prefixEnd_2233736 := by exact prefixLift 2233736
  have htrace : WordTrace (prefixWord ++ tailWord_2233736) baseStart_2233736 baseEnd_2233736 := by
    simpa [prefixWord, tailWord_2233736, baseEnd_2233736] using wordTrace_append hprefix tailTrace_2233736
  have hstable : (prefixWord ++ tailWord_2233736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233736).length < 2 ^ (prefixWord ++ tailWord_2233736).sum := by decide
  have hdescent : baseEnd_2233736 < baseStart_2233736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233737 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 1, 1, 3]
def baseStart_2233737 : Nat := 118140960795 + 2233737 * 2 ^ 59
def prefixEnd_2233737 : Nat := 4983230072969 + 3 ^ 40 * 2233737 * 2
def baseEnd_2233737 : Nat := 1146980736732232227414737

theorem tailTrace_2233737 : CollatzResearch.WordTrace tailWord_2233737 prefixEnd_2233737 1146980736732232227414737 := by
  unfold tailWord_2233737
  simp only [CollatzResearch.WordTrace]
  refine ⟨81471081508559815752587465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54314054339039877168391643 81471081508559815752587465)
  ·
    refine ⟨61103311131419861814440599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81471081508559815752587465 61103311131419861814440599)
    ·
      refine ⟨91654966697129792721660899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61103311131419861814440599 91654966697129792721660899)
      ·
        refine ⟨137482450045694689082491349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91654966697129792721660899 137482450045694689082491349)
        ·
          refine ⟨3222244922945969275370891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 137482450045694689082491349 3222244922945969275370891)
          ·
            refine ⟨4833367384418953913056337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222244922945969275370891 4833367384418953913056337)
            ·
              refine ⟨3625025538314215434792253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833367384418953913056337 3625025538314215434792253)
              ·
                refine ⟨1359384576867830788047095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3625025538314215434792253 1359384576867830788047095)
                ·
                  refine ⟨2039076865301746182070643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359384576867830788047095 2039076865301746182070643)
                  ·
                    refine ⟨3058615297952619273105965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039076865301746182070643 3058615297952619273105965)
                    ·
                      refine ⟨1146980736732232227414737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058615297952619273105965 1146980736732232227414737)
                      ·
                        rfl

theorem cell23_2233737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 1, 3].length) (baseStart_2233737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233737 prefixEnd_2233737 := by exact prefixLift 2233737
  have htrace : WordTrace (prefixWord ++ tailWord_2233737) baseStart_2233737 baseEnd_2233737 := by
    simpa [prefixWord, tailWord_2233737, baseEnd_2233737] using wordTrace_append hprefix tailTrace_2233737
  have hstable : (prefixWord ++ tailWord_2233737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233737).length < 2 ^ (prefixWord ++ tailWord_2233737).sum := by decide
  have hdescent : baseEnd_2233737 < baseStart_2233737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233753 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_2233753 : Nat := 118140960795 + 2233753 * 2 ^ 59
def prefixEnd_2233753 : Nat := 4983230072969 + 3 ^ 40 * 2233753 * 2
def baseEnd_2233753 : Nat := 382329650807568054938221

theorem tailTrace_2233753 : CollatzResearch.WordTrace tailWord_2233753 prefixEnd_2233753 382329650807568054938221 := by
  unfold tailWord_2233753
  simp only [CollatzResearch.WordTrace]
  refine ⟨81471665076501850485169913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54314443384334566990113275 81471665076501850485169913)
  ·
    refine ⟨61103748807376387863877435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81471665076501850485169913 61103748807376387863877435)
    ·
      refine ⟨91655623211064581795816153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61103748807376387863877435 91655623211064581795816153)
      ·
        refine ⟨68741717408298436346862115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91655623211064581795816153 68741717408298436346862115)
        ·
          refine ⟨103112576112447654520293173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68741717408298436346862115 103112576112447654520293173)
          ·
            refine ⟨9666804010541967611277485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103112576112447654520293173 9666804010541967611277485)
            ·
              refine ⟨3625051503953237854229057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9666804010541967611277485 3625051503953237854229057)
              ·
                refine ⟨2718788627964928390671793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3625051503953237854229057 2718788627964928390671793)
                ·
                  refine ⟨2039091470973696293003845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2718788627964928390671793 2039091470973696293003845)
                  ·
                    refine ⟨382329650807568054938221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2039091470973696293003845 382329650807568054938221)
                    ·
                      rfl

theorem cell23_2233753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_2233753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233753 prefixEnd_2233753 := by exact prefixLift 2233753
  have htrace : WordTrace (prefixWord ++ tailWord_2233753) baseStart_2233753 baseEnd_2233753 := by
    simpa [prefixWord, tailWord_2233753, baseEnd_2233753] using wordTrace_append hprefix tailTrace_2233753
  have hstable : (prefixWord ++ tailWord_2233753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233753).length < 2 ^ (prefixWord ++ tailWord_2233753).sum := by decide
  have hdescent : baseEnd_2233753 < baseStart_2233753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233760 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2]
def baseStart_2233760 : Nat := 118140960795 + 2233760 * 2 ^ 59
def prefixEnd_2233760 : Nat := 4983230072969 + 3 ^ 40 * 2233760 * 2
def baseEnd_2233760 : Nat := 1146992546787285637427131

theorem tailTrace_2233760 : CollatzResearch.WordTrace tailWord_2233760 prefixEnd_2233760 1146992546787285637427131 := by
  unfold tailWord_2233760
  simp only [CollatzResearch.WordTrace]
  refine ⟨40735960193738245340337367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54314613591650993787116489 40735960193738245340337367)
  ·
    refine ⟨61103940290607368010506051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40735960193738245340337367 61103940290607368010506051)
    ·
      refine ⟨91655910435911052015759077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61103940290607368010506051 91655910435911052015759077)
      ·
        refine ⟨17185483206733322252954827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91655910435911052015759077 17185483206733322252954827)
        ·
          refine ⟨25778224810099983379432241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17185483206733322252954827 25778224810099983379432241)
          ·
            refine ⟨19333668607574987534574181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25778224810099983379432241 19333668607574987534574181)
            ·
              refine ⟨3625062863920310162732659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19333668607574987534574181 3625062863920310162732659)
              ·
                refine ⟨5437594295880465244098989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625062863920310162732659 5437594295880465244098989)
                ·
                  refine ⟨2039097860955174466537121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5437594295880465244098989 2039097860955174466537121)
                  ·
                    refine ⟨1529323395716380849902841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2039097860955174466537121 1529323395716380849902841)
                    ·
                      refine ⟨1146992546787285637427131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529323395716380849902841 1146992546787285637427131)
                      ·
                        rfl

theorem cell23_2233760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_2233760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233760 prefixEnd_2233760 := by exact prefixLift 2233760
  have htrace : WordTrace (prefixWord ++ tailWord_2233760) baseStart_2233760 baseEnd_2233760 := by
    simpa [prefixWord, tailWord_2233760, baseEnd_2233760] using wordTrace_append hprefix tailTrace_2233760
  have hstable : (prefixWord ++ tailWord_2233760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233760).length < 2 ^ (prefixWord ++ tailWord_2233760).sum := by decide
  have hdescent : baseEnd_2233760 < baseStart_2233760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233773 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2233773 : Nat := 118140960795 + 2233773 * 2 ^ 59
def prefixEnd_2233773 : Nat := 4983230072969 + 3 ^ 40 * 2233773 * 2
def baseEnd_2233773 : Nat := 1146999222035794086564571

theorem tailTrace_2233773 : CollatzResearch.WordTrace tailWord_2233773 prefixEnd_2233773 1146999222035794086564571 := by
  unfold tailWord_2233773
  simp only [CollatzResearch.WordTrace]
  refine ⟨81472394536429393900897973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54314929690952929267265315 81472394536429393900897973)
  ·
    refine ⟨7638036987790255678209185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81472394536429393900897973 7638036987790255678209185)
    ·
      refine ⟨5728527740842691758656889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7638036987790255678209185 5728527740842691758656889)
      ·
        refine ⟨4296395805632018818992667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5728527740842691758656889 4296395805632018818992667)
        ·
          refine ⟨6444593708448028228489001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296395805632018818992667 6444593708448028228489001)
          ·
            refine ⟨4833445281336021171366751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6444593708448028228489001 4833445281336021171366751)
            ·
              refine ⟨7250167922004031757050127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4833445281336021171366751 7250167922004031757050127)
              ·
                refine ⟨10875251883006047635575191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250167922004031757050127 10875251883006047635575191)
                ·
                  refine ⟨16312877824509071453362787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10875251883006047635575191 16312877824509071453362787)
                  ·
                    refine ⟨24469316736763607180044181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16312877824509071453362787 24469316736763607180044181)
                    ·
                      refine ⟨1146999222035794086564571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24469316736763607180044181 1146999222035794086564571)
                      ·
                        rfl

theorem cell23_2233773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2233773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233773 prefixEnd_2233773 := by exact prefixLift 2233773
  have htrace : WordTrace (prefixWord ++ tailWord_2233773) baseStart_2233773 baseEnd_2233773 := by
    simpa [prefixWord, tailWord_2233773, baseEnd_2233773] using wordTrace_append hprefix tailTrace_2233773
  have hstable : (prefixWord ++ tailWord_2233773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233773).length < 2 ^ (prefixWord ++ tailWord_2233773).sum := by decide
  have hdescent : baseEnd_2233773 < baseStart_2233773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233776 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_2233776 : Nat := 118140960795 + 2233776 * 2 ^ 59
def prefixEnd_2233776 : Nat := 4983230072969 + 3 ^ 40 * 2233776 * 2
def baseEnd_2233776 : Nat := 1147000762477757574827057

theorem tailTrace_2233776 : CollatzResearch.WordTrace tailWord_2233776 prefixEnd_2233776 1147000762477757574827057 := by
  unfold tailWord_2233776
  simp only [CollatzResearch.WordTrace]
  refine ⟨40736251977709262706628591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54315002636945683608838121 40736251977709262706628591)
  ·
    refine ⟨61104377966563894059942887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40736251977709262706628591 61104377966563894059942887)
    ·
      refine ⟨91656566949845841089914331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61104377966563894059942887 91656566949845841089914331)
      ·
        refine ⟨137484850424768761634871497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91656566949845841089914331 137484850424768761634871497)
        ·
          refine ⟨103113637818576571226153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137484850424768761634871497 103113637818576571226153623)
          ·
            refine ⟨154670456727864856839230435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103113637818576571226153623 154670456727864856839230435)
            ·
              refine ⟨232005685091797285258845653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154670456727864856839230435 232005685091797285258845653)
              ·
                refine ⟨5437633244338998873254195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232005685091797285258845653 5437633244338998873254195)
                ·
                  refine ⟨8156449866508498309881293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437633244338998873254195 8156449866508498309881293)
                  ·
                    refine ⟨3058668699940686866205485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8156449866508498309881293 3058668699940686866205485)
                    ·
                      refine ⟨1147000762477757574827057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058668699940686866205485 1147000762477757574827057)
                      ·
                        rfl

theorem cell23_2233776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_2233776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233776 prefixEnd_2233776 := by exact prefixLift 2233776
  have htrace : WordTrace (prefixWord ++ tailWord_2233776) baseStart_2233776 baseEnd_2233776 := by
    simpa [prefixWord, tailWord_2233776, baseEnd_2233776] using wordTrace_append hprefix tailTrace_2233776
  have hstable : (prefixWord ++ tailWord_2233776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233776).length < 2 ^ (prefixWord ++ tailWord_2233776).sum := by decide
  have hdescent : baseEnd_2233776 < baseStart_2233776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233779 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 7]
def baseStart_2233779 : Nat := 118140960795 + 2233779 * 2 ^ 59
def prefixEnd_2233779 : Nat := 4983230072969 + 3 ^ 40 * 2233779 * 2
def baseEnd_2233779 : Nat := 382334100973240354363181

theorem tailTrace_2233779 : CollatzResearch.WordTrace tailWord_2233779 prefixEnd_2233779 382334100973240354363181 := by
  unfold tailWord_2233779
  simp only [CollatzResearch.WordTrace]
  refine ⟨81472613374407656925616391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54315075582938437950410927 81472613374407656925616391)
  ·
    refine ⟨122208920061611485388424587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81472613374407656925616391 122208920061611485388424587)
    ·
      refine ⟨183313380092417228082636881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122208920061611485388424587 183313380092417228082636881)
      ·
        refine ⟨137485035069312921061977661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183313380092417228082636881 137485035069312921061977661)
        ·
          refine ⟨51556888150992345398241623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137485035069312921061977661 51556888150992345398241623)
          ·
            refine ⟨77335332226488518097362435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51556888150992345398241623 77335332226488518097362435)
            ·
              refine ⟨116002998339732777146043653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77335332226488518097362435 116002998339732777146043653)
              ·
                refine ⟨21750562188699895714883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116002998339732777146043653 21750562188699895714883185)
                ·
                  refine ⟨16312921641524921786162389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21750562188699895714883185 16312921641524921786162389)
                  ·
                    refine ⟨382334100973240354363181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16312921641524921786162389 382334100973240354363181)
                    ·
                      rfl

theorem cell23_2233779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_2233779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233779 prefixEnd_2233779 := by exact prefixLift 2233779
  have htrace : WordTrace (prefixWord ++ tailWord_2233779) baseStart_2233779 baseEnd_2233779 := by
    simpa [prefixWord, tailWord_2233779, baseEnd_2233779] using wordTrace_append hprefix tailTrace_2233779
  have hstable : (prefixWord ++ tailWord_2233779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233779).length < 2 ^ (prefixWord ++ tailWord_2233779).sum := by decide
  have hdescent : baseEnd_2233779 < baseStart_2233779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233827 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2233827 : Nat := 118140960795 + 2233827 * 2 ^ 59
def prefixEnd_2233827 : Nat := 4983230072969 + 3 ^ 40 * 2233827 * 2
def baseEnd_2233827 : Nat := 1147026949991136875289323

theorem tailTrace_2233827 : CollatzResearch.WordTrace tailWord_2233827 prefixEnd_2233827 1147026949991136875289323 := by
  unfold tailWord_2233827
  simp only [CollatzResearch.WordTrace]
  refine ⟨81474364078233761123363735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54316242718822507415575823 81474364078233761123363735)
  ·
    refine ⟨122211546117350641685045603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81474364078233761123363735 122211546117350641685045603)
    ·
      refine ⟨183317319176025962527568405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122211546117350641685045603 183317319176025962527568405)
      ·
        refine ⟨8592999336376216993479769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 183317319176025962527568405 8592999336376216993479769)
        ·
          refine ⟨6444749502282162745109827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8592999336376216993479769 6444749502282162745109827)
          ·
            refine ⟨9667124253423244117664741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444749502282162745109827 9667124253423244117664741)
            ·
              refine ⟨1812585797516858272062139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9667124253423244117664741 1812585797516858272062139)
              ·
                refine ⟨2718878696275287408093209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812585797516858272062139 2718878696275287408093209)
                ·
                  refine ⟨2039159022206465556069907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2718878696275287408093209 2039159022206465556069907)
                  ·
                    refine ⟨3058738533309698334104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039159022206465556069907 3058738533309698334104861)
                    ·
                      refine ⟨1147026949991136875289323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058738533309698334104861 1147026949991136875289323)
                      ·
                        rfl

theorem cell23_2233827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2233827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233827 prefixEnd_2233827 := by exact prefixLift 2233827
  have htrace : WordTrace (prefixWord ++ tailWord_2233827) baseStart_2233827 baseEnd_2233827 := by
    simpa [prefixWord, tailWord_2233827, baseEnd_2233827] using wordTrace_append hprefix tailTrace_2233827
  have hstable : (prefixWord ++ tailWord_2233827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233827).length < 2 ^ (prefixWord ++ tailWord_2233827).sum := by decide
  have hdescent : baseEnd_2233827 < baseStart_2233827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233836 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_2233836 : Nat := 118140960795 + 2233836 * 2 ^ 59
def prefixEnd_2233836 : Nat := 4983230072969 + 3 ^ 40 * 2233836 * 2
def baseEnd_2233836 : Nat := 1147031571317027340076781

theorem tailTrace_2233836 : CollatzResearch.WordTrace tailWord_2233836 prefixEnd_2233836 1147031571317027340076781 := by
  unfold tailWord_2233836
  simp only [CollatzResearch.WordTrace]
  refine ⟨40737346167600577830220681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54316461556800770440294241 40737346167600577830220681)
  ·
    refine ⟨30553009625700433372665511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40737346167600577830220681 30553009625700433372665511)
    ·
      refine ⟨45829514438550650058998267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30553009625700433372665511 45829514438550650058998267)
      ·
        refine ⟨68744271657825975088497401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45829514438550650058998267 68744271657825975088497401)
        ·
          refine ⟨51558203743369481316373051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68744271657825975088497401 51558203743369481316373051)
          ·
            refine ⟨77337305615054221974559577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51558203743369481316373051 77337305615054221974559577)
            ·
              refine ⟨58002979211290666480919683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77337305615054221974559577 58002979211290666480919683)
              ·
                refine ⟨87004468816935999721379525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58002979211290666480919683 87004468816935999721379525)
                ·
                  refine ⟨16313337903175499947758661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87004468816935999721379525 16313337903175499947758661)
                  ·
                    refine ⟨3058750856845406240204749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16313337903175499947758661 3058750856845406240204749)
                    ·
                      refine ⟨1147031571317027340076781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058750856845406240204749 1147031571317027340076781)
                      ·
                        rfl

theorem cell23_2233836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_2233836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233836 prefixEnd_2233836 := by exact prefixLift 2233836
  have htrace : WordTrace (prefixWord ++ tailWord_2233836) baseStart_2233836 baseEnd_2233836 := by
    simpa [prefixWord, tailWord_2233836, baseEnd_2233836] using wordTrace_append hprefix tailTrace_2233836
  have hstable : (prefixWord ++ tailWord_2233836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233836).length < 2 ^ (prefixWord ++ tailWord_2233836).sum := by decide
  have hdescent : baseEnd_2233836 < baseStart_2233836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233837 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2233837 : Nat := 118140960795 + 2233837 * 2 ^ 59
def prefixEnd_2233837 : Nat := 4983230072969 + 3 ^ 40 * 2233837 * 2
def baseEnd_2233837 : Nat := 1147032084797681836164277

theorem tailTrace_2233837 : CollatzResearch.WordTrace tailWord_2233837 prefixEnd_2233837 1147032084797681836164277 := by
  unfold tailWord_2233837
  simp only [CollatzResearch.WordTrace]
  refine ⟨81474728808197532831227765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54316485872131688554151843 81474728808197532831227765)
  ·
    refine ⟨7638255825768518702927603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81474728808197532831227765 7638255825768518702927603)
    ·
      refine ⟨11457383738652778054391405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7638255825768518702927603 11457383738652778054391405)
      ·
        refine ⟨4296518901994791770396777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11457383738652778054391405 4296518901994791770396777)
        ·
          refine ⟨3222389176496093827797583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4296518901994791770396777 3222389176496093827797583)
          ·
            refine ⟨4833583764744140741696375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222389176496093827797583 4833583764744140741696375)
            ·
              refine ⟨7250375647116211112544563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4833583764744140741696375 7250375647116211112544563)
              ·
                refine ⟨10875563470674316668816845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250375647116211112544563 10875563470674316668816845)
                ·
                  refine ⟨4078336301502868750806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10875563470674316668816845 4078336301502868750806317)
                  ·
                    refine ⟨1529376113063575781552369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4078336301502868750806317 1529376113063575781552369)
                    ·
                      refine ⟨1147032084797681836164277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529376113063575781552369 1147032084797681836164277)
                      ·
                        rfl

theorem cell23_2233837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2233837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233837 prefixEnd_2233837 := by exact prefixLift 2233837
  have htrace : WordTrace (prefixWord ++ tailWord_2233837) baseStart_2233837 baseEnd_2233837 := by
    simpa [prefixWord, tailWord_2233837, baseEnd_2233837] using wordTrace_append hprefix tailTrace_2233837
  have hstable : (prefixWord ++ tailWord_2233837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233837).length < 2 ^ (prefixWord ++ tailWord_2233837).sum := by decide
  have hdescent : baseEnd_2233837 < baseStart_2233837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233862 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2233862 : Nat := 118140960795 + 2233862 * 2 ^ 59
def prefixEnd_2233862 : Nat := 4983230072969 + 3 ^ 40 * 2233862 * 2
def baseEnd_2233862 : Nat := 1147044921814044238351663

theorem tailTrace_2233862 : CollatzResearch.WordTrace tailWord_2233862 prefixEnd_2233862 1147044921814044238351663 := by
  unfold tailWord_2233862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546113769784592565652745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54317093755404641400591893 2546113769784592565652745)
  ·
    refine ⟨1909585327338444424239559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546113769784592565652745 1909585327338444424239559)
    ·
      refine ⟨2864377991007666636359339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909585327338444424239559 2864377991007666636359339)
      ·
        refine ⟨4296566986511499954539009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864377991007666636359339 4296566986511499954539009)
        ·
          refine ⟨3222425239883624965904257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4296566986511499954539009 3222425239883624965904257)
          ·
            refine ⟨2416818929912718724428193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222425239883624965904257 2416818929912718724428193)
            ·
              refine ⟨1812614197434539043321145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416818929912718724428193 1812614197434539043321145)
              ·
                refine ⟨1359460648075904282490859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812614197434539043321145 1359460648075904282490859)
                ·
                  refine ⟨2039190972113856423736289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359460648075904282490859 2039190972113856423736289)
                  ·
                    refine ⟨1529393229085392317802217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2039190972113856423736289 1529393229085392317802217)
                    ·
                      refine ⟨1147044921814044238351663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529393229085392317802217 1147044921814044238351663)
                      ·
                        rfl

theorem cell23_2233862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2233862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233862 prefixEnd_2233862 := by exact prefixLift 2233862
  have htrace : WordTrace (prefixWord ++ tailWord_2233862) baseStart_2233862 baseEnd_2233862 := by
    simpa [prefixWord, tailWord_2233862, baseEnd_2233862] using wordTrace_append hprefix tailTrace_2233862
  have hstable : (prefixWord ++ tailWord_2233862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233862).length < 2 ^ (prefixWord ++ tailWord_2233862).sum := by decide
  have hdescent : baseEnd_2233862 < baseStart_2233862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233873 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 5]
def baseStart_2233873 : Nat := 118140960795 + 2233873 * 2 ^ 59
def prefixEnd_2233873 : Nat := 4983230072969 + 3 ^ 40 * 2233873 * 2
def baseEnd_2233873 : Nat := 127450063344582632812679

theorem tailTrace_2233873 : CollatzResearch.WordTrace tailWord_2233873 prefixEnd_2233873 127450063344582632812679 := by
  unfold tailWord_2233873
  simp only [CollatzResearch.WordTrace]
  refine ⟨81476041836067110979538273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54317361224044740653025515 81476041836067110979538273)
  ·
    refine ⟨61107031377050333234653705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81476041836067110979538273 61107031377050333234653705)
    ·
      refine ⟨45830273532787749925990279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61107031377050333234653705 45830273532787749925990279)
      ·
        refine ⟨68745410299181624888985419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45830273532787749925990279 68745410299181624888985419)
        ·
          refine ⟨103118115448772437333478129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68745410299181624888985419 103118115448772437333478129)
          ·
            refine ⟨77338586586579328000108597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103118115448772437333478129 77338586586579328000108597)
            ·
              refine ⟨7250492492491812000010181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77338586586579328000108597 7250492492491812000010181)
              ·
                refine ⟨1359467342342214750001909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7250492492491812000010181 1359467342342214750001909)
                ·
                  refine ⟨127450063344582632812679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359467342342214750001909 127450063344582632812679)
                  ·
                    rfl

theorem cell23_2233873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 5].length) (baseStart_2233873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233873 prefixEnd_2233873 := by exact prefixLift 2233873
  have htrace : WordTrace (prefixWord ++ tailWord_2233873) baseStart_2233873 baseEnd_2233873 := by
    simpa [prefixWord, tailWord_2233873, baseEnd_2233873] using wordTrace_append hprefix tailTrace_2233873
  have hstable : (prefixWord ++ tailWord_2233873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233873).length < 2 ^ (prefixWord ++ tailWord_2233873).sum := by decide
  have hdescent : baseEnd_2233873 < baseStart_2233873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233893 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_2233893 : Nat := 118140960795 + 2233893 * 2 ^ 59
def prefixEnd_2233893 : Nat := 4983230072969 + 3 ^ 40 * 2233893 * 2
def baseEnd_2233893 : Nat := 1147060839714333617064019

theorem tailTrace_2233893 : CollatzResearch.WordTrace tailWord_2233893 prefixEnd_2233893 1147060839714333617064019 := by
  unfold tailWord_2233893
  simp only [CollatzResearch.WordTrace]
  refine ⟨81476771295994654395266333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54317847530663102930177555 81476771295994654395266333)
  ·
    refine ⟨30553789235997995398224875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81476771295994654395266333 30553789235997995398224875)
    ·
      refine ⟨45830683853996993097337313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30553789235997995398224875 45830683853996993097337313)
      ·
        refine ⟨34373012890497744823002985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45830683853996993097337313 34373012890497744823002985)
        ·
          refine ⟨25779759667873308617252239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34373012890497744823002985 25779759667873308617252239)
          ·
            refine ⟨38669639501809962925878359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25779759667873308617252239 38669639501809962925878359)
            ·
              refine ⟨58004459252714944388817539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38669639501809962925878359 58004459252714944388817539)
              ·
                refine ⟨87006688879072416583226309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58004459252714944388817539 87006688879072416583226309)
                ·
                  refine ⟨16313754164826078109354933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87006688879072416583226309 16313754164826078109354933)
                  ·
                    refine ⟨1529414452952444822752025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16313754164826078109354933 1529414452952444822752025)
                    ·
                      refine ⟨1147060839714333617064019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529414452952444822752025 1147060839714333617064019)
                      ·
                        rfl

theorem cell23_2233893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_2233893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233893 prefixEnd_2233893 := by exact prefixLift 2233893
  have htrace : WordTrace (prefixWord ++ tailWord_2233893) baseStart_2233893 baseEnd_2233893 := by
    simpa [prefixWord, tailWord_2233893, baseEnd_2233893] using wordTrace_append hprefix tailTrace_2233893
  have hstable : (prefixWord ++ tailWord_2233893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233893).length < 2 ^ (prefixWord ++ tailWord_2233893).sum := by decide
  have hdescent : baseEnd_2233893 < baseStart_2233893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233936 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2233936 : Nat := 118140960795 + 2233936 * 2 ^ 59
def prefixEnd_2233936 : Nat := 4983230072969 + 3 ^ 40 * 2233936 * 2
def baseEnd_2233936 : Nat := 1147082919382476948826321

theorem tailTrace_2233936 : CollatzResearch.WordTrace tailWord_2233936 prefixEnd_2233936 1147082919382476948826321 := by
  unfold tailWord_2233936
  simp only [CollatzResearch.WordTrace]
  refine ⟨40739169817419436369540831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54318893089892581826054441 40739169817419436369540831)
  ·
    refine ⟨61108754726129154554311247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40739169817419436369540831 61108754726129154554311247)
    ·
      refine ⟨91663132089193731831466871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61108754726129154554311247 91663132089193731831466871)
      ·
        refine ⟨137494698133790597747200307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91663132089193731831466871 137494698133790597747200307)
        ·
          refine ⟨206242047200685896620800461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137494698133790597747200307 206242047200685896620800461)
          ·
            refine ⟨77340767700257211232800173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206242047200685896620800461 77340767700257211232800173)
            ·
              refine ⟨29002787887596454212300065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77340767700257211232800173 29002787887596454212300065)
              ·
                refine ⟨21752090915697340659225049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29002787887596454212300065 21752090915697340659225049)
                ·
                  refine ⟨16314068186773005494418787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21752090915697340659225049 16314068186773005494418787)
                  ·
                    refine ⟨24471102280159508241628181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16314068186773005494418787 24471102280159508241628181)
                    ·
                      refine ⟨1147082919382476948826321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24471102280159508241628181 1147082919382476948826321)
                      ·
                        rfl

theorem cell23_2233936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2233936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233936 prefixEnd_2233936 := by exact prefixLift 2233936
  have htrace : WordTrace (prefixWord ++ tailWord_2233936) baseStart_2233936 baseEnd_2233936 := by
    simpa [prefixWord, tailWord_2233936, baseEnd_2233936] using wordTrace_append hprefix tailTrace_2233936
  have hstable : (prefixWord ++ tailWord_2233936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233936).length < 2 ^ (prefixWord ++ tailWord_2233936).sum := by decide
  have hdescent : baseEnd_2233936 < baseStart_2233936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233940 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_2233940 : Nat := 118140960795 + 2233940 * 2 ^ 59
def prefixEnd_2233940 : Nat := 4983230072969 + 3 ^ 40 * 2233940 * 2
def baseEnd_2233940 : Nat := 1147084973305094933176303

theorem tailTrace_2233940 : CollatzResearch.WordTrace tailWord_2233940 prefixEnd_2233940 1147084973305094933176303 := by
  unfold tailWord_2233940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40739242763412190711113637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54318990351216254281484849 40739242763412190711113637)
  ·
    refine ⟨7638608018139785758333807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40739242763412190711113637 7638608018139785758333807)
    ·
      refine ⟨11457912027209678637500711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7638608018139785758333807 11457912027209678637500711)
      ·
        refine ⟨17186868040814517956251067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11457912027209678637500711 17186868040814517956251067)
        ·
          refine ⟨25780302061221776934376601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17186868040814517956251067 25780302061221776934376601)
          ·
            refine ⟨19335226545916332700782451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25780302061221776934376601 19335226545916332700782451)
            ·
              refine ⟨29002839818874499051173677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19335226545916332700782451 29002839818874499051173677)
              ·
                refine ⟨10876064932077937144190129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29002839818874499051173677 10876064932077937144190129)
                ·
                  refine ⟨8157048699058452858142597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10876064932077937144190129 8157048699058452858142597)
                  ·
                    refine ⟨1529446631073459910901737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8157048699058452858142597 1529446631073459910901737)
                    ·
                      refine ⟨1147084973305094933176303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529446631073459910901737 1147084973305094933176303)
                      ·
                        rfl

theorem cell23_2233940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_2233940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233940 prefixEnd_2233940 := by exact prefixLift 2233940
  have htrace : WordTrace (prefixWord ++ tailWord_2233940) baseStart_2233940 baseEnd_2233940 := by
    simpa [prefixWord, tailWord_2233940, baseEnd_2233940] using wordTrace_append hprefix tailTrace_2233940
  have hstable : (prefixWord ++ tailWord_2233940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233940).length < 2 ^ (prefixWord ++ tailWord_2233940).sum := by decide
  have hdescent : baseEnd_2233940 < baseStart_2233940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233943 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2233943 : Nat := 118140960795 + 2233943 * 2 ^ 59
def prefixEnd_2233943 : Nat := 4983230072969 + 3 ^ 40 * 2233943 * 2
def baseEnd_2233943 : Nat := 1147086513747058421438789

theorem tailTrace_2233943 : CollatzResearch.WordTrace tailWord_2233943 prefixEnd_2233943 1147086513747058421438789 := by
  unfold tailWord_2233943
  simp only [CollatzResearch.WordTrace]
  refine ⟨81478594945813512934586483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54319063297209008623057655 81478594945813512934586483)
  ·
    refine ⟨122217892418720269401879725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81478594945813512934586483 122217892418720269401879725)
    ·
      refine ⟨45831709657020101025704897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122217892418720269401879725 45831709657020101025704897)
      ·
        refine ⟨34373782242765075769278673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45831709657020101025704897 34373782242765075769278673)
        ·
          refine ⟨25780336682073806826959005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34373782242765075769278673 25780336682073806826959005)
          ·
            refine ⟨9667626255777677560109627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25780336682073806826959005 9667626255777677560109627)
            ·
              refine ⟨14501439383666516340164441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9667626255777677560109627 14501439383666516340164441)
              ·
                refine ⟨10876079537749887255123331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14501439383666516340164441 10876079537749887255123331)
                ·
                  refine ⟨16314119306624830882684997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10876079537749887255123331 16314119306624830882684997)
                  ·
                    refine ⟨3058897369992155790503437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16314119306624830882684997 3058897369992155790503437)
                    ·
                      refine ⟨1147086513747058421438789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058897369992155790503437 1147086513747058421438789)
                      ·
                        rfl

theorem cell23_2233943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2233943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233943 prefixEnd_2233943 := by exact prefixLift 2233943
  have htrace : WordTrace (prefixWord ++ tailWord_2233943) baseStart_2233943 baseEnd_2233943 := by
    simpa [prefixWord, tailWord_2233943, baseEnd_2233943] using wordTrace_append hprefix tailTrace_2233943
  have hstable : (prefixWord ++ tailWord_2233943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233943).length < 2 ^ (prefixWord ++ tailWord_2233943).sum := by decide
  have hdescent : baseEnd_2233943 < baseStart_2233943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233960 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2233960 : Nat := 118140960795 + 2233960 * 2 ^ 59
def prefixEnd_2233960 : Nat := 4983230072969 + 3 ^ 40 * 2233960 * 2
def baseEnd_2233960 : Nat := 1147095242918184854926211

theorem tailTrace_2233960 : CollatzResearch.WordTrace tailWord_2233960 prefixEnd_2233960 1147095242918184854926211 := by
  unfold tailWord_2233960
  simp only [CollatzResearch.WordTrace]
  refine ⟨40739607493375962418977667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54319476657834616558636889 40739607493375962418977667)
  ·
    refine ⟨61109411240063943628466501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40739607493375962418977667 61109411240063943628466501)
    ·
      refine ⟨11458014607511989430337469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61109411240063943628466501 11458014607511989430337469)
      ·
        refine ⟨4296755477816996036376551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11458014607511989430337469 4296755477816996036376551)
        ·
          refine ⟨6445133216725494054564827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296755477816996036376551 6445133216725494054564827)
          ·
            refine ⟨9667699825088241081847241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445133216725494054564827 9667699825088241081847241)
            ·
              refine ⟨7250774868816180811385431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667699825088241081847241 7250774868816180811385431)
              ·
                refine ⟨10876162303224271217078147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250774868816180811385431 10876162303224271217078147)
                ·
                  refine ⟨16314243454836406825617221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10876162303224271217078147 16314243454836406825617221)
                  ·
                    refine ⟨3058920647781826279803229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16314243454836406825617221 3058920647781826279803229)
                    ·
                      refine ⟨1147095242918184854926211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3058920647781826279803229 1147095242918184854926211)
                      ·
                        rfl

theorem cell23_2233960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2233960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2233960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2233960 prefixEnd_2233960 := by exact prefixLift 2233960
  have htrace : WordTrace (prefixWord ++ tailWord_2233960) baseStart_2233960 baseEnd_2233960 := by
    simpa [prefixWord, tailWord_2233960, baseEnd_2233960] using wordTrace_append hprefix tailTrace_2233960
  have hstable : (prefixWord ++ tailWord_2233960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233960).length < 2 ^ (prefixWord ++ tailWord_2233960).sum := by decide
  have hdescent : baseEnd_2233960 < baseStart_2233960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234017 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2234017 : Nat := 118140960795 + 2234017 * 2 ^ 59
def prefixEnd_2234017 : Nat := 4983230072969 + 3 ^ 40 * 2234017 * 2
def baseEnd_2234017 : Nat := 1147124511315491131913449

theorem tailTrace_2234017 : CollatzResearch.WordTrace tailWord_2234017 prefixEnd_2234017 1147124511315491131913449 := by
  unfold tailWord_2234017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81481293947545423572780305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54320862631696949048520203 81481293947545423572780305)
  ·
    refine ⟨61110970460659067679585229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81481293947545423572780305 61110970460659067679585229)
    ·
      refine ⟨22916613922747150379844461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61110970460659067679585229 22916613922747150379844461)
      ·
        refine ⟨8593730221030181392441673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22916613922747150379844461 8593730221030181392441673)
        ·
          refine ⟨6445297665772636044331255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8593730221030181392441673 6445297665772636044331255)
          ·
            refine ⟨9667946498658954066496883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445297665772636044331255 9667946498658954066496883)
            ·
              refine ⟨14501919747988431099745325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9667946498658954066496883 14501919747988431099745325)
              ·
                refine ⟨5438219905495661662404497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14501919747988431099745325 5438219905495661662404497)
                ·
                  refine ⟨4078664929121746246803373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5438219905495661662404497 4078664929121746246803373)
                  ·
                    refine ⟨1529499348420654842551265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4078664929121746246803373 1529499348420654842551265)
                    ·
                      refine ⟨1147124511315491131913449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529499348420654842551265 1147124511315491131913449)
                      ·
                        rfl

theorem cell23_2234017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2234017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234017 prefixEnd_2234017 := by exact prefixLift 2234017
  have htrace : WordTrace (prefixWord ++ tailWord_2234017) baseStart_2234017 baseEnd_2234017 := by
    simpa [prefixWord, tailWord_2234017, baseEnd_2234017] using wordTrace_append hprefix tailTrace_2234017
  have hstable : (prefixWord ++ tailWord_2234017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234017).length < 2 ^ (prefixWord ++ tailWord_2234017).sum := by decide
  have hdescent : baseEnd_2234017 < baseStart_2234017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234047 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 3, 2, 2]
def baseStart_2234047 : Nat := 118140960795 + 2234047 * 2 ^ 59
def prefixEnd_2234047 : Nat := 4983230072969 + 3 ^ 40 * 2234047 * 2
def baseEnd_2234047 : Nat := 1147139915735126014538311

theorem tailTrace_2234047 : CollatzResearch.WordTrace tailWord_2234047 prefixEnd_2234047 1147139915735126014538311 := by
  unfold tailWord_2234047
  simp only [CollatzResearch.WordTrace]
  refine ⟨81482388137436738696372395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54321592091624492464248263 81482388137436738696372395)
  ·
    refine ⟨122223582206155108044558593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81482388137436738696372395 122223582206155108044558593)
    ·
      refine ⟨91667686654616331033418945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122223582206155108044558593 91667686654616331033418945)
      ·
        refine ⟨68750764990962248275064209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91667686654616331033418945 68750764990962248275064209)
        ·
          refine ⟨51563073743221686206298157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68750764990962248275064209 51563073743221686206298157)
          ·
            refine ⟨19336152653708132327361809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51563073743221686206298157 19336152653708132327361809)
            ·
              refine ⟨14502114490281099245521357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19336152653708132327361809 14502114490281099245521357)
              ·
                refine ⟨5438292933855412217070509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14502114490281099245521357 5438292933855412217070509)
                ·
                  refine ⟨2039359850195779581401441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5438292933855412217070509 2039359850195779581401441)
                  ·
                    refine ⟨1529519887646834686051081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2039359850195779581401441 1529519887646834686051081)
                    ·
                      refine ⟨1147139915735126014538311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529519887646834686051081 1147139915735126014538311)
                      ·
                        rfl

theorem cell23_2234047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_2234047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234047 prefixEnd_2234047 := by exact prefixLift 2234047
  have htrace : WordTrace (prefixWord ++ tailWord_2234047) baseStart_2234047 baseEnd_2234047 := by
    simpa [prefixWord, tailWord_2234047, baseEnd_2234047] using wordTrace_append hprefix tailTrace_2234047
  have hstable : (prefixWord ++ tailWord_2234047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234047).length < 2 ^ (prefixWord ++ tailWord_2234047).sum := by decide
  have hdescent : baseEnd_2234047 < baseStart_2234047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234080 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2234080 : Nat := 118140960795 + 2234080 * 2 ^ 59
def prefixEnd_2234080 : Nat := 4983230072969 + 3 ^ 40 * 2234080 * 2
def baseEnd_2234080 : Nat := 1147156860596724385425659

theorem tailTrace_2234080 : CollatzResearch.WordTrace tailWord_2234080 prefixEnd_2234080 1147156860596724385425659 := by
  unfold tailWord_2234080
  simp only [CollatzResearch.WordTrace]
  refine ⟨40741795873158592666161847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54322394497544790221549129 40741795873158592666161847)
  ·
    refine ⟨61112693809737888999242771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40741795873158592666161847 61112693809737888999242771)
    ·
      refine ⟨91669040714606833498864157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61112693809737888999242771 91669040714606833498864157)
      ·
        refine ⟨34375890267977562562074059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91669040714606833498864157 34375890267977562562074059)
        ·
          refine ⟨51563835401966343843111089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34375890267977562562074059 51563835401966343843111089)
          ·
            refine ⟨38672876551474757882333317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51563835401966343843111089 38672876551474757882333317)
            ·
              refine ⟨7251164353401517102937497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38672876551474757882333317 7251164353401517102937497)
              ·
                refine ⟨5438373265051137827203123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7251164353401517102937497 5438373265051137827203123)
                ·
                  refine ⟨8157559897576706740804685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438373265051137827203123 8157559897576706740804685)
                  ·
                    refine ⟨3059084961591265027801757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157559897576706740804685 3059084961591265027801757)
                    ·
                      refine ⟨1147156860596724385425659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059084961591265027801757 1147156860596724385425659)
                      ·
                        rfl

theorem cell23_2234080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2234080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234080 prefixEnd_2234080 := by exact prefixLift 2234080
  have htrace : WordTrace (prefixWord ++ tailWord_2234080) baseStart_2234080 baseEnd_2234080 := by
    simpa [prefixWord, tailWord_2234080, baseEnd_2234080] using wordTrace_append hprefix tailTrace_2234080
  have hstable : (prefixWord ++ tailWord_2234080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234080).length < 2 ^ (prefixWord ++ tailWord_2234080).sum := by decide
  have hdescent : baseEnd_2234080 < baseStart_2234080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234081 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_2234081 : Nat := 118140960795 + 2234081 * 2 ^ 59
def prefixEnd_2234081 : Nat := 4983230072969 + 3 ^ 40 * 2234081 * 2
def baseEnd_2234081 : Nat := 1147157374077378881513155

theorem tailTrace_2234081 : CollatzResearch.WordTrace tailWord_2234081 prefixEnd_2234081 1147157374077378881513155 := by
  unfold tailWord_2234081
  simp only [CollatzResearch.WordTrace]
  refine ⟨81483628219313562503110097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54322418812875708335406731 81483628219313562503110097)
  ·
    refine ⟨61112721164485171877332573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81483628219313562503110097 61112721164485171877332573)
    ·
      refine ⟨22917270436681939453999715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61112721164485171877332573 22917270436681939453999715)
      ·
        refine ⟨34375905655022909180999573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22917270436681939453999715 34375905655022909180999573)
        ·
          refine ⟨1611370577579198867859355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34375905655022909180999573 1611370577579198867859355)
          ·
            refine ⟨2417055866368798301789033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611370577579198867859355 2417055866368798301789033)
            ·
              refine ⟨1812791899776598726341775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417055866368798301789033 1812791899776598726341775)
              ·
                refine ⟨2719187849664898089512663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812791899776598726341775 2719187849664898089512663)
                ·
                  refine ⟨4078781774497347134268995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719187849664898089512663 4078781774497347134268995)
                  ·
                    refine ⟨6118172661746020701403493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078781774497347134268995 6118172661746020701403493)
                    ·
                      refine ⟨1147157374077378881513155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6118172661746020701403493 1147157374077378881513155)
                      ·
                        rfl

theorem cell23_2234081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_2234081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234081 prefixEnd_2234081 := by exact prefixLift 2234081
  have htrace : WordTrace (prefixWord ++ tailWord_2234081) baseStart_2234081 baseEnd_2234081 := by
    simpa [prefixWord, tailWord_2234081, baseEnd_2234081] using wordTrace_append hprefix tailTrace_2234081
  have hstable : (prefixWord ++ tailWord_2234081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234081).length < 2 ^ (prefixWord ++ tailWord_2234081).sum := by decide
  have hdescent : baseEnd_2234081 < baseStart_2234081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234097 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_2234097 : Nat := 118140960795 + 2234097 * 2 ^ 59
def prefixEnd_2234097 : Nat := 4983230072969 + 3 ^ 40 * 2234097 * 2
def baseEnd_2234097 : Nat := 1147165589767850818913081

theorem tailTrace_2234097 : CollatzResearch.WordTrace tailWord_2234097 prefixEnd_2234097 1147165589767850818913081 := by
  unfold tailWord_2234097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81484211787255597235692545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54322807858170398157128363 81484211787255597235692545)
  ·
    refine ⟨61113158840441697926769409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81484211787255597235692545 61113158840441697926769409)
    ·
      refine ⟨45834869130331273445077057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61113158840441697926769409 45834869130331273445077057)
      ·
        refine ⟨34376151847748455083807793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45834869130331273445077057 34376151847748455083807793)
        ·
          refine ⟨25782113885811341312855845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34376151847748455083807793 25782113885811341312855845)
          ·
            refine ⟨4834146353589626496160471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25782113885811341312855845 4834146353589626496160471)
            ·
              refine ⟨7251219530384439744240707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834146353589626496160471 7251219530384439744240707)
              ·
                refine ⟨10876829295576659616361061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7251219530384439744240707 10876829295576659616361061)
                ·
                  refine ⟨2039405492920623678067699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10876829295576659616361061 2039405492920623678067699)
                  ·
                    refine ⟨3059108239380935517101549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039405492920623678067699 3059108239380935517101549)
                    ·
                      refine ⟨1147165589767850818913081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059108239380935517101549 1147165589767850818913081)
                      ·
                        rfl

theorem cell23_2234097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_2234097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234097 prefixEnd_2234097 := by exact prefixLift 2234097
  have htrace : WordTrace (prefixWord ++ tailWord_2234097) baseStart_2234097 baseEnd_2234097 := by
    simpa [prefixWord, tailWord_2234097, baseEnd_2234097] using wordTrace_append hprefix tailTrace_2234097
  have hstable : (prefixWord ++ tailWord_2234097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234097).length < 2 ^ (prefixWord ++ tailWord_2234097).sum := by decide
  have hdescent : baseEnd_2234097 < baseStart_2234097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234103 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_2234103 : Nat := 118140960795 + 2234103 * 2 ^ 59
def prefixEnd_2234103 : Nat := 4983230072969 + 3 ^ 40 * 2234103 * 2
def baseEnd_2234103 : Nat := 1147168670651777795438053

theorem tailTrace_2234103 : CollatzResearch.WordTrace tailWord_2234103 prefixEnd_2234103 1147168670651777795438053 := by
  unfold tailWord_2234103
  simp only [CollatzResearch.WordTrace]
  refine ⟨81484430625233860260410963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54322953750155906840273975 81484430625233860260410963)
  ·
    refine ⟨122226645937850790390616445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81484430625233860260410963 122226645937850790390616445)
    ·
      refine ⟨45834992226694046396481167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122226645937850790390616445 45834992226694046396481167)
      ·
        refine ⟨68752488340041069594721751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45834992226694046396481167 68752488340041069594721751)
        ·
          refine ⟨103128732510061604392082627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68752488340041069594721751 103128732510061604392082627)
          ·
            refine ⟨154693098765092406588123941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103128732510061604392082627 154693098765092406588123941)
            ·
              refine ⟨29004956018454826235273239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154693098765092406588123941 29004956018454826235273239)
              ·
                refine ⟨43507434027682239352909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29004956018454826235273239 43507434027682239352909859)
                ·
                  refine ⟨65261151041523359029364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43507434027682239352909859 65261151041523359029364789)
                  ·
                    refine ⟨6118232910142814909002949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65261151041523359029364789 6118232910142814909002949)
                    ·
                      refine ⟨1147168670651777795438053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6118232910142814909002949 1147168670651777795438053)
                      ·
                        rfl

theorem cell23_2234103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_2234103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234103 prefixEnd_2234103 := by exact prefixLift 2234103
  have htrace : WordTrace (prefixWord ++ tailWord_2234103) baseStart_2234103 baseEnd_2234103 := by
    simpa [prefixWord, tailWord_2234103, baseEnd_2234103] using wordTrace_append hprefix tailTrace_2234103
  have hstable : (prefixWord ++ tailWord_2234103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234103).length < 2 ^ (prefixWord ++ tailWord_2234103).sum := by decide
  have hdescent : baseEnd_2234103 < baseStart_2234103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234140 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2234140 : Nat := 118140960795 + 2234140 * 2 ^ 59
def prefixEnd_2234140 : Nat := 4983230072969 + 3 ^ 40 * 2234140 * 2
def baseEnd_2234140 : Nat := 1147187669435994150675383

theorem tailTrace_2234140 : CollatzResearch.WordTrace tailWord_2234140 prefixEnd_2234140 1147187669435994150675383 := by
  unfold tailWord_2234140
  simp only [CollatzResearch.WordTrace]
  refine ⟨40742890063049907789753937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54323853417399877053005249 40742890063049907789753937)
  ·
    refine ⟨30557167547287430842315453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40742890063049907789753937 30557167547287430842315453)
    ·
      refine ⟨11458937830232786565868295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30557167547287430842315453 11458937830232786565868295)
      ·
        refine ⟨17188406745349179848802443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11458937830232786565868295 17188406745349179848802443)
        ·
          refine ⟨25782610118023769773203665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17188406745349179848802443 25782610118023769773203665)
          ·
            refine ⟨19336957588517827329902749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25782610118023769773203665 19336957588517827329902749)
            ·
              refine ⟨7251359095694185248713531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19336957588517827329902749 7251359095694185248713531)
              ·
                refine ⟨10877038643541277873070297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7251359095694185248713531 10877038643541277873070297)
                ·
                  refine ⟨8157778982655958404802723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877038643541277873070297 8157778982655958404802723)
                  ·
                    refine ⟨12236668473983937607204085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8157778982655958404802723 12236668473983937607204085)
                    ·
                      refine ⟨1147187669435994150675383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12236668473983937607204085 1147187669435994150675383)
                      ·
                        rfl

theorem cell23_2234140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2234140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234140 prefixEnd_2234140 := by exact prefixLift 2234140
  have htrace : WordTrace (prefixWord ++ tailWord_2234140) baseStart_2234140 baseEnd_2234140 := by
    simpa [prefixWord, tailWord_2234140, baseEnd_2234140] using wordTrace_append hprefix tailTrace_2234140
  have hstable : (prefixWord ++ tailWord_2234140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234140).length < 2 ^ (prefixWord ++ tailWord_2234140).sum := by decide
  have hdescent : baseEnd_2234140 < baseStart_2234140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234211 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 5]
def baseStart_2234211 : Nat := 118140960795 + 2234211 * 2 ^ 59
def prefixEnd_2234211 : Nat := 4983230072969 + 3 ^ 40 * 2234211 * 2
def baseEnd_2234211 : Nat := 127469347395829263654173

theorem tailTrace_2234211 : CollatzResearch.WordTrace tailWord_2234211 prefixEnd_2234211 127469347395829263654173 := by
  unfold tailWord_2234211
  simp only [CollatzResearch.WordTrace]
  refine ⟨81488369708842594705342487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54325579805895063136894991 81488369708842594705342487)
  ·
    refine ⟨122232554563263892058013731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81488369708842594705342487 122232554563263892058013731)
    ·
      refine ⟨183348831844895838087020597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122232554563263892058013731 183348831844895838087020597)
      ·
        refine ⟨17188952985458984820658181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183348831844895838087020597 17188952985458984820658181)
        ·
          refine ⟨3222928684773559653873409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17188952985458984820658181 3222928684773559653873409)
          ·
            refine ⟨2417196513580169740405057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222928684773559653873409 2417196513580169740405057)
            ·
              refine ⟨1812897385185127305303793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417196513580169740405057 1812897385185127305303793)
              ·
                refine ⟨1359673038888845478977845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812897385185127305303793 1359673038888845478977845)
                ·
                  refine ⟨127469347395829263654173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359673038888845478977845 127469347395829263654173)
                  ·
                    rfl

theorem cell23_2234211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 5].length) (baseStart_2234211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234211 prefixEnd_2234211 := by exact prefixLift 2234211
  have htrace : WordTrace (prefixWord ++ tailWord_2234211) baseStart_2234211 baseEnd_2234211 := by
    simpa [prefixWord, tailWord_2234211, baseEnd_2234211] using wordTrace_append hprefix tailTrace_2234211
  have hstable : (prefixWord ++ tailWord_2234211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234211).length < 2 ^ (prefixWord ++ tailWord_2234211).sum := by decide
  have hdescent : baseEnd_2234211 < baseStart_2234211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234241 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2234241 : Nat := 118140960795 + 2234241 * 2 ^ 59
def prefixEnd_2234241 : Nat := 4983230072969 + 3 ^ 40 * 2234241 * 2
def baseEnd_2234241 : Nat := 382413176994032751837473

theorem tailTrace_2234241 : CollatzResearch.WordTrace tailWord_2234241 prefixEnd_2234241 382413176994032751837473 := by
  unfold tailWord_2234241
  simp only [CollatzResearch.WordTrace]
  refine ⟨81489463898733909828934577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54326309265822606552623051 81489463898733909828934577)
  ·
    refine ⟨61117097924050432371700933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81489463898733909828934577 61117097924050432371700933)
    ·
      refine ⟨11459455860759456069693925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61117097924050432371700933 11459455860759456069693925)
      ·
        refine ⟨2148647973892398013067611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11459455860759456069693925 2148647973892398013067611)
        ·
          refine ⟨3222971960838597019601417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148647973892398013067611 3222971960838597019601417)
          ·
            refine ⟨2417228970628947764701063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222971960838597019601417 2417228970628947764701063)
            ·
              refine ⟨3625843455943421647051595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417228970628947764701063 3625843455943421647051595)
              ·
                refine ⟨5438765183915132470577393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625843455943421647051595 5438765183915132470577393)
                ·
                  refine ⟨4079073887936349352933045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5438765183915132470577393 4079073887936349352933045)
                  ·
                    refine ⟨382413176994032751837473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4079073887936349352933045 382413176994032751837473)
                    ·
                      rfl

theorem cell23_2234241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2234241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234241 prefixEnd_2234241 := by exact prefixLift 2234241
  have htrace : WordTrace (prefixWord ++ tailWord_2234241) baseStart_2234241 baseEnd_2234241 := by
    simpa [prefixWord, tailWord_2234241, baseEnd_2234241] using wordTrace_append hprefix tailTrace_2234241
  have hstable : (prefixWord ++ tailWord_2234241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234241).length < 2 ^ (prefixWord ++ tailWord_2234241).sum := by decide
  have hdescent : baseEnd_2234241 < baseStart_2234241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234287 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 5, 2]
def baseStart_2234287 : Nat := 118140960795 + 2234287 * 2 ^ 59
def prefixEnd_2234287 : Nat := 4983230072969 + 3 ^ 40 * 2234287 * 2
def baseEnd_2234287 : Nat := 1147263151092205075537207

theorem tailTrace_2234287 : CollatzResearch.WordTrace tailWord_2234287 prefixEnd_2234287 1147263151092205075537207 := by
  unfold tailWord_2234287
  simp only [CollatzResearch.WordTrace]
  refine ⟨81491141656567259685109115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54327427771044839790072743 81491141656567259685109115)
  ·
    refine ⟨122236712484850889527663673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81491141656567259685109115 122236712484850889527663673)
    ·
      refine ⟨91677534363638167145747755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122236712484850889527663673 91677534363638167145747755)
      ·
        refine ⟨137516301545457250718621633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91677534363638167145747755 137516301545457250718621633)
        ·
          refine ⟨103137226159092938038966225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137516301545457250718621633 103137226159092938038966225)
          ·
            refine ⟨77352919619319703529224669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103137226159092938038966225 77352919619319703529224669)
            ·
              refine ⟨29007344857244888823459251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77352919619319703529224669 29007344857244888823459251)
              ·
                refine ⟨43511017285867333235188877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29007344857244888823459251 43511017285867333235188877)
                ·
                  refine ⟨16316631482200249963195829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43511017285867333235188877 16316631482200249963195829)
                  ·
                    refine ⟨1529684201456273434049609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16316631482200249963195829 1529684201456273434049609)
                    ·
                      refine ⟨1147263151092205075537207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529684201456273434049609 1147263151092205075537207)
                      ·
                        rfl

theorem cell23_2234287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5, 2].length) (baseStart_2234287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234287 prefixEnd_2234287 := by exact prefixLift 2234287
  have htrace : WordTrace (prefixWord ++ tailWord_2234287) baseStart_2234287 baseEnd_2234287 := by
    simpa [prefixWord, tailWord_2234287, baseEnd_2234287] using wordTrace_append hprefix tailTrace_2234287
  have hstable : (prefixWord ++ tailWord_2234287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234287).length < 2 ^ (prefixWord ++ tailWord_2234287).sum := by decide
  have hdescent : baseEnd_2234287 < baseStart_2234287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234290 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2234290 : Nat := 118140960795 + 2234290 * 2 ^ 59
def prefixEnd_2234290 : Nat := 4983230072969 + 3 ^ 40 * 2234290 * 2
def baseEnd_2234290 : Nat := 1147264691534168563799693

theorem tailTrace_2234290 : CollatzResearch.WordTrace tailWord_2234290 prefixEnd_2234290 1147264691534168563799693 := by
  unfold tailWord_2234290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20372812768889097799367081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54327500717037594131645549 20372812768889097799367081)
  ·
    refine ⟨15279609576666823349525311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20372812768889097799367081 15279609576666823349525311)
    ·
      refine ⟨22919414365000235024287967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15279609576666823349525311 22919414365000235024287967)
      ·
        refine ⟨34379121547500352536431951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22919414365000235024287967 34379121547500352536431951)
        ·
          refine ⟨51568682321250528804647927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34379121547500352536431951 51568682321250528804647927)
          ·
            refine ⟨77353023481875793206971891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51568682321250528804647927 77353023481875793206971891)
            ·
              refine ⟨116029535222813689810457837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77353023481875793206971891 116029535222813689810457837)
              ·
                refine ⟨43511075708555133678921689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116029535222813689810457837 43511075708555133678921689)
                ·
                  refine ⟨32633306781416350259191267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43511075708555133678921689 32633306781416350259191267)
                  ·
                    refine ⟨48949960172124525388786901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32633306781416350259191267 48949960172124525388786901)
                    ·
                      refine ⟨1147264691534168563799693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48949960172124525388786901 1147264691534168563799693)
                      ·
                        rfl

theorem cell23_2234290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2234290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234290 prefixEnd_2234290 := by exact prefixLift 2234290
  have htrace : WordTrace (prefixWord ++ tailWord_2234290) baseStart_2234290 baseEnd_2234290 := by
    simpa [prefixWord, tailWord_2234290, baseEnd_2234290] using wordTrace_append hprefix tailTrace_2234290
  have hstable : (prefixWord ++ tailWord_2234290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234290).length < 2 ^ (prefixWord ++ tailWord_2234290).sum := by decide
  have hdescent : baseEnd_2234290 < baseStart_2234290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234304 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2]
def baseStart_2234304 : Nat := 118140960795 + 2234304 * 2 ^ 59
def prefixEnd_2234304 : Nat := 4983230072969 + 3 ^ 40 * 2234304 * 2
def baseEnd_2234304 : Nat := 1147271880263331509024629

theorem tailTrace_2234304 : CollatzResearch.WordTrace tailWord_2234304 prefixEnd_2234304 1147271880263331509024629 := by
  unfold tailWord_2234304
  simp only [CollatzResearch.WordTrace]
  refine ⟨40745880848752835794238983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54327841131670447725651977 40745880848752835794238983)
  ·
    refine ⟨61118821273129253691358475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40745880848752835794238983 61118821273129253691358475)
    ·
      refine ⟨91678231909693880537037713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61118821273129253691358475 91678231909693880537037713)
      ·
        refine ⟨68758673932270410402778285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91678231909693880537037713 68758673932270410402778285)
        ·
          refine ⟨25784502724601403901041857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68758673932270410402778285 25784502724601403901041857)
          ·
            refine ⟨19338377043451052925781393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25784502724601403901041857 19338377043451052925781393)
            ·
              refine ⟨14503782782588289694336045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19338377043451052925781393 14503782782588289694336045)
              ·
                refine ⟨5438918543470608635376017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14503782782588289694336045 5438918543470608635376017)
                ·
                  refine ⟨4079188907602956476532013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5438918543470608635376017 4079188907602956476532013)
                  ·
                    refine ⟨1529695840351108678699505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4079188907602956476532013 1529695840351108678699505)
                    ·
                      refine ⟨1147271880263331509024629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529695840351108678699505 1147271880263331509024629)
                      ·
                        rfl

theorem cell23_2234304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_2234304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234304 prefixEnd_2234304 := by exact prefixLift 2234304
  have htrace : WordTrace (prefixWord ++ tailWord_2234304) baseStart_2234304 baseEnd_2234304 := by
    simpa [prefixWord, tailWord_2234304, baseEnd_2234304] using wordTrace_append hprefix tailTrace_2234304
  have hstable : (prefixWord ++ tailWord_2234304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234304).length < 2 ^ (prefixWord ++ tailWord_2234304).sum := by decide
  have hdescent : baseEnd_2234304 < baseStart_2234304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234327 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 4, 4]
def baseStart_2234327 : Nat := 118140960795 + 2234327 * 2 ^ 59
def prefixEnd_2234327 : Nat := 4983230072969 + 3 ^ 40 * 2234327 * 2
def baseEnd_2234327 : Nat := 382427896772794973012341

theorem tailTrace_2234327 : CollatzResearch.WordTrace tailWord_2234327 prefixEnd_2234327 382427896772794973012341 := by
  unfold tailWord_2234327
  simp only [CollatzResearch.WordTrace]
  refine ⟨81492600576422346516565235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54328400384281564344376823 81492600576422346516565235)
  ·
    refine ⟨122238900864633519774847853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81492600576422346516565235 122238900864633519774847853)
    ·
      refine ⟨45839587824237569915567945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122238900864633519774847853 45839587824237569915567945)
      ·
        refine ⟨34379690868178177436675959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45839587824237569915567945 34379690868178177436675959)
        ·
          refine ⟨51569536302267266155013939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34379690868178177436675959 51569536302267266155013939)
          ·
            refine ⟨77354304453400899232520909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51569536302267266155013939 77354304453400899232520909)
            ·
              refine ⟨29007864170025337212195341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77354304453400899232520909 29007864170025337212195341)
              ·
                refine ⟨10877949063759501454573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29007864170025337212195341 10877949063759501454573253)
                ·
                  refine ⟨2039615449454906522732485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10877949063759501454573253 2039615449454906522732485)
                  ·
                    refine ⟨382427896772794973012341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2039615449454906522732485 382427896772794973012341)
                    ·
                      rfl

theorem cell23_2234327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_2234327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234327 prefixEnd_2234327 := by exact prefixLift 2234327
  have htrace : WordTrace (prefixWord ++ tailWord_2234327) baseStart_2234327 baseEnd_2234327 := by
    simpa [prefixWord, tailWord_2234327, baseEnd_2234327] using wordTrace_append hprefix tailTrace_2234327
  have hstable : (prefixWord ++ tailWord_2234327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234327).length < 2 ^ (prefixWord ++ tailWord_2234327).sum := by decide
  have hdescent : baseEnd_2234327 < baseStart_2234327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234328 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_2234328 : Nat := 118140960795 + 2234328 * 2 ^ 59
def prefixEnd_2234328 : Nat := 4983230072969 + 3 ^ 40 * 2234328 * 2
def baseEnd_2234328 : Nat := 1147284203799039415124519

theorem tailTrace_2234328 : CollatzResearch.WordTrace tailWord_2234328 prefixEnd_2234328 1147284203799039415124519 := by
  unfold tailWord_2234328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40746318524709361843675819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54328424699612482458234425 40746318524709361843675819)
  ·
    refine ⟨61119477787064042765513729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40746318524709361843675819 61119477787064042765513729)
    ·
      refine ⟨45839608340298032074135297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61119477787064042765513729 45839608340298032074135297)
      ·
        refine ⟨34379706255223524055601473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45839608340298032074135297 34379706255223524055601473)
        ·
          refine ⟨25784779691417643041701105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34379706255223524055601473 25784779691417643041701105)
          ·
            refine ⟨19338584768563232281275829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25784779691417643041701105 19338584768563232281275829)
            ·
              refine ⟨1812992322052803026369609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19338584768563232281275829 1812992322052803026369609)
              ·
                refine ⟨1359744241539602269777207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812992322052803026369609 1359744241539602269777207)
                ·
                  refine ⟨2039616362309403404665811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359744241539602269777207 2039616362309403404665811)
                  ·
                    refine ⟨3059424543464105106998717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039616362309403404665811 3059424543464105106998717)
                    ·
                      refine ⟨1147284203799039415124519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059424543464105106998717 1147284203799039415124519)
                      ·
                        rfl

theorem cell23_2234328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_2234328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234328 prefixEnd_2234328 := by exact prefixLift 2234328
  have htrace : WordTrace (prefixWord ++ tailWord_2234328) baseStart_2234328 baseEnd_2234328 := by
    simpa [prefixWord, tailWord_2234328, baseEnd_2234328] using wordTrace_append hprefix tailTrace_2234328
  have hstable : (prefixWord ++ tailWord_2234328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234328).length < 2 ^ (prefixWord ++ tailWord_2234328).sum := by decide
  have hdescent : baseEnd_2234328 < baseStart_2234328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234337 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_2234337 : Nat := 118140960795 + 2234337 * 2 ^ 59
def prefixEnd_2234337 : Nat := 4983230072969 + 3 ^ 40 * 2234337 * 2
def baseEnd_2234337 : Nat := 1147288825124929879911977

theorem tailTrace_2234337 : CollatzResearch.WordTrace tailWord_2234337 prefixEnd_2234337 1147288825124929879911977 := by
  unfold tailWord_2234337
  simp only [CollatzResearch.WordTrace]
  refine ⟨81492965306386118224429265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54328643537590745482952843 81492965306386118224429265)
  ·
    refine ⟨61119723979789588668321949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81492965306386118224429265 61119723979789588668321949)
    ·
      refine ⟨22919896492421095750620731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61119723979789588668321949 22919896492421095750620731)
      ·
        refine ⟨34379844738631643625931097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22919896492421095750620731 34379844738631643625931097)
        ·
          refine ⟨25784883553973732719448323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34379844738631643625931097 25784883553973732719448323)
          ·
            refine ⟨38677325330960599079172485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25784883553973732719448323 38677325330960599079172485)
            ·
              refine ⟨7251998499555112327344841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38677325330960599079172485 7251998499555112327344841)
              ·
                refine ⟨5438998874666334245508631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7251998499555112327344841 5438998874666334245508631)
                ·
                  refine ⟨8158498311999501368262947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438998874666334245508631 8158498311999501368262947)
                  ·
                    refine ⟨12237747467999252052394421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8158498311999501368262947 12237747467999252052394421)
                    ·
                      refine ⟨1147288825124929879911977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12237747467999252052394421 1147288825124929879911977)
                      ·
                        rfl

theorem cell23_2234337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_2234337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234337 prefixEnd_2234337 := by exact prefixLift 2234337
  have htrace : WordTrace (prefixWord ++ tailWord_2234337) baseStart_2234337 baseEnd_2234337 := by
    simpa [prefixWord, tailWord_2234337, baseEnd_2234337] using wordTrace_append hprefix tailTrace_2234337
  have hstable : (prefixWord ++ tailWord_2234337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234337).length < 2 ^ (prefixWord ++ tailWord_2234337).sum := by decide
  have hdescent : baseEnd_2234337 < baseStart_2234337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234391 : List Nat := [1, 1, 3, 5, 3, 1, 1, 8]
def baseStart_2234391 : Nat := 118140960795 + 2234391 * 2 ^ 59
def prefixEnd_2234391 : Nat := 4983230072969 + 3 ^ 40 * 2234391 * 2
def baseEnd_2234391 : Nat := 42493205669639728468027

theorem tailTrace_2234391 : CollatzResearch.WordTrace tailWord_2234391 prefixEnd_2234391 42493205669639728468027 := by
  unfold tailWord_2234391
  simp only [CollatzResearch.WordTrace]
  refine ⟨81494934848190485446895027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54329956565460323631263351 81494934848190485446895027)
  ·
    refine ⟨122242402272285728170342541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81494934848190485446895027 122242402272285728170342541)
    ·
      refine ⟨45840900852107148063878453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122242402272285728170342541 45840900852107148063878453)
      ·
        refine ⟨4297584454885045130988605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45840900852107148063878453 4297584454885045130988605)
        ·
          refine ⟨1611594170581891924120727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4297584454885045130988605 1611594170581891924120727)
          ·
            refine ⟨2417391255872837886181091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611594170581891924120727 2417391255872837886181091)
            ·
              refine ⟨3626086883809256829271637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417391255872837886181091 3626086883809256829271637)
              ·
                refine ⟨42493205669639728468027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3626086883809256829271637 42493205669639728468027)
                ·
                  rfl

theorem cell23_2234391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 8].length) (baseStart_2234391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234391 prefixEnd_2234391 := by exact prefixLift 2234391
  have htrace : WordTrace (prefixWord ++ tailWord_2234391) baseStart_2234391 baseEnd_2234391 := by
    simpa [prefixWord, tailWord_2234391, baseEnd_2234391] using wordTrace_append hprefix tailTrace_2234391
  have hstable : (prefixWord ++ tailWord_2234391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234391).length < 2 ^ (prefixWord ++ tailWord_2234391).sum := by decide
  have hdescent : baseEnd_2234391 < baseStart_2234391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234401 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2234401 : Nat := 118140960795 + 2234401 * 2 ^ 59
def prefixEnd_2234401 : Nat := 4983230072969 + 3 ^ 40 * 2234401 * 2
def baseEnd_2234401 : Nat := 1147321687886817629511683

theorem tailTrace_2234401 : CollatzResearch.WordTrace tailWord_2234401 prefixEnd_2234401 1147321687886817629511683 := by
  unfold tailWord_2234401
  simp only [CollatzResearch.WordTrace]
  refine ⟨81495299578154257154759057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54330199718769504769839371 81495299578154257154759057)
  ·
    refine ⟨61121474683615692866069293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81495299578154257154759057 61121474683615692866069293)
    ·
      refine ⟨22920553006355884824775985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61121474683615692866069293 22920553006355884824775985)
      ·
        refine ⟨17190414754766913618581989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22920553006355884824775985 17190414754766913618581989)
        ·
          refine ⟨3223202766518796303484123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17190414754766913618581989 3223202766518796303484123)
          ·
            refine ⟨4834804149778194455226185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223202766518796303484123 4834804149778194455226185)
            ·
              refine ⟨3626103112333645841419639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4834804149778194455226185 3626103112333645841419639)
              ·
                refine ⟨5439154668500468762129459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626103112333645841419639 5439154668500468762129459)
                ·
                  refine ⟨8158732002750703143194189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439154668500468762129459 8158732002750703143194189)
                  ·
                    refine ⟨3059524501031513678697821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8158732002750703143194189 3059524501031513678697821)
                    ·
                      refine ⟨1147321687886817629511683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059524501031513678697821 1147321687886817629511683)
                      ·
                        rfl

theorem cell23_2234401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2234401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234401 prefixEnd_2234401 := by exact prefixLift 2234401
  have htrace : WordTrace (prefixWord ++ tailWord_2234401) baseStart_2234401 baseEnd_2234401 := by
    simpa [prefixWord, tailWord_2234401, baseEnd_2234401] using wordTrace_append hprefix tailTrace_2234401
  have hstable : (prefixWord ++ tailWord_2234401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234401).length < 2 ^ (prefixWord ++ tailWord_2234401).sum := by decide
  have hdescent : baseEnd_2234401 < baseStart_2234401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3]
def baseStart_2234427 : Nat := 118140960795 + 2234427 * 2 ^ 59
def prefixEnd_2234427 : Nat := 4983230072969 + 3 ^ 40 * 2234427 * 2
def baseEnd_2234427 : Nat := 1147335038383834527786563

theorem tailTrace_2234427 : CollatzResearch.WordTrace tailWord_2234427 prefixEnd_2234427 1147335038383834527786563 := by
  unfold tailWord_2234427
  simp only [CollatzResearch.WordTrace]
  refine ⟨81496247876060063595205535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54330831917373375730137023 81496247876060063595205535)
  ·
    refine ⟨122244371814090095392808303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81496247876060063595205535 122244371814090095392808303)
    ·
      refine ⟨183366557721135143089212455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122244371814090095392808303 183366557721135143089212455)
      ·
        refine ⟨275049836581702714633818683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183366557721135143089212455 275049836581702714633818683)
        ·
          refine ⟨412574754872554071950728025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275049836581702714633818683 412574754872554071950728025)
          ·
            refine ⟨309431066154415553963046019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412574754872554071950728025 309431066154415553963046019)
            ·
              refine ⟨464146599231623330944569029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309431066154415553963046019 464146599231623330944569029)
              ·
                refine ⟨87027487355929374552106693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464146599231623330944569029 87027487355929374552106693)
                ·
                  refine ⟨16317653879236757728520005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87027487355929374552106693 16317653879236757728520005)
                  ·
                    refine ⟨3059560102356892074097501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16317653879236757728520005 3059560102356892074097501)
                    ·
                      refine ⟨1147335038383834527786563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059560102356892074097501 1147335038383834527786563)
                      ·
                        rfl

theorem cell23_2234427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].length) (baseStart_2234427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234427 prefixEnd_2234427 := by exact prefixLift 2234427
  have htrace : WordTrace (prefixWord ++ tailWord_2234427) baseStart_2234427 baseEnd_2234427 := by
    simpa [prefixWord, tailWord_2234427, baseEnd_2234427] using wordTrace_append hprefix tailTrace_2234427
  have hstable : (prefixWord ++ tailWord_2234427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234427).length < 2 ^ (prefixWord ++ tailWord_2234427).sum := by decide
  have hdescent : baseEnd_2234427 < baseStart_2234427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234441 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 4, 2, 2]
def baseStart_2234441 : Nat := 118140960795 + 2234441 * 2 ^ 59
def prefixEnd_2234441 : Nat := 4983230072969 + 3 ^ 40 * 2234441 * 2
def baseEnd_2234441 : Nat := 1147342227112997473011499

theorem tailTrace_2234441 : CollatzResearch.WordTrace tailWord_2234441 prefixEnd_2234441 1147342227112997473011499 := by
  unfold tailWord_2234441
  simp only [CollatzResearch.WordTrace]
  refine ⟨81496758498009343986215177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54331172332006229324143451 81496758498009343986215177)
  ·
    refine ⟨61122568873507007989661383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81496758498009343986215177 61122568873507007989661383)
    ·
      refine ⟨91683853310260511984492075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61122568873507007989661383 91683853310260511984492075)
      ·
        refine ⟨137525779965390767976738113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91683853310260511984492075 137525779965390767976738113)
        ·
          refine ⟨103144334974043075982553585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137525779965390767976738113 103144334974043075982553585)
          ·
            refine ⟨77358251230532306986915189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103144334974043075982553585 77358251230532306986915189)
            ·
              refine ⟨7252336052862403780023299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77358251230532306986915189 7252336052862403780023299)
              ·
                refine ⟨10878504079293605670034949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252336052862403780023299 10878504079293605670034949)
                ·
                  refine ⟨2039719514867551063131553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10878504079293605670034949 2039719514867551063131553)
                  ·
                    refine ⟨1529789636150663297348665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2039719514867551063131553 1529789636150663297348665)
                    ·
                      refine ⟨1147342227112997473011499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1529789636150663297348665 1147342227112997473011499)
                      ·
                        rfl

theorem cell23_2234441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2, 2].length) (baseStart_2234441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234441 prefixEnd_2234441 := by exact prefixLift 2234441
  have htrace : WordTrace (prefixWord ++ tailWord_2234441) baseStart_2234441 baseEnd_2234441 := by
    simpa [prefixWord, tailWord_2234441, baseEnd_2234441] using wordTrace_append hprefix tailTrace_2234441
  have hstable : (prefixWord ++ tailWord_2234441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234441).length < 2 ^ (prefixWord ++ tailWord_2234441).sum := by decide
  have hdescent : baseEnd_2234441 < baseStart_2234441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234504 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2234504 : Nat := 118140960795 + 2234504 * 2 ^ 59
def prefixEnd_2234504 : Nat := 4983230072969 + 3 ^ 40 * 2234504 * 2
def baseEnd_2234504 : Nat := 1147374576394230726523709

theorem tailTrace_2234504 : CollatzResearch.WordTrace tailWord_2234504 prefixEnd_2234504 1147374576394230726523709 := by
  unfold tailWord_2234504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40749528148390552872879283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54332704197854070497172377 40749528148390552872879283)
  ·
    refine ⟨61124292222585829309318925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40749528148390552872879283 61124292222585829309318925)
    ·
      refine ⟨22921609583469685990994597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61124292222585829309318925 22921609583469685990994597)
      ·
        refine ⟨4297801796900566123311487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22921609583469685990994597 4297801796900566123311487)
        ·
          refine ⟨6446702695350849184967231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4297801796900566123311487 6446702695350849184967231)
          ·
            refine ⟨9670054043026273777450847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6446702695350849184967231 9670054043026273777450847)
            ·
              refine ⟨14505081064539410666176271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9670054043026273777450847 14505081064539410666176271)
              ·
                refine ⟨21757621596809115999264407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14505081064539410666176271 21757621596809115999264407)
                ·
                  refine ⟨32636432395213673998896611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21757621596809115999264407 32636432395213673998896611)
                  ·
                    refine ⟨48954648592820510998344917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32636432395213673998896611 48954648592820510998344917)
                    ·
                      refine ⟨1147374576394230726523709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48954648592820510998344917 1147374576394230726523709)
                      ·
                        rfl

theorem cell23_2234504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2234504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234504 prefixEnd_2234504 := by exact prefixLift 2234504
  have htrace : WordTrace (prefixWord ++ tailWord_2234504) baseStart_2234504 baseEnd_2234504 := by
    simpa [prefixWord, tailWord_2234504, baseEnd_2234504] using wordTrace_append hprefix tailTrace_2234504
  have hstable : (prefixWord ++ tailWord_2234504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234504).length < 2 ^ (prefixWord ++ tailWord_2234504).sum := by decide
  have hdescent : baseEnd_2234504 < baseStart_2234504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234551 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_2234551 : Nat := 118140960795 + 2234551 * 2 ^ 59
def prefixEnd_2234551 : Nat := 4983230072969 + 3 ^ 40 * 2234551 * 2
def baseEnd_2234551 : Nat := 1147398709984992042635993

theorem tailTrace_2234551 : CollatzResearch.WordTrace tailWord_2234551 prefixEnd_2234551 1147398709984992042635993 := by
  unfold tailWord_2234551
  simp only [CollatzResearch.WordTrace]
  refine ⟨81500770527610832772719507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54333847018407221848479671 81500770527610832772719507)
  ·
    refine ⟨122251155791416249159079261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81500770527610832772719507 122251155791416249159079261)
    ·
      refine ⟨45844183421781093434654723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122251155791416249159079261 45844183421781093434654723)
      ·
        refine ⟨68766275132671640151982085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45844183421781093434654723 68766275132671640151982085)
        ·
          refine ⟨12893676587375932528496641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68766275132671640151982085 12893676587375932528496641)
          ·
            refine ⟨9670257440531949396372481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12893676587375932528496641 9670257440531949396372481)
            ·
              refine ⟨7252693080398962047279361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9670257440531949396372481 7252693080398962047279361)
              ·
                refine ⟨5439519810299221535459521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7252693080398962047279361 5439519810299221535459521)
                ·
                  refine ⟨4079639857724416151594641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5439519810299221535459521 4079639857724416151594641)
                  ·
                    refine ⟨3059729893293312113695981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079639857724416151594641 3059729893293312113695981)
                    ·
                      refine ⟨1147398709984992042635993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059729893293312113695981 1147398709984992042635993)
                      ·
                        rfl

theorem cell23_2234551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_2234551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234551 prefixEnd_2234551 := by exact prefixLift 2234551
  have htrace : WordTrace (prefixWord ++ tailWord_2234551) baseStart_2234551 baseEnd_2234551 := by
    simpa [prefixWord, tailWord_2234551, baseEnd_2234551] using wordTrace_append hprefix tailTrace_2234551
  have hstable : (prefixWord ++ tailWord_2234551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234551).length < 2 ^ (prefixWord ++ tailWord_2234551).sum := by decide
  have hdescent : baseEnd_2234551 < baseStart_2234551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234554 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_2234554 : Nat := 118140960795 + 2234554 * 2 ^ 59
def prefixEnd_2234554 : Nat := 4983230072969 + 3 ^ 40 * 2234554 * 2
def baseEnd_2234554 : Nat := 127488916714106170099831

theorem tailTrace_2234554 : CollatzResearch.WordTrace tailWord_2234554 prefixEnd_2234554 127488916714106170099831 := by
  unfold tailWord_2234554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20375219986649991071269679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54333919964399976190052477 20375219986649991071269679)
  ·
    refine ⟨30562829979974986606904519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20375219986649991071269679 30562829979974986606904519)
    ·
      refine ⟨45844244969962479910356779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30562829979974986606904519 45844244969962479910356779)
      ·
        refine ⟨68766367454943719865535169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45844244969962479910356779 68766367454943719865535169)
        ·
          refine ⟨51574775591207789899151377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68766367454943719865535169 51574775591207789899151377)
          ·
            refine ⟨38681081693405842424363533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51574775591207789899151377 38681081693405842424363533)
            ·
              refine ⟨14505405635027190909136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38681081693405842424363533 14505405635027190909136325)
              ·
                refine ⟨2719763556567598295463061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14505405635027190909136325 2719763556567598295463061)
                ·
                  refine ⟨127488916714106170099831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2719763556567598295463061 127488916714106170099831)
                  ·
                    rfl

theorem cell23_2234554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_2234554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234554 prefixEnd_2234554 := by exact prefixLift 2234554
  have htrace : WordTrace (prefixWord ++ tailWord_2234554) baseStart_2234554 baseEnd_2234554 := by
    simpa [prefixWord, tailWord_2234554, baseEnd_2234554] using wordTrace_append hprefix tailTrace_2234554
  have hstable : (prefixWord ++ tailWord_2234554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234554).length < 2 ^ (prefixWord ++ tailWord_2234554).sum := by decide
  have hdescent : baseEnd_2234554 < baseStart_2234554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234605 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2234605 : Nat := 118140960795 + 2234605 * 2 ^ 59
def prefixEnd_2234605 : Nat := 4983230072969 + 3 ^ 40 * 2234605 * 2
def baseEnd_2234605 : Nat := 127491826437814981262305

theorem tailTrace_2234605 : CollatzResearch.WordTrace tailWord_2234605 prefixEnd_2234605 127491826437814981262305 := by
  unfold tailWord_2234605
  simp only [CollatzResearch.WordTrace]
  refine ⟨81502740069415199995185269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54335160046276799996790179 81502740069415199995185269)
  ·
    refine ⟨7640881881507674999548619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81502740069415199995185269 7640881881507674999548619)
    ·
      refine ⟨11461322822261512499322929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640881881507674999548619 11461322822261512499322929)
      ·
        refine ⟨8595992116696134374492197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11461322822261512499322929 8595992116696134374492197)
        ·
          refine ⟨1611748521880525195217287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8595992116696134374492197 1611748521880525195217287)
          ·
            refine ⟨2417622782820787792825931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611748521880525195217287 2417622782820787792825931)
            ·
              refine ⟨3626434174231181689238897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417622782820787792825931 3626434174231181689238897)
              ·
                refine ⟨2719825630673386266929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626434174231181689238897 2719825630673386266929173)
                ·
                  refine ⟨127491826437814981262305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2719825630673386266929173 127491826437814981262305)
                  ·
                    rfl

theorem cell23_2234605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2234605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234605 prefixEnd_2234605 := by exact prefixLift 2234605
  have htrace : WordTrace (prefixWord ++ tailWord_2234605) baseStart_2234605 baseEnd_2234605 := by
    simpa [prefixWord, tailWord_2234605, baseEnd_2234605] using wordTrace_append hprefix tailTrace_2234605
  have hstable : (prefixWord ++ tailWord_2234605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234605).length < 2 ^ (prefixWord ++ tailWord_2234605).sum := by decide
  have hdescent : baseEnd_2234605 < baseStart_2234605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234624 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2234624 : Nat := 118140960795 + 2234624 * 2 ^ 59
def prefixEnd_2234624 : Nat := 4983230072969 + 3 ^ 40 * 2234624 * 2
def baseEnd_2234624 : Nat := 1147436194072770257023157

theorem tailTrace_2234624 : CollatzResearch.WordTrace tailWord_2234624 prefixEnd_2234624 1147436194072770257023157 := by
  unfold tailWord_2234624
  simp only [CollatzResearch.WordTrace]
  refine ⟨40751716528173183120063463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54335622037564244160084617 40751716528173183120063463)
  ·
    refine ⟨61127574792259774680095195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40751716528173183120063463 61127574792259774680095195)
    ·
      refine ⟨91691362188389662020142793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61127574792259774680095195 91691362188389662020142793)
      ·
        refine ⟨68768521641292246515107095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91691362188389662020142793 68768521641292246515107095)
        ·
          refine ⟨103152782461938369772660643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68768521641292246515107095 103152782461938369772660643)
          ·
            refine ⟨154729173692907554658990965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103152782461938369772660643 154729173692907554658990965)
            ·
              refine ⟨14505860033710083249280403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154729173692907554658990965 14505860033710083249280403)
              ·
                refine ⟨21758790050565124873920605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14505860033710083249280403 21758790050565124873920605)
                ·
                  refine ⟨8159546268961921827720227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21758790050565124873920605 8159546268961921827720227)
                  ·
                    refine ⟨12239319403442882741580341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8159546268961921827720227 12239319403442882741580341)
                    ·
                      refine ⟨1147436194072770257023157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12239319403442882741580341 1147436194072770257023157)
                      ·
                        rfl

theorem cell23_2234624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2234624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234624 prefixEnd_2234624 := by exact prefixLift 2234624
  have htrace : WordTrace (prefixWord ++ tailWord_2234624) baseStart_2234624 baseEnd_2234624 := by
    simpa [prefixWord, tailWord_2234624, baseEnd_2234624] using wordTrace_append hprefix tailTrace_2234624
  have hstable : (prefixWord ++ tailWord_2234624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234624).length < 2 ^ (prefixWord ++ tailWord_2234624).sum := by decide
  have hdescent : baseEnd_2234624 < baseStart_2234624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234638 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2234638 : Nat := 118140960795 + 2234638 * 2 ^ 59
def prefixEnd_2234638 : Nat := 4983230072969 + 3 ^ 40 * 2234638 * 2
def baseEnd_2234638 : Nat := 1147443382801933202248093

theorem tailTrace_2234638 : CollatzResearch.WordTrace tailWord_2234638 prefixEnd_2234638 1147443382801933202248093 := by
  unfold tailWord_2234638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187992959786955828892071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54335962452197097754091045 10187992959786955828892071)
  ·
    refine ⟨15281989439680433743338107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10187992959786955828892071 15281989439680433743338107)
    ·
      refine ⟨22922984159520650615007161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15281989439680433743338107 22922984159520650615007161)
      ·
        refine ⟨17192238119640487961255371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22922984159520650615007161 17192238119640487961255371)
        ·
          refine ⟨25788357179460731941883057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17192238119640487961255371 25788357179460731941883057)
          ·
            refine ⟨19341267884595548956412293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25788357179460731941883057 19341267884595548956412293)
            ·
              refine ⟨3626487728361665429327305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19341267884595548956412293 3626487728361665429327305)
              ·
                refine ⟨2719865796271249071995479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626487728361665429327305 2719865796271249071995479)
                ·
                  refine ⟨4079798694406873607993219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719865796271249071995479 4079798694406873607993219)
                  ·
                    refine ⟨6119698041610310411989829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4079798694406873607993219 6119698041610310411989829)
                    ·
                      refine ⟨1147443382801933202248093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6119698041610310411989829 1147443382801933202248093)
                      ·
                        rfl

theorem cell23_2234638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2234638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234638 prefixEnd_2234638 := by exact prefixLift 2234638
  have htrace : WordTrace (prefixWord ++ tailWord_2234638) baseStart_2234638 baseEnd_2234638 := by
    simpa [prefixWord, tailWord_2234638, baseEnd_2234638] using wordTrace_append hprefix tailTrace_2234638
  have hstable : (prefixWord ++ tailWord_2234638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234638).length < 2 ^ (prefixWord ++ tailWord_2234638).sum := by decide
  have hdescent : baseEnd_2234638 < baseStart_2234638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234658 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2234658 : Nat := 118140960795 + 2234658 * 2 ^ 59
def prefixEnd_2234658 : Nat := 4983230072969 + 3 ^ 40 * 2234658 * 2
def baseEnd_2234658 : Nat := 1147453652415023123998001

theorem tailTrace_2234658 : CollatzResearch.WordTrace tailWord_2234658 prefixEnd_2234658 1147453652415023123998001 := by
  unfold tailWord_2234658
  simp only [CollatzResearch.WordTrace]
  refine ⟨20376168284555797511716157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54336448758815460031243085 20376168284555797511716157)
  ·
    refine ⟨7641063106708424066893559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20376168284555797511716157 7641063106708424066893559)
    ·
      refine ⟨11461594660062636100340339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641063106708424066893559 11461594660062636100340339)
      ·
        refine ⟨17192391990093954150510509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11461594660062636100340339 17192391990093954150510509)
        ·
          refine ⟨6447146996285232806441441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17192391990093954150510509 6447146996285232806441441)
          ·
            refine ⟨4835360247213924604831081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6447146996285232806441441 4835360247213924604831081)
            ·
              refine ⟨3626520185410443453623311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835360247213924604831081 3626520185410443453623311)
              ·
                refine ⟨5439780278115665180434967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626520185410443453623311 5439780278115665180434967)
                ·
                  refine ⟨8159670417173497770652451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439780278115665180434967 8159670417173497770652451)
                  ·
                    refine ⟨12239505625760246655978677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8159670417173497770652451 12239505625760246655978677)
                    ·
                      refine ⟨1147453652415023123998001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12239505625760246655978677 1147453652415023123998001)
                      ·
                        rfl

theorem cell23_2234658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2234658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234658 prefixEnd_2234658 := by exact prefixLift 2234658
  have htrace : WordTrace (prefixWord ++ tailWord_2234658) baseStart_2234658 baseEnd_2234658 := by
    simpa [prefixWord, tailWord_2234658, baseEnd_2234658] using wordTrace_append hprefix tailTrace_2234658
  have hstable : (prefixWord ++ tailWord_2234658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234658).length < 2 ^ (prefixWord ++ tailWord_2234658).sum := by decide
  have hdescent : baseEnd_2234658 < baseStart_2234658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234661 : List Nat := [1, 3, 1, 2, 5, 2, 9]
def baseStart_2234661 : Nat := 118140960795 + 2234661 * 2 ^ 59
def prefixEnd_2234661 : Nat := 4983230072969 + 3 ^ 40 * 2234661 * 2
def baseEnd_2234661 : Nat := 14166113492061563114327

theorem tailTrace_2234661 : CollatzResearch.WordTrace tailWord_2234661 prefixEnd_2234661 14166113492061563114327 := by
  unfold tailWord_2234661
  simp only [CollatzResearch.WordTrace]
  refine ⟨81504782557212321559223837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54336521704808214372815891 81504782557212321559223837)
  ·
    refine ⟨30564293458954620584708939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81504782557212321559223837 30564293458954620584708939)
    ·
      refine ⟨45846440188431930877063409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30564293458954620584708939 45846440188431930877063409)
      ·
        refine ⟨34384830141323948157797557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45846440188431930877063409 34384830141323948157797557)
        ·
          refine ⟨3223577825749120139793521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34384830141323948157797557 3223577825749120139793521)
          ·
            refine ⟨2417683369311840104845141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223577825749120139793521 2417683369311840104845141)
            ·
              refine ⟨14166113492061563114327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2417683369311840104845141 14166113492061563114327)
              ·
                rfl

theorem cell23_2234661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 9].length) (baseStart_2234661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234661 prefixEnd_2234661 := by exact prefixLift 2234661
  have htrace : WordTrace (prefixWord ++ tailWord_2234661) baseStart_2234661 baseEnd_2234661 := by
    simpa [prefixWord, tailWord_2234661, baseEnd_2234661] using wordTrace_append hprefix tailTrace_2234661
  have hstable : (prefixWord ++ tailWord_2234661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234661).length < 2 ^ (prefixWord ++ tailWord_2234661).sum := by decide
  have hdescent : baseEnd_2234661 < baseStart_2234661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234722 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2234722 : Nat := 118140960795 + 2234722 * 2 ^ 59
def prefixEnd_2234722 : Nat := 4983230072969 + 3 ^ 40 * 2234722 * 2
def baseEnd_2234722 : Nat := 1147486515176910873597707

theorem tailTrace_2234722 : CollatzResearch.WordTrace tailWord_2234722 prefixEnd_2234722 1147486515176910873597707 := by
  unfold tailWord_2234722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20376751852497832244298605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54338004939994219318129613 20376751852497832244298605)
  ·
    refine ⟨7641281944686687091611977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20376751852497832244298605 7641281944686687091611977)
    ·
      refine ⟨5730961458515015318708983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7641281944686687091611977 5730961458515015318708983)
      ·
        refine ⟨8596442187772522978063475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730961458515015318708983 8596442187772522978063475)
        ·
          refine ⟨12894663281658784467095213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596442187772522978063475 12894663281658784467095213)
          ·
            refine ⟨4835498730622044175160705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12894663281658784467095213 4835498730622044175160705)
            ·
              refine ⟨3626624047966533131370529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835498730622044175160705 3626624047966533131370529)
              ·
                refine ⟨2719968035974899848527897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626624047966533131370529 2719968035974899848527897)
                ·
                  refine ⟨2039976026981174886395923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2719968035974899848527897 2039976026981174886395923)
                  ·
                    refine ⟨3059964040471762329593885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2039976026981174886395923 3059964040471762329593885)
                    ·
                      refine ⟨1147486515176910873597707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3059964040471762329593885 1147486515176910873597707)
                      ·
                        rfl

theorem cell23_2234722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2234722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234722 prefixEnd_2234722 := by exact prefixLift 2234722
  have htrace : WordTrace (prefixWord ++ tailWord_2234722) baseStart_2234722 baseEnd_2234722 := by
    simpa [prefixWord, tailWord_2234722, baseEnd_2234722] using wordTrace_append hprefix tailTrace_2234722
  have hstable : (prefixWord ++ tailWord_2234722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234722).length < 2 ^ (prefixWord ++ tailWord_2234722).sum := by decide
  have hdescent : baseEnd_2234722 < baseStart_2234722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
