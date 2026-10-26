import V185TrunkScan22Chunk341

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3050975 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 1, 3]
def baseStart_3050975 : Nat := 118140960795 + 3050975 * 2 ^ 59
def prefixEnd_3050975 : Nat := 4983230072969 + 3 ^ 40 * 3050975 * 2
def baseEnd_3050975 : Nat := 1044411093234203853320885

theorem tailTrace_3050975 : CollatzResearch.WordTrace tailWord_3050975 prefixEnd_3050975 1044411093234203853320885 := by
  unfold tailWord_3050975
  simp only [CollatzResearch.WordTrace]
  refine ⟨111278200121846114891002379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74185466747897409927334919 111278200121846114891002379)
  ·
    refine ⟨166917300182769172336503569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111278200121846114891002379 166917300182769172336503569)
    ·
      refine ⟨125187975137076879252377677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166917300182769172336503569 125187975137076879252377677)
      ·
        refine ⟨46945490676403829719641629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125187975137076879252377677 46945490676403829719641629)
        ·
          refine ⟨17604559003651436144865611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46945490676403829719641629 17604559003651436144865611)
          ·
            refine ⟨26406838505477154217298417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17604559003651436144865611 26406838505477154217298417)
            ·
              refine ⟨19805128879107865662973813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26406838505477154217298417 19805128879107865662973813)
              ·
                refine ⟨1856730832416362405903795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19805128879107865662973813 1856730832416362405903795)
                ·
                  refine ⟨2785096248624543608855693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856730832416362405903795 2785096248624543608855693)
                  ·
                    refine ⟨1044411093234203853320885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785096248624543608855693 1044411093234203853320885)
                    ·
                      rfl

theorem cell22_3050975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_3050975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050975 prefixEnd_3050975 := by exact prefixLift 3050975
  have htrace : WordTrace (prefixWord ++ tailWord_3050975) baseStart_3050975 baseEnd_3050975 := by
    simpa [prefixWord, tailWord_3050975, baseEnd_3050975] using wordTrace_append hprefix tailTrace_3050975
  have hstable : (prefixWord ++ tailWord_3050975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050975).length < 2 ^ (prefixWord ++ tailWord_3050975).sum := by decide
  have hdescent : baseEnd_3050975 < baseStart_3050975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050992 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_3050992 : Nat := 118140960795 + 3050992 * 2 ^ 59
def prefixEnd_3050992 : Nat := 4983230072969 + 3 ^ 40 * 3050992 * 2
def baseEnd_3050992 : Nat := 1044416912681621475645833

theorem tailTrace_3050992 : CollatzResearch.WordTrace tailWord_3050992 prefixEnd_3050992 1044416912681621475645833 := by
  unfold tailWord_3050992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55639410081392263397185615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74185880108523017862914153 55639410081392263397185615)
  ·
    refine ⟨83459115122088395095778423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55639410081392263397185615 83459115122088395095778423)
    ·
      refine ⟨125188672683132592643667635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83459115122088395095778423 125188672683132592643667635)
      ·
        refine ⟨187783009024698888965501453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125188672683132592643667635 187783009024698888965501453)
        ·
          refine ⟨70418628384262083362063045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187783009024698888965501453 70418628384262083362063045)
          ·
            refine ⟨13203492822049140630386821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70418628384262083362063045 13203492822049140630386821)
            ·
              refine ⟨2475654904134213868197529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13203492822049140630386821 2475654904134213868197529)
              ·
                refine ⟨1856741178100660401148147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475654904134213868197529 1856741178100660401148147)
                ·
                  refine ⟨2785111767150990601722221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856741178100660401148147 2785111767150990601722221)
                  ·
                    refine ⟨1044416912681621475645833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785111767150990601722221 1044416912681621475645833)
                    ·
                      rfl

theorem cell22_3050992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_3050992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050992 prefixEnd_3050992 := by exact prefixLift 3050992
  have htrace : WordTrace (prefixWord ++ tailWord_3050992) baseStart_3050992 baseEnd_3050992 := by
    simpa [prefixWord, tailWord_3050992, baseEnd_3050992] using wordTrace_append hprefix tailTrace_3050992
  have hstable : (prefixWord ++ tailWord_3050992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050992).length < 2 ^ (prefixWord ++ tailWord_3050992).sum := by decide
  have hdescent : baseEnd_3050992 < baseStart_3050992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051016 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_3051016 : Nat := 118140960795 + 3051016 * 2 ^ 59
def prefixEnd_3051016 : Nat := 4983230072969 + 3 ^ 40 * 3051016 * 2
def baseEnd_3051016 : Nat := 348141709457364471015253

theorem tailTrace_3051016 : CollatzResearch.WordTrace tailWord_3051016 prefixEnd_3051016 348141709457364471015253 := by
  unfold tailWord_3051016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55639847757348789446622451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74186463676465052595496601 55639847757348789446622451)
  ·
    refine ⟨83459771636023184169933677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55639847757348789446622451 83459771636023184169933677)
    ·
      refine ⟨31297414363508694063725129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83459771636023184169933677 31297414363508694063725129)
      ·
        refine ⟨23473060772631520547793847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31297414363508694063725129 23473060772631520547793847)
        ·
          refine ⟨35209591158947280821690771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23473060772631520547793847 35209591158947280821690771)
          ·
            refine ⟨52814386738420921232536157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35209591158947280821690771 52814386738420921232536157)
            ·
              refine ⟨19805395026907845462201059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52814386738420921232536157 19805395026907845462201059)
              ·
                refine ⟨29708092540361768193301589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19805395026907845462201059 29708092540361768193301589)
                ·
                  refine ⟨348141709457364471015253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29708092540361768193301589 348141709457364471015253)
                  ·
                    rfl

theorem cell22_3051016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_3051016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051016 prefixEnd_3051016 := by exact prefixLift 3051016
  have htrace : WordTrace (prefixWord ++ tailWord_3051016) baseStart_3051016 baseEnd_3051016 := by
    simpa [prefixWord, tailWord_3051016, baseEnd_3051016] using wordTrace_append hprefix tailTrace_3051016
  have hstable : (prefixWord ++ tailWord_3051016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051016).length < 2 ^ (prefixWord ++ tailWord_3051016).sum := by decide
  have hdescent : baseEnd_3051016 < baseStart_3051016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051018 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3051018 : Nat := 118140960795 + 3051018 * 2 ^ 59
def prefixEnd_3051018 : Nat := 4983230072969 + 3 ^ 40 * 3051018 * 2
def baseEnd_3051018 : Nat := 1044425813012966074495753

theorem tailTrace_3051018 : CollatzResearch.WordTrace tailWord_3051018 prefixEnd_3051018 1044425813012966074495753 := by
  unfold tailWord_3051018
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819942115172583308704427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74186512307126888823211805 27819942115172583308704427)
  ·
    refine ⟨41729913172758874963056641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27819942115172583308704427 41729913172758874963056641)
    ·
      refine ⟨31297434879569156222292481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41729913172758874963056641 31297434879569156222292481)
      ·
        refine ⟨23473076159676867166719361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31297434879569156222292481 23473076159676867166719361)
        ·
          refine ⟨17604807119757650375039521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23473076159676867166719361 17604807119757650375039521)
          ·
            refine ⟨13203605339818237781279641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17604807119757650375039521 13203605339818237781279641)
            ·
              refine ⟨9902704004863678335959731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203605339818237781279641 9902704004863678335959731)
              ·
                refine ⟨14854056007295517503939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902704004863678335959731 14854056007295517503939597)
                ·
                  refine ⟨5570271002735819063977349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14854056007295517503939597 5570271002735819063977349)
                  ·
                    refine ⟨1044425813012966074495753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570271002735819063977349 1044425813012966074495753)
                    ·
                      rfl

theorem cell22_3051018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3051018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051018 prefixEnd_3051018 := by exact prefixLift 3051018
  have htrace : WordTrace (prefixWord ++ tailWord_3051018) baseStart_3051018 baseEnd_3051018 := by
    simpa [prefixWord, tailWord_3051018, baseEnd_3051018] using wordTrace_append hprefix tailTrace_3051018
  have hstable : (prefixWord ++ tailWord_3051018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051018).length < 2 ^ (prefixWord ++ tailWord_3051018).sum := by decide
  have hdescent : baseEnd_3051018 < baseStart_3051018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051050 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_3051050 : Nat := 118140960795 + 3051050 * 2 ^ 59
def prefixEnd_3051050 : Nat := 4983230072969 + 3 ^ 40 * 3051050 * 2
def baseEnd_3051050 : Nat := 348145589088976219231885

theorem tailTrace_3051050 : CollatzResearch.WordTrace tailWord_3051050 prefixEnd_3051050 348145589088976219231885 := by
  unfold tailWord_3051050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820233899143600674995651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74187290397716268466655069 27820233899143600674995651)
  ·
    refine ⟨41730350848715401012493477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27820233899143600674995651 41730350848715401012493477)
    ·
      refine ⟨7824440784134137689842527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41730350848715401012493477 7824440784134137689842527)
      ·
        refine ⟨11736661176201206534763791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824440784134137689842527 11736661176201206534763791)
        ·
          refine ⟨17604991764301809802145687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736661176201206534763791 17604991764301809802145687)
          ·
            refine ⟨26407487646452714703218531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17604991764301809802145687 26407487646452714703218531)
            ·
              refine ⟨39611231469679072054827797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26407487646452714703218531 39611231469679072054827797)
              ·
                refine ⟨1856776475141206502570053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39611231469679072054827797 1856776475141206502570053)
                ·
                  refine ⟨348145589088976219231885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856776475141206502570053 348145589088976219231885)
                  ·
                    rfl

theorem cell22_3051050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_3051050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051050 prefixEnd_3051050 := by exact prefixLift 3051050
  have htrace : WordTrace (prefixWord ++ tailWord_3051050) baseStart_3051050 baseEnd_3051050 := by
    simpa [prefixWord, tailWord_3051050, baseEnd_3051050] using wordTrace_append hprefix tailTrace_3051050
  have hstable : (prefixWord ++ tailWord_3051050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051050).length < 2 ^ (prefixWord ++ tailWord_3051050).sum := by decide
  have hdescent : baseEnd_3051050 < baseStart_3051050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051065 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_3051065 : Nat := 118140960795 + 3051065 * 2 ^ 59
def prefixEnd_3051065 : Nat := 4983230072969 + 3 ^ 40 * 3051065 * 2
def baseEnd_3051065 : Nat := 1044441902073473618570609

theorem tailTrace_3051065 : CollatzResearch.WordTrace tailWord_3051065 prefixEnd_3051065 1044441902073473618570609 := by
  unfold tailWord_3051065
  simp only [CollatzResearch.WordTrace]
  refine ⟨111281482691520060261778649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74187655127680040174519099 111281482691520060261778649)
  ·
    refine ⟨83461112018640045196333987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111281482691520060261778649 83461112018640045196333987)
    ·
      refine ⟨125191668027960067794500981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83461112018640045196333987 125191668027960067794500981)
      ·
        refine ⟨11736718877621256355734467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125191668027960067794500981 11736718877621256355734467)
        ·
          refine ⟨17605078316431884533601701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736718877621256355734467 17605078316431884533601701)
          ·
            refine ⟨3300952184330978350050319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17605078316431884533601701 3300952184330978350050319)
            ·
              refine ⟨4951428276496467525075479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300952184330978350050319 4951428276496467525075479)
              ·
                refine ⟨7427142414744701287613219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951428276496467525075479 7427142414744701287613219)
                ·
                  refine ⟨11140713622117051931419829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427142414744701287613219 11140713622117051931419829)
                  ·
                    refine ⟨1044441902073473618570609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11140713622117051931419829 1044441902073473618570609)
                    ·
                      rfl

theorem cell22_3051065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_3051065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051065 prefixEnd_3051065 := by exact prefixLift 3051065
  have htrace : WordTrace (prefixWord ++ tailWord_3051065) baseStart_3051065 baseEnd_3051065 := by
    simpa [prefixWord, tailWord_3051065, baseEnd_3051065] using wordTrace_append hprefix tailTrace_3051065
  have hstable : (prefixWord ++ tailWord_3051065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051065).length < 2 ^ (prefixWord ++ tailWord_3051065).sum := by decide
  have hdescent : baseEnd_3051065 < baseStart_3051065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051091 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_3051091 : Nat := 118140960795 + 3051091 * 2 ^ 59
def prefixEnd_3051091 : Nat := 4983230072969 + 3 ^ 40 * 3051091 * 2
def baseEnd_3051091 : Nat := 1044450802404818217420529

theorem tailTrace_3051091 : CollatzResearch.WordTrace tailWord_3051091 prefixEnd_3051091 1044450802404818217420529 := by
  unfold tailWord_3051091
  simp only [CollatzResearch.WordTrace]
  refine ⟨111282430989425866702225127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74188287326283911134816751 111282430989425866702225127)
  ·
    refine ⟨166923646484138800053337691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111282430989425866702225127 166923646484138800053337691)
    ·
      refine ⟨250385469726208200080006537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166923646484138800053337691 250385469726208200080006537)
      ·
        refine ⟨187789102294656150060004903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250385469726208200080006537 187789102294656150060004903)
        ·
          refine ⟨281683653441984225090007355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187789102294656150060004903 281683653441984225090007355)
          ·
            refine ⟨422525480162976337635011033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281683653441984225090007355 422525480162976337635011033)
            ·
              refine ⟨316894110122232253226258275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422525480162976337635011033 316894110122232253226258275)
              ·
                refine ⟨475341165183348379839387413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316894110122232253226258275 475341165183348379839387413)
                ·
                  refine ⟨22281617117969455304971285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 475341165183348379839387413 22281617117969455304971285)
                  ·
                    refine ⟨1044450802404818217420529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22281617117969455304971285 1044450802404818217420529)
                    ·
                      rfl

theorem cell22_3051091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_3051091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051091 prefixEnd_3051091 := by exact prefixLift 3051091
  have htrace : WordTrace (prefixWord ++ tailWord_3051091) baseStart_3051091 baseEnd_3051091 := by
    simpa [prefixWord, tailWord_3051091, baseEnd_3051091] using wordTrace_append hprefix tailTrace_3051091
  have hstable : (prefixWord ++ tailWord_3051091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051091).length < 2 ^ (prefixWord ++ tailWord_3051091).sum := by decide
  have hdescent : baseEnd_3051091 < baseStart_3051091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051101 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 4]
def baseStart_3051101 : Nat := 118140960795 + 3051101 * 2 ^ 59
def prefixEnd_3051101 : Nat := 4983230072969 + 3 ^ 40 * 3051101 * 2
def baseEnd_3051101 : Nat := 348151408536393841556833

theorem tailTrace_3051101 : CollatzResearch.WordTrace tailWord_3051101 prefixEnd_3051101 348151408536393841556833 := by
  unfold tailWord_3051101
  simp only [CollatzResearch.WordTrace]
  refine ⟨111282795719389638410089157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74188530479593092273392771 111282795719389638410089157)
  ·
    refine ⟨20865524197385557201891717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111282795719389638410089157 20865524197385557201891717)
    ·
      refine ⟨3912285787009791975354697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20865524197385557201891717 3912285787009791975354697)
      ·
        refine ⟨2934214340257343981516023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912285787009791975354697 2934214340257343981516023)
        ·
          refine ⟨4401321510386015972274035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934214340257343981516023 4401321510386015972274035)
          ·
            refine ⟨6601982265579023958411053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401321510386015972274035 6601982265579023958411053)
            ·
              refine ⟨2475743349592133984404145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601982265579023958411053 2475743349592133984404145)
              ·
                refine ⟨1856807512194100488303109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475743349592133984404145 1856807512194100488303109)
                ·
                  refine ⟨348151408536393841556833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856807512194100488303109 348151408536393841556833)
                  ·
                    rfl

theorem cell22_3051101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_3051101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051101 prefixEnd_3051101 := by exact prefixLift 3051101
  have htrace : WordTrace (prefixWord ++ tailWord_3051101) baseStart_3051101 baseEnd_3051101 := by
    simpa [prefixWord, tailWord_3051101, baseEnd_3051101] using wordTrace_append hprefix tailTrace_3051101
  have hstable : (prefixWord ++ tailWord_3051101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051101).length < 2 ^ (prefixWord ++ tailWord_3051101).sum := by decide
  have hdescent : baseEnd_3051101 < baseStart_3051101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051200 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_3051200 : Nat := 118140960795 + 3051200 * 2 ^ 59
def prefixEnd_3051200 : Nat := 4983230072969 + 3 ^ 40 * 3051200 * 2
def baseEnd_3051200 : Nat := 1044488115332378266445195

theorem tailTrace_3051200 : CollatzResearch.WordTrace tailWord_3051200 prefixEnd_3051200 1044488115332378266445195 := by
  unfold tailWord_3051200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643203273015489158971527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74190937697353985545295369 55643203273015489158971527)
  ·
    refine ⟨83464804909523233738457291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55643203273015489158971527 83464804909523233738457291)
    ·
      refine ⟨125197207364284850607685937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83464804909523233738457291 125197207364284850607685937)
      ·
        refine ⟨93897905523213637955764453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125197207364284850607685937 93897905523213637955764453)
        ·
          refine ⟨17605857285602557116705835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93897905523213637955764453 17605857285602557116705835)
          ·
            refine ⟨26408785928403835675058753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17605857285602557116705835 26408785928403835675058753)
            ·
              refine ⟨19806589446302876756294065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26408785928403835675058753 19806589446302876756294065)
              ·
                refine ⟨14854942084727157567220549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19806589446302876756294065 14854942084727157567220549)
                ·
                  refine ⟨2785301640886342043853853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14854942084727157567220549 2785301640886342043853853)
                  ·
                    refine ⟨1044488115332378266445195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785301640886342043853853 1044488115332378266445195)
                    ·
                      rfl

theorem cell22_3051200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_3051200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051200 prefixEnd_3051200 := by exact prefixLift 3051200
  have htrace : WordTrace (prefixWord ++ tailWord_3051200) baseStart_3051200 baseEnd_3051200 := by
    simpa [prefixWord, tailWord_3051200, baseEnd_3051200] using wordTrace_append hprefix tailTrace_3051200
  have hstable : (prefixWord ++ tailWord_3051200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051200).length < 2 ^ (prefixWord ++ tailWord_3051200).sum := by decide
  have hdescent : baseEnd_3051200 < baseStart_3051200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051217 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_3051217 : Nat := 118140960795 + 3051217 * 2 ^ 59
def prefixEnd_3051217 : Nat := 4983230072969 + 3 ^ 40 * 3051217 * 2
def baseEnd_3051217 : Nat := 1044493934779795888770143

theorem tailTrace_3051217 : CollatzResearch.WordTrace tailWord_3051217 prefixEnd_3051217 1044493934779795888770143 := by
  unfold tailWord_3051217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111287026586969390221311905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74191351057979593480874603 111287026586969390221311905)
  ·
    refine ⟨83465269940227042665983929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111287026586969390221311905 83465269940227042665983929)
    ·
      refine ⟨62598952455170281999487947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83465269940227042665983929 62598952455170281999487947)
      ·
        refine ⟨93898428682755422999231921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62598952455170281999487947 93898428682755422999231921)
        ·
          refine ⟨70423821512066567249423941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93898428682755422999231921 70423821512066567249423941)
          ·
            refine ⟨13204466533512481359266989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70423821512066567249423941 13204466533512481359266989)
            ·
              refine ⟨4951674950067180509725121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13204466533512481359266989 4951674950067180509725121)
              ·
                refine ⟨3713756212550385382293841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951674950067180509725121 3713756212550385382293841)
                ·
                  refine ⟨2785317159412789036720381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713756212550385382293841 2785317159412789036720381)
                  ·
                    refine ⟨1044493934779795888770143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785317159412789036720381 1044493934779795888770143)
                    ·
                      rfl

theorem cell22_3051217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_3051217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051217 prefixEnd_3051217 := by exact prefixLift 3051217
  have htrace : WordTrace (prefixWord ++ tailWord_3051217) baseStart_3051217 baseEnd_3051217 := by
    simpa [prefixWord, tailWord_3051217, baseEnd_3051217] using wordTrace_append hprefix tailTrace_3051217
  have hstable : (prefixWord ++ tailWord_3051217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051217).length < 2 ^ (prefixWord ++ tailWord_3051217).sum := by decide
  have hdescent : baseEnd_3051217 < baseStart_3051217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051243 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_3051243 : Nat := 118140960795 + 3051243 * 2 ^ 59
def prefixEnd_3051243 : Nat := 4983230072969 + 3 ^ 40 * 3051243 * 2
def baseEnd_3051243 : Nat := 1044502835111140487620063

theorem tailTrace_3051243 : CollatzResearch.WordTrace tailWord_3051243 prefixEnd_3051243 1044502835111140487620063 := by
  unfold tailWord_3051243
  simp only [CollatzResearch.WordTrace]
  refine ⟨111287974884875196661758383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74191983256583464441172255 111287974884875196661758383)
  ·
    refine ⟨166931962327312794992637575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111287974884875196661758383 166931962327312794992637575)
    ·
      refine ⟨250397943490969192488956363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166931962327312794992637575 250397943490969192488956363)
      ·
        refine ⟨375596915236453788733434545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250397943490969192488956363 375596915236453788733434545)
        ·
          refine ⟨281697686427340341550075909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375596915236453788733434545 281697686427340341550075909)
          ·
            refine ⟨52818316205126314040639233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281697686427340341550075909 52818316205126314040639233)
            ·
              refine ⟨39613737153844735530479425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52818316205126314040639233 39613737153844735530479425)
              ·
                refine ⟨29710302865383551647859569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39613737153844735530479425 29710302865383551647859569)
                ·
                  refine ⟨22282727149037663735894677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29710302865383551647859569 22282727149037663735894677)
                  ·
                    refine ⟨1044502835111140487620063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22282727149037663735894677 1044502835111140487620063)
                    ·
                      rfl

theorem cell22_3051243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_3051243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051243 prefixEnd_3051243 := by exact prefixLift 3051243
  have htrace : WordTrace (prefixWord ++ tailWord_3051243) baseStart_3051243 baseEnd_3051243 := by
    simpa [prefixWord, tailWord_3051243, baseEnd_3051243] using wordTrace_append hprefix tailTrace_3051243
  have hstable : (prefixWord ++ tailWord_3051243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051243).length < 2 ^ (prefixWord ++ tailWord_3051243).sum := by decide
  have hdescent : baseEnd_3051243 < baseStart_3051243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051270 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3051270 : Nat := 118140960795 + 3051270 * 2 ^ 59
def prefixEnd_3051270 : Nat := 4983230072969 + 3 ^ 40 * 3051270 * 2
def baseEnd_3051270 : Nat := 348170692587640472398327

theorem tailTrace_3051270 : CollatzResearch.WordTrace tailWord_3051270 prefixEnd_3051270 348170692587640472398327 := by
  unfold tailWord_3051270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477779989243043133530977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74192639770518253515327509 3477779989243043133530977)
  ·
    refine ⟨2608334991932282350148233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3477779989243043133530977 2608334991932282350148233)
    ·
      refine ⟨1956251243949211762611175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2608334991932282350148233 1956251243949211762611175)
      ·
        refine ⟨2934376865923817643916763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956251243949211762611175 2934376865923817643916763)
        ·
          refine ⟨4401565298885726465875145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934376865923817643916763 4401565298885726465875145)
          ·
            refine ⟨3301173974164294849406359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401565298885726465875145 3301173974164294849406359)
            ·
              refine ⟨4951760961246442274109539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301173974164294849406359 4951760961246442274109539)
              ·
                refine ⟨7427641441869663411164309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951760961246442274109539 7427641441869663411164309)
                ·
                  refine ⟨348170692587640472398327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7427641441869663411164309 348170692587640472398327)
                  ·
                    rfl

theorem cell22_3051270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3051270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051270 prefixEnd_3051270 := by exact prefixLift 3051270
  have htrace : WordTrace (prefixWord ++ tailWord_3051270) baseStart_3051270 baseEnd_3051270 := by
    simpa [prefixWord, tailWord_3051270, baseEnd_3051270] using wordTrace_append hprefix tailTrace_3051270
  have hstable : (prefixWord ++ tailWord_3051270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051270).length < 2 ^ (prefixWord ++ tailWord_3051270).sum := by decide
  have hdescent : baseEnd_3051270 < baseStart_3051270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051337 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 4]
def baseStart_3051337 : Nat := 118140960795 + 3051337 * 2 ^ 59
def prefixEnd_3051337 : Nat := 4983230072969 + 3 ^ 40 * 3051337 * 2
def baseEnd_3051337 : Nat := 348178337744051858589925

theorem tailTrace_3051337 : CollatzResearch.WordTrace tailWord_3051337 prefixEnd_3051337 348178337744051858589925 := by
  unfold tailWord_3051337
  simp only [CollatzResearch.WordTrace]
  refine ⟨111291403346534650715680265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74194268897689767143786843 111291403346534650715680265)
  ·
    refine ⟨83468552509900988036760199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111291403346534650715680265 83468552509900988036760199)
    ·
      refine ⟨125202828764851482055140299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83468552509900988036760199 125202828764851482055140299)
      ·
        refine ⟨187804243147277223082710449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125202828764851482055140299 187804243147277223082710449)
        ·
          refine ⟨140853182360457917312032837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187804243147277223082710449 140853182360457917312032837)
          ·
            refine ⟨26409971692585859496006157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140853182360457917312032837 26409971692585859496006157)
            ·
              refine ⟨9903739384719697311002309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26409971692585859496006157 9903739384719697311002309)
              ·
                refine ⟨1856951134634943245812933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9903739384719697311002309 1856951134634943245812933)
                ·
                  refine ⟨348178337744051858589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856951134634943245812933 348178337744051858589925)
                  ·
                    rfl

theorem cell22_3051337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_3051337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051337 prefixEnd_3051337 := by exact prefixLift 3051337
  have htrace : WordTrace (prefixWord ++ tailWord_3051337) baseStart_3051337 baseEnd_3051337 := by
    simpa [prefixWord, tailWord_3051337, baseEnd_3051337] using wordTrace_append hprefix tailTrace_3051337
  have hstable : (prefixWord ++ tailWord_3051337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051337).length < 2 ^ (prefixWord ++ tailWord_3051337).sum := by decide
  have hdescent : baseEnd_3051337 < baseStart_3051337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051416 : List Nat := [2, 1, 2, 6, 1, 2, 2, 6]
def baseStart_3051416 : Nat := 118140960795 + 3051416 * 2 ^ 59
def prefixEnd_3051416 : Nat := 4983230072969 + 3 ^ 40 * 3051416 * 2
def baseEnd_3051416 : Nat := 116062450727402855893837

theorem tailTrace_3051416 : CollatzResearch.WordTrace tailWord_3051416 prefixEnd_3051416 116062450727402855893837 := by
  unfold tailWord_3051416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55647142356624223603903051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74196189808832298138537401 55647142356624223603903051)
  ·
    refine ⟨83470713534936335405854577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55647142356624223603903051 83470713534936335405854577)
    ·
      refine ⟨62603035151202251554390933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83470713534936335405854577 62603035151202251554390933)
      ·
        refine ⟨2934517272712605541612075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62603035151202251554390933 2934517272712605541612075)
        ·
          refine ⟨4401775909068908312418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934517272712605541612075 4401775909068908312418113)
          ·
            refine ⟨3301331931801681234313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401775909068908312418113 3301331931801681234313585)
            ·
              refine ⟨2475998948851260925735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301331931801681234313585 2475998948851260925735189)
              ·
                refine ⟨116062450727402855893837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2475998948851260925735189 116062450727402855893837)
                ·
                  rfl

theorem cell22_3051416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_3051416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051416 prefixEnd_3051416 := by exact prefixLift 3051416
  have htrace : WordTrace (prefixWord ++ tailWord_3051416) baseStart_3051416 baseEnd_3051416 := by
    simpa [prefixWord, tailWord_3051416, baseEnd_3051416] using wordTrace_append hprefix tailTrace_3051416
  have hstable : (prefixWord ++ tailWord_3051416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051416).length < 2 ^ (prefixWord ++ tailWord_3051416).sum := by decide
  have hdescent : baseEnd_3051416 < baseStart_3051416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051487 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3051487 : Nat := 118140960795 + 3051487 * 2 ^ 59
def prefixEnd_3051487 : Nat := 4983230072969 + 3 ^ 40 * 3051487 * 2
def baseEnd_3051487 : Nat := 1044586361297605184519315

theorem tailTrace_3051487 : CollatzResearch.WordTrace tailWord_3051487 prefixEnd_3051487 1044586361297605184519315 := by
  unfold tailWord_3051487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111296874295991226333640715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74197916197327484222427143 111296874295991226333640715)
  ·
    refine ⟨166945311443986839500461073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111296874295991226333640715 166945311443986839500461073)
    ·
      refine ⟨125208983582990129625345805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166945311443986839500461073 125208983582990129625345805)
      ·
        refine ⟨46953368843621298609504677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125208983582990129625345805 46953368843621298609504677)
        ·
          refine ⟨8803756658178993489282127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46953368843621298609504677 8803756658178993489282127)
          ·
            refine ⟨13205634987268490233923191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8803756658178993489282127 13205634987268490233923191)
            ·
              refine ⟨19808452480902735350884787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13205634987268490233923191 19808452480902735350884787)
              ·
                refine ⟨29712678721354103026327181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19808452480902735350884787 29712678721354103026327181)
                ·
                  refine ⟨11142254520507788634872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29712678721354103026327181 11142254520507788634872693)
                  ·
                    refine ⟨1044586361297605184519315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11142254520507788634872693 1044586361297605184519315)
                    ·
                      rfl

theorem cell22_3051487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3051487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051487 prefixEnd_3051487 := by exact prefixLift 3051487
  have htrace : WordTrace (prefixWord ++ tailWord_3051487) baseStart_3051487 baseEnd_3051487 := by
    simpa [prefixWord, tailWord_3051487, baseEnd_3051487] using wordTrace_append hprefix tailTrace_3051487
  have hstable : (prefixWord ++ tailWord_3051487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051487).length < 2 ^ (prefixWord ++ tailWord_3051487).sum := by decide
  have hdescent : baseEnd_3051487 < baseStart_3051487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051491 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 1, 4]
def baseStart_3051491 : Nat := 118140960795 + 3051491 * 2 ^ 59
def prefixEnd_3051491 : Nat := 4983230072969 + 3 ^ 40 * 3051491 * 2
def baseEnd_3051491 : Nat := 1044587730579350507419303

theorem tailTrace_3051491 : CollatzResearch.WordTrace tailWord_3051491 prefixEnd_3051491 1044587730579350507419303 := by
  unfold tailWord_3051491
  simp only [CollatzResearch.WordTrace]
  refine ⟨111297020187976735016786327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74198013458651156677857551 111297020187976735016786327)
  ·
    refine ⟨166945530281965102525179491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111297020187976735016786327 166945530281965102525179491)
    ·
      refine ⟨250418295422947653787769237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166945530281965102525179491 250418295422947653787769237)
      ·
        refine ⟨11738357597950671271301683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 250418295422947653787769237 11738357597950671271301683)
        ·
          refine ⟨17607536396926006906952525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11738357597950671271301683 17607536396926006906952525)
          ·
            refine ⟨6602826148847252590107197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17607536396926006906952525 6602826148847252590107197)
            ·
              refine ⟨2476059805817719721290199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6602826148847252590107197 2476059805817719721290199)
              ·
                refine ⟨3714089708726579581935299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476059805817719721290199 3714089708726579581935299)
                ·
                  refine ⟨5571134563089869372902949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714089708726579581935299 5571134563089869372902949)
                  ·
                    refine ⟨1044587730579350507419303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571134563089869372902949 1044587730579350507419303)
                    ·
                      rfl

theorem cell22_3051491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 4].length) (baseStart_3051491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051491 prefixEnd_3051491 := by exact prefixLift 3051491
  have htrace : WordTrace (prefixWord ++ tailWord_3051491) baseStart_3051491 baseEnd_3051491 := by
    simpa [prefixWord, tailWord_3051491, baseEnd_3051491] using wordTrace_append hprefix tailTrace_3051491
  have hstable : (prefixWord ++ tailWord_3051491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051491).length < 2 ^ (prefixWord ++ tailWord_3051491).sum := by decide
  have hdescent : baseEnd_3051491 < baseStart_3051491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051504 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_3051504 : Nat := 118140960795 + 3051504 * 2 ^ 59
def prefixEnd_3051504 : Nat := 4983230072969 + 3 ^ 40 * 3051504 * 2
def baseEnd_3051504 : Nat := 1044592180745022806844263

theorem tailTrace_3051504 : CollatzResearch.WordTrace tailWord_3051504 prefixEnd_3051504 1044592180745022806844263 := by
  unfold tailWord_3051504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55648747168464819118504783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74198329557953092158006377 55648747168464819118504783)
  ·
    refine ⟨83473120752697228677757175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55648747168464819118504783 83473120752697228677757175)
    ·
      refine ⟨125209681129045843016635763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83473120752697228677757175 125209681129045843016635763)
      ·
        refine ⟨187814521693568764524953645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125209681129045843016635763 187814521693568764524953645)
        ·
          refine ⟨70430445635088286696857617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187814521693568764524953645 70430445635088286696857617)
          ·
            refine ⟨52822834226316215022643213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70430445635088286696857617 52822834226316215022643213)
            ·
              refine ⟨19808562834868580633491205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52822834226316215022643213 19808562834868580633491205)
              ·
                refine ⟨3714105531537858868779601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19808562834868580633491205 3714105531537858868779601)
                ·
                  refine ⟨2785579148653394151584701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714105531537858868779601 2785579148653394151584701)
                  ·
                    refine ⟨1044592180745022806844263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785579148653394151584701 1044592180745022806844263)
                    ·
                      rfl

theorem cell22_3051504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_3051504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051504 prefixEnd_3051504 := by exact prefixLift 3051504
  have htrace : WordTrace (prefixWord ++ tailWord_3051504) baseStart_3051504 baseEnd_3051504 := by
    simpa [prefixWord, tailWord_3051504, baseEnd_3051504] using wordTrace_append hprefix tailTrace_3051504
  have hstable : (prefixWord ++ tailWord_3051504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051504).length < 2 ^ (prefixWord ++ tailWord_3051504).sum := by decide
  have hdescent : baseEnd_3051504 < baseStart_3051504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051517 : List Nat := [1, 4, 1, 1, 1, 2, 5, 7]
def baseStart_3051517 : Nat := 118140960795 + 3051517 * 2 ^ 59
def prefixEnd_3051517 : Nat := 4983230072969 + 3 ^ 40 * 3051517 * 2
def baseEnd_3051517 : Nat := 116066292323410567363247

theorem tailTrace_3051517 : CollatzResearch.WordTrace tailWord_3051517 prefixEnd_3051517 116066292323410567363247 := by
  unfold tailWord_3051517
  simp only [CollatzResearch.WordTrace]
  refine ⟨111297968485882541457232805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74198645657255027638155203 111297968485882541457232805)
  ·
    refine ⟨20868369091102976523231151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111297968485882541457232805 20868369091102976523231151)
    ·
      refine ⟨31302553636654464784846727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20868369091102976523231151 31302553636654464784846727)
      ·
        refine ⟨46953830454981697177270091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31302553636654464784846727 46953830454981697177270091)
        ·
          refine ⟨70430745682472545765905137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46953830454981697177270091 70430745682472545765905137)
          ·
            refine ⟨52823059261854409324428853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70430745682472545765905137 52823059261854409324428853)
            ·
              refine ⟨4952161805798850874165205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52823059261854409324428853 4952161805798850874165205)
              ·
                refine ⟨116066292323410567363247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4952161805798850874165205 116066292323410567363247)
                ·
                  rfl

theorem cell22_3051517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 7].length) (baseStart_3051517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051517 prefixEnd_3051517 := by exact prefixLift 3051517
  have htrace : WordTrace (prefixWord ++ tailWord_3051517) baseStart_3051517 baseEnd_3051517 := by
    simpa [prefixWord, tailWord_3051517, baseEnd_3051517] using wordTrace_append hprefix tailTrace_3051517
  have hstable : (prefixWord ++ tailWord_3051517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051517).length < 2 ^ (prefixWord ++ tailWord_3051517).sum := by decide
  have hdescent : baseEnd_3051517 < baseStart_3051517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051534 : List Nat := [4, 1, 1, 2, 2, 1, 5, 6]
def baseStart_3051534 : Nat := 118140960795 + 3051534 * 2 ^ 59
def prefixEnd_3051534 : Nat := 4983230072969 + 3 ^ 40 * 3051534 * 2
def baseEnd_3051534 : Nat := 116066938928679192066019

theorem tailTrace_3051534 : CollatzResearch.WordTrace tailWord_3051534 prefixEnd_3051534 116066938928679192066019 := by
  unfold tailWord_3051534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13912323565852619170075207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74199059017880635573734437 13912323565852619170075207)
  ·
    refine ⟨20868485348778928755112811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13912323565852619170075207 20868485348778928755112811)
    ·
      refine ⟨31302728023168393132669217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20868485348778928755112811 31302728023168393132669217)
      ·
        refine ⟨23477046017376294849501913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31302728023168393132669217 23477046017376294849501913)
        ·
          refine ⟨17607784513032221137126435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23477046017376294849501913 17607784513032221137126435)
          ·
            refine ⟨26411676769548331705689653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17607784513032221137126435 26411676769548331705689653)
            ·
              refine ⟨2476094697145156097408405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26411676769548331705689653 2476094697145156097408405)
              ·
                refine ⟨116066938928679192066019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2476094697145156097408405 116066938928679192066019)
                ·
                  rfl

theorem cell22_3051534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_3051534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051534 prefixEnd_3051534 := by exact prefixLift 3051534
  have htrace : WordTrace (prefixWord ++ tailWord_3051534) baseStart_3051534 baseEnd_3051534 := by
    simpa [prefixWord, tailWord_3051534, baseEnd_3051534] using wordTrace_append hprefix tailTrace_3051534
  have hstable : (prefixWord ++ tailWord_3051534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051534).length < 2 ^ (prefixWord ++ tailWord_3051534).sum := by decide
  have hdescent : baseEnd_3051534 < baseStart_3051534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051540 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3051540 : Nat := 118140960795 + 3051540 * 2 ^ 59
def prefixEnd_3051540 : Nat := 4983230072969 + 3 ^ 40 * 3051540 * 2
def baseEnd_3051540 : Nat := 348201501426910237648051

theorem tailTrace_3051540 : CollatzResearch.WordTrace tailWord_3051540 prefixEnd_3051540 348201501426910237648051 := by
  unfold tailWord_3051540
  simp only [CollatzResearch.WordTrace]
  refine ⟨55649403682399608192660037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74199204909866144256880049 55649403682399608192660037)
  ·
    refine ⟨10434263190449926536123757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55649403682399608192660037 10434263190449926536123757)
    ·
      refine ⟨3912848696418722451046409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10434263190449926536123757 3912848696418722451046409)
      ·
        refine ⟨2934636522314041838284807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912848696418722451046409 2934636522314041838284807)
        ·
          refine ⟨4401954783471062757427211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934636522314041838284807 4401954783471062757427211)
          ·
            refine ⟨6602932175206594136140817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401954783471062757427211 6602932175206594136140817)
            ·
              refine ⟨4952199131404945602105613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6602932175206594136140817 4952199131404945602105613)
              ·
                refine ⟨1857074674276854600789605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4952199131404945602105613 1857074674276854600789605)
                ·
                  refine ⟨348201501426910237648051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857074674276854600789605 348201501426910237648051)
                  ·
                    rfl

theorem cell22_3051540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3051540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051540 prefixEnd_3051540 := by exact prefixLift 3051540
  have htrace : WordTrace (prefixWord ++ tailWord_3051540) baseStart_3051540 baseEnd_3051540 := by
    simpa [prefixWord, tailWord_3051540, baseEnd_3051540] using wordTrace_append hprefix tailTrace_3051540
  have hstable : (prefixWord ++ tailWord_3051540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051540).length < 2 ^ (prefixWord ++ tailWord_3051540).sum := by decide
  have hdescent : baseEnd_3051540 < baseStart_3051540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051566 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3051566 : Nat := 118140960795 + 3051566 * 2 ^ 59
def prefixEnd_3051566 : Nat := 4983230072969 + 3 ^ 40 * 3051566 * 2
def baseEnd_3051566 : Nat := 1044613404612075311794073

theorem tailTrace_3051566 : CollatzResearch.WordTrace tailWord_3051566 prefixEnd_3051566 1044613404612075311794073 := by
  unfold tailWord_3051566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13912469457838127853220819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74199837108470015217177701 13912469457838127853220819)
  ·
    refine ⟨20868704186757191779831229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13912469457838127853220819 20868704186757191779831229)
    ·
      refine ⟨7825764070033946917436711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20868704186757191779831229 7825764070033946917436711)
      ·
        refine ⟨11738646105050920376155067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7825764070033946917436711 11738646105050920376155067)
        ·
          refine ⟨17607969157576380564232601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11738646105050920376155067 17607969157576380564232601)
          ·
            refine ⟨13205976868182285423174451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17607969157576380564232601 13205976868182285423174451)
            ·
              refine ⟨19808965302273428134761677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13205976868182285423174451 19808965302273428134761677)
              ·
                refine ⟨7428361988352535550535629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19808965302273428134761677 7428361988352535550535629)
                ·
                  refine ⟨2785635745632200831450861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7428361988352535550535629 2785635745632200831450861)
                  ·
                    refine ⟨1044613404612075311794073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785635745632200831450861 1044613404612075311794073)
                    ·
                      rfl

theorem cell22_3051566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3051566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051566 prefixEnd_3051566 := by exact prefixLift 3051566
  have htrace : WordTrace (prefixWord ++ tailWord_3051566) baseStart_3051566 baseEnd_3051566 := by
    simpa [prefixWord, tailWord_3051566, baseEnd_3051566] using wordTrace_append hprefix tailTrace_3051566
  have hstable : (prefixWord ++ tailWord_3051566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051566).length < 2 ^ (prefixWord ++ tailWord_3051566).sum := by decide
  have hdescent : baseEnd_3051566 < baseStart_3051566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051607 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 8]
def baseStart_3051607 : Nat := 118140960795 + 3051607 * 2 ^ 59
def prefixEnd_3051607 : Nat := 4983230072969 + 3 ^ 40 * 3051607 * 2
def baseEnd_3051607 : Nat := 348209146583321623839649

theorem tailTrace_3051607 : CollatzResearch.WordTrace tailWord_3051607 prefixEnd_3051607 348209146583321623839649 := by
  unfold tailWord_3051607
  simp only [CollatzResearch.WordTrace]
  refine ⟨111301251055556486828009075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74200834037037657885339383 111301251055556486828009075)
  ·
    refine ⟨166951876583334730242013613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111301251055556486828009075 166951876583334730242013613)
    ·
      refine ⟨62606953718750523840755105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166951876583334730242013613 62606953718750523840755105)
      ·
        refine ⟨46955215289062892880566329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62606953718750523840755105 46955215289062892880566329)
        ·
          refine ⟨35216411466797169660424747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46955215289062892880566329 35216411466797169660424747)
          ·
            refine ⟨52824617200195754490637121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35216411466797169660424747 52824617200195754490637121)
            ·
              refine ⟨39618462900146815867977841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52824617200195754490637121 39618462900146815867977841)
              ·
                refine ⟨29713847175110111900983381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39618462900146815867977841 29713847175110111900983381)
                ·
                  refine ⟨348209146583321623839649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29713847175110111900983381 348209146583321623839649)
                  ·
                    rfl

theorem cell22_3051607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_3051607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051607 prefixEnd_3051607 := by exact prefixLift 3051607
  have htrace : WordTrace (prefixWord ++ tailWord_3051607) baseStart_3051607 baseEnd_3051607 := by
    simpa [prefixWord, tailWord_3051607, baseEnd_3051607] using wordTrace_append hprefix tailTrace_3051607
  have hstable : (prefixWord ++ tailWord_3051607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051607).length < 2 ^ (prefixWord ++ tailWord_3051607).sum := by decide
  have hdescent : baseEnd_3051607 < baseStart_3051607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051609 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_3051609 : Nat := 118140960795 + 3051609 * 2 ^ 59
def prefixEnd_3051609 : Nat := 4983230072969 + 3 ^ 40 * 3051609 * 2
def baseEnd_3051609 : Nat := 1044628124390837532968941

theorem tailTrace_3051609 : CollatzResearch.WordTrace tailWord_3051609 prefixEnd_3051609 1044628124390837532968941 := by
  unfold tailWord_3051609
  simp only [CollatzResearch.WordTrace]
  refine ⟨111301324001549241169581881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74200882667699494113054587 111301324001549241169581881)
  ·
    refine ⟨83475993001161930877186411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111301324001549241169581881 83475993001161930877186411)
    ·
      refine ⟨125213989501742896315779617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83475993001161930877186411 125213989501742896315779617)
      ·
        refine ⟨93910492126307172236834713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125213989501742896315779617 93910492126307172236834713)
        ·
          refine ⟨70432869094730379177626035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93910492126307172236834713 70432869094730379177626035)
          ·
            refine ⟨105649303642095568766439053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70432869094730379177626035 105649303642095568766439053)
            ·
              refine ⟨39618488865785838287414645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105649303642095568766439053 39618488865785838287414645)
              ·
                refine ⟨3714233331167422339445123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39618488865785838287414645 3714233331167422339445123)
                ·
                  refine ⟨5571349996751133509167685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714233331167422339445123 5571349996751133509167685)
                  ·
                    refine ⟨1044628124390837532968941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571349996751133509167685 1044628124390837532968941)
                    ·
                      rfl

theorem cell22_3051609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_3051609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051609 prefixEnd_3051609 := by exact prefixLift 3051609
  have htrace : WordTrace (prefixWord ++ tailWord_3051609) baseStart_3051609 baseEnd_3051609 := by
    simpa [prefixWord, tailWord_3051609, baseEnd_3051609] using wordTrace_append hprefix tailTrace_3051609
  have hstable : (prefixWord ++ tailWord_3051609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051609).length < 2 ^ (prefixWord ++ tailWord_3051609).sum := by decide
  have hdescent : baseEnd_3051609 < baseStart_3051609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051656 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3051656 : Nat := 118140960795 + 3051656 * 2 ^ 59
def prefixEnd_3051656 : Nat := 4983230072969 + 3 ^ 40 * 3051656 * 2
def baseEnd_3051656 : Nat := 1044644213451345077043797

theorem tailTrace_3051656 : CollatzResearch.WordTrace tailWord_3051656 prefixEnd_3051656 1044644213451345077043797 := by
  unfold tailWord_3051656
  simp only [CollatzResearch.WordTrace]
  refine ⟨55651519116189484098271411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74202025488252645464361881 55651519116189484098271411)
  ·
    refine ⟨83477278674284226147407117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55651519116189484098271411 83477278674284226147407117)
    ·
      refine ⟨31303979502856584805277669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83477278674284226147407117 31303979502856584805277669)
      ·
        refine ⟨5869496156785609650989563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31303979502856584805277669 5869496156785609650989563)
        ·
          refine ⟨8804244235178414476484345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869496156785609650989563 8804244235178414476484345)
          ·
            refine ⟨6603183176383810857363259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804244235178414476484345 6603183176383810857363259)
            ·
              refine ⟨9904774764575716286044889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603183176383810857363259 9904774764575716286044889)
              ·
                refine ⟨7428581073431787214533667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904774764575716286044889 7428581073431787214533667)
                ·
                  refine ⟨11142871610147680821800501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428581073431787214533667 11142871610147680821800501)
                  ·
                    refine ⟨1044644213451345077043797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11142871610147680821800501 1044644213451345077043797)
                    ·
                      rfl

theorem cell22_3051656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3051656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051656 prefixEnd_3051656 := by exact prefixLift 3051656
  have htrace : WordTrace (prefixWord ++ tailWord_3051656) baseStart_3051656 baseEnd_3051656 := by
    simpa [prefixWord, tailWord_3051656, baseEnd_3051656] using wordTrace_append hprefix tailTrace_3051656
  have hstable : (prefixWord ++ tailWord_3051656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051656).length < 2 ^ (prefixWord ++ tailWord_3051656).sum := by decide
  have hdescent : baseEnd_3051656 < baseStart_3051656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051729 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3051729 : Nat := 118140960795 + 3051729 * 2 ^ 59
def prefixEnd_3051729 : Nat := 4983230072969 + 3 ^ 40 * 3051729 * 2
def baseEnd_3051729 : Nat := 1044669202843197219968573

theorem tailTrace_3051729 : CollatzResearch.WordTrace tailWord_3051729 prefixEnd_3051729 1044669202843197219968573 := by
  unfold tailWord_3051729
  simp only [CollatzResearch.WordTrace]
  refine ⟨111305700761114501663950241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74203800507409667775966827 111305700761114501663950241)
  ·
    refine ⟨83479275570835876247962681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111305700761114501663950241 83479275570835876247962681)
    ·
      refine ⟨62609456678126907185972011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83479275570835876247962681 62609456678126907185972011)
      ·
        refine ⟨93914185017190360778958017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62609456678126907185972011 93914185017190360778958017)
        ·
          refine ⟨70435638762892770584218513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93914185017190360778958017 70435638762892770584218513)
          ·
            refine ⟨52826729072169577938163885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70435638762892770584218513 52826729072169577938163885)
            ·
              refine ⟨19810023402063591726811457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52826729072169577938163885 19810023402063591726811457)
              ·
                refine ⟨14857517551547693795108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19810023402063591726811457 14857517551547693795108593)
                ·
                  refine ⟨11143138163660770346331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857517551547693795108593 11143138163660770346331445)
                  ·
                    refine ⟨1044669202843197219968573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143138163660770346331445 1044669202843197219968573)
                    ·
                      rfl

theorem cell22_3051729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3051729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051729 prefixEnd_3051729 := by exact prefixLift 3051729
  have htrace : WordTrace (prefixWord ++ tailWord_3051729) baseStart_3051729 baseEnd_3051729 := by
    simpa [prefixWord, tailWord_3051729, baseEnd_3051729] using wordTrace_append hprefix tailTrace_3051729
  have hstable : (prefixWord ++ tailWord_3051729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051729).length < 2 ^ (prefixWord ++ tailWord_3051729).sum := by decide
  have hdescent : baseEnd_3051729 < baseStart_3051729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051761 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3051761 : Nat := 118140960795 + 3051761 * 2 ^ 59
def prefixEnd_3051761 : Nat := 4983230072969 + 3 ^ 40 * 3051761 * 2
def baseEnd_3051761 : Nat := 1044680157097159803168475

theorem tailTrace_3051761 : CollatzResearch.WordTrace tailWord_3051761 prefixEnd_3051761 1044680157097159803168475 := by
  unfold tailWord_3051761
  simp only [CollatzResearch.WordTrace]
  refine ⟨111306867896998571129115137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74204578597999047419410091 111306867896998571129115137)
  ·
    refine ⟨83480150922748928346836353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111306867896998571129115137 83480150922748928346836353)
    ·
      refine ⟨62610113192061696260127265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83480150922748928346836353 62610113192061696260127265)
      ·
        refine ⟨46957584894046272195095449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62610113192061696260127265 46957584894046272195095449)
        ·
          refine ⟨35218188670534704146321587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46957584894046272195095449 35218188670534704146321587)
          ·
            refine ⟨52827283005802056219482381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35218188670534704146321587 52827283005802056219482381)
            ·
              refine ⟨19810231127175771082305893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52827283005802056219482381 19810231127175771082305893)
              ·
                refine ⟨3714418336345457077932355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19810231127175771082305893 3714418336345457077932355)
                ·
                  refine ⟨5571627504518185616898533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714418336345457077932355 5571627504518185616898533)
                  ·
                    refine ⟨1044680157097159803168475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571627504518185616898533 1044680157097159803168475)
                    ·
                      rfl

theorem cell22_3051761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3051761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051761 prefixEnd_3051761 := by exact prefixLift 3051761
  have htrace : WordTrace (prefixWord ++ tailWord_3051761) baseStart_3051761 baseEnd_3051761 := by
    simpa [prefixWord, tailWord_3051761, baseEnd_3051761] using wordTrace_append hprefix tailTrace_3051761
  have hstable : (prefixWord ++ tailWord_3051761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051761).length < 2 ^ (prefixWord ++ tailWord_3051761).sum := by decide
  have hdescent : baseEnd_3051761 < baseStart_3051761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051844 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3051844 : Nat := 118140960795 + 3051844 * 2 ^ 59
def prefixEnd_3051844 : Nat := 4983230072969 + 3 ^ 40 * 3051844 * 2
def baseEnd_3051844 : Nat := 348236189897791751114407

theorem tailTrace_3051844 : CollatzResearch.WordTrace tailWord_3051844 prefixEnd_3051844 348236189897791751114407 := by
  unfold tailWord_3051844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55654947577848938152193293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74206596770465250869591057 55654947577848938152193293)
  ·
    refine ⟨20870605341693351807072485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55654947577848938152193293 20870605341693351807072485)
    ·
      refine ⟨3913238501567503463826091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20870605341693351807072485 3913238501567503463826091)
      ·
        refine ⟨5869857752351255195739137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913238501567503463826091 5869857752351255195739137)
        ·
          refine ⟨4402393314263441396804353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5869857752351255195739137 4402393314263441396804353)
          ·
            refine ⟨3301794985697581047603265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402393314263441396804353 3301794985697581047603265)
            ·
              refine ⟨2476346239273185785702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301794985697581047603265 2476346239273185785702449)
              ·
                refine ⟨1857259679454889339276837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476346239273185785702449 1857259679454889339276837)
                ·
                  refine ⟨348236189897791751114407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857259679454889339276837 348236189897791751114407)
                  ·
                    rfl

theorem cell22_3051844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3051844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051844 prefixEnd_3051844 := by exact prefixLift 3051844
  have htrace : WordTrace (prefixWord ++ tailWord_3051844) baseStart_3051844 baseEnd_3051844 := by
    simpa [prefixWord, tailWord_3051844, baseEnd_3051844] using wordTrace_append hprefix tailTrace_3051844
  have hstable : (prefixWord ++ tailWord_3051844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051844).length < 2 ^ (prefixWord ++ tailWord_3051844).sum := by decide
  have hdescent : baseEnd_3051844 < baseStart_3051844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051928 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_3051928 : Nat := 118140960795 + 3051928 * 2 ^ 59
def prefixEnd_3051928 : Nat := 4983230072969 + 3 ^ 40 * 3051928 * 2
def baseEnd_3051928 : Nat := 348245774870009011414321

theorem tailTrace_3051928 : CollatzResearch.WordTrace tailWord_3051928 prefixEnd_3051928 348245774870009011414321 := by
  unfold tailWord_3051928
  simp only [CollatzResearch.WordTrace]
  refine ⟨55656479443696779325222219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74208639258262372433629625 55656479443696779325222219)
  ·
    refine ⟨83484719165545168987833329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55656479443696779325222219 83484719165545168987833329)
    ·
      refine ⟨62613539374158876740874997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83484719165545168987833329 62613539374158876740874997)
      ·
        refine ⟨5870019316327394694457031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62613539374158876740874997 5870019316327394694457031)
        ·
          refine ⟨8805028974491092041685547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5870019316327394694457031 8805028974491092041685547)
          ·
            refine ⟨13207543461736638062528321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805028974491092041685547 13207543461736638062528321)
            ·
              refine ⟨9905657596302478546896241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13207543461736638062528321 9905657596302478546896241)
              ·
                refine ⟨7429243197226858910172181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905657596302478546896241 7429243197226858910172181)
                ·
                  refine ⟨348245774870009011414321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7429243197226858910172181 348245774870009011414321)
                  ·
                    rfl

theorem cell22_3051928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_3051928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051928 prefixEnd_3051928 := by exact prefixLift 3051928
  have htrace : WordTrace (prefixWord ++ tailWord_3051928) baseStart_3051928 baseEnd_3051928 := by
    simpa [prefixWord, tailWord_3051928, baseEnd_3051928] using wordTrace_append hprefix tailTrace_3051928
  have hstable : (prefixWord ++ tailWord_3051928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051928).length < 2 ^ (prefixWord ++ tailWord_3051928).sum := by decide
  have hdescent : baseEnd_3051928 < baseStart_3051928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051930 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_3051930 : Nat := 118140960795 + 3051930 * 2 ^ 59
def prefixEnd_3051930 : Nat := 4983230072969 + 3 ^ 40 * 3051930 * 2
def baseEnd_3051930 : Nat := 1044738009250899695692957

theorem tailTrace_3051930 : CollatzResearch.WordTrace tailWord_3051930 prefixEnd_3051930 1044738009250899695692957 := by
  unfold tailWord_3051930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27828257958346578248004311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74208687888924208661344829 27828257958346578248004311)
  ·
    refine ⟨41742386937519867372006467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27828257958346578248004311 41742386937519867372006467)
    ·
      refine ⟨62613580406279801058009701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742386937519867372006467 62613580406279801058009701)
      ·
        refine ⟨11740046326177462698376819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62613580406279801058009701 11740046326177462698376819)
        ·
          refine ⟨17610069489266194047565229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740046326177462698376819 17610069489266194047565229)
          ·
            refine ⟨6603776058474822767836961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17610069489266194047565229 6603776058474822767836961)
            ·
              refine ⟨4952832043856117075877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603776058474822767836961 4952832043856117075877721)
              ·
                refine ⟨3714624032892087806908291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952832043856117075877721 3714624032892087806908291)
                ·
                  refine ⟨5571936049338131710362437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714624032892087806908291 5571936049338131710362437)
                  ·
                    refine ⟨1044738009250899695692957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571936049338131710362437 1044738009250899695692957)
                    ·
                      rfl

theorem cell22_3051930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_3051930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051930 prefixEnd_3051930 := by exact prefixLift 3051930
  have htrace : WordTrace (prefixWord ++ tailWord_3051930) baseStart_3051930 baseEnd_3051930 := by
    simpa [prefixWord, tailWord_3051930, baseEnd_3051930] using wordTrace_append hprefix tailTrace_3051930
  have hstable : (prefixWord ++ tailWord_3051930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051930).length < 2 ^ (prefixWord ++ tailWord_3051930).sum := by decide
  have hdescent : baseEnd_3051930 < baseStart_3051930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051941 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_3051941 : Nat := 118140960795 + 3051941 * 2 ^ 59
def prefixEnd_3051941 : Nat := 4983230072969 + 3 ^ 40 * 3051941 * 2
def baseEnd_3051941 : Nat := 1044741774775699333667923

theorem tailTrace_3051941 : CollatzResearch.WordTrace tailWord_3051941 prefixEnd_3051941 1044741774775699333667923 := by
  unfold tailWord_3051941
  simp only [CollatzResearch.WordTrace]
  refine ⟨111313433036346461870667677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74208955357564307913778451 111313433036346461870667677)
  ·
    refine ⟨41742537388629923201500379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111313433036346461870667677 41742537388629923201500379)
    ·
      refine ⟨62613806082944884802250569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742537388629923201500379 62613806082944884802250569)
      ·
        refine ⟨46960354562208663601687927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62613806082944884802250569 46960354562208663601687927)
        ·
          refine ⟨70440531843312995402531891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46960354562208663601687927 70440531843312995402531891)
          ·
            refine ⟨105660797764969493103797837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70440531843312995402531891 105660797764969493103797837)
            ·
              refine ⟨39622799161863559913924189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105660797764969493103797837 39622799161863559913924189)
              ·
                refine ⟨14858549685698834967721571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39622799161863559913924189 14858549685698834967721571)
                ·
                  refine ⟨22287824528548252451582357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14858549685698834967721571 22287824528548252451582357)
                  ·
                    refine ⟨1044741774775699333667923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22287824528548252451582357 1044741774775699333667923)
                    ·
                      rfl

theorem cell22_3051941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_3051941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3051941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3051941 prefixEnd_3051941 := by exact prefixLift 3051941
  have htrace : WordTrace (prefixWord ++ tailWord_3051941) baseStart_3051941 baseEnd_3051941 := by
    simpa [prefixWord, tailWord_3051941, baseEnd_3051941] using wordTrace_append hprefix tailTrace_3051941
  have hstable : (prefixWord ++ tailWord_3051941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051941).length < 2 ^ (prefixWord ++ tailWord_3051941).sum := by decide
  have hdescent : baseEnd_3051941 < baseStart_3051941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052033 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3052033 : Nat := 118140960795 + 3052033 * 2 ^ 59
def prefixEnd_3052033 : Nat := 4983230072969 + 3 ^ 40 * 3052033 * 2
def baseEnd_3052033 : Nat := 1044773268255841760367641

theorem tailTrace_3052033 : CollatzResearch.WordTrace tailWord_3052033 prefixEnd_3052033 1044773268255841760367641 := by
  unfold tailWord_3052033
  simp only [CollatzResearch.WordTrace]
  refine ⟨111316788552013161583016753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74211192368008774388677835 111316788552013161583016753)
  ·
    refine ⟨83487591414009871187262565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111316788552013161583016753 83487591414009871187262565)
    ·
      refine ⟨15653923390126850847611731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83487591414009871187262565 15653923390126850847611731)
      ·
        refine ⟨23480885085190276271417597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15653923390126850847611731 23480885085190276271417597)
        ·
          refine ⟨8805331906946353601781599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23480885085190276271417597 8805331906946353601781599)
          ·
            refine ⟨13207997860419530402672399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805331906946353601781599 13207997860419530402672399)
            ·
              refine ⟨19811996790629295604008599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13207997860419530402672399 19811996790629295604008599)
              ·
                refine ⟨29717995185943943406012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19811996790629295604008599 29717995185943943406012899)
                ·
                  refine ⟨44576992778915915109019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29717995185943943406012899 44576992778915915109019349)
                  ·
                    refine ⟨1044773268255841760367641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44576992778915915109019349 1044773268255841760367641)
                    ·
                      rfl

theorem cell22_3052033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3052033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052033 prefixEnd_3052033 := by exact prefixLift 3052033
  have htrace : WordTrace (prefixWord ++ tailWord_3052033) baseStart_3052033 baseEnd_3052033 := by
    simpa [prefixWord, tailWord_3052033, baseEnd_3052033] using wordTrace_append hprefix tailTrace_3052033
  have hstable : (prefixWord ++ tailWord_3052033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052033).length < 2 ^ (prefixWord ++ tailWord_3052033).sum := by decide
  have hdescent : baseEnd_3052033 < baseStart_3052033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052065 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3052065 : Nat := 118140960795 + 3052065 * 2 ^ 59
def prefixEnd_3052065 : Nat := 4983230072969 + 3 ^ 40 * 3052065 * 2
def baseEnd_3052065 : Nat := 1044784222509804343567543

theorem tailTrace_3052065 : CollatzResearch.WordTrace tailWord_3052065 prefixEnd_3052065 1044784222509804343567543 := by
  unfold tailWord_3052065
  simp only [CollatzResearch.WordTrace]
  refine ⟨111317955687897231048181649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74211970458598154032121099 111317955687897231048181649)
  ·
    refine ⟨83488466765922923286136237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111317955687897231048181649 83488466765922923286136237)
    ·
      refine ⟨31308175037221096232301089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83488466765922923286136237 31308175037221096232301089)
      ·
        refine ⟨23481131277915822174225817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31308175037221096232301089 23481131277915822174225817)
        ·
          refine ⟨17610848458436866630669363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23481131277915822174225817 17610848458436866630669363)
          ·
            refine ⟨26416272687655299946004045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17610848458436866630669363 26416272687655299946004045)
            ·
              refine ⟨9906102257870737479751517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26416272687655299946004045 9906102257870737479751517)
              ·
                refine ⟨3714788346701526554906819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9906102257870737479751517 3714788346701526554906819)
                ·
                  refine ⟨5572182520052289832360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714788346701526554906819 5572182520052289832360229)
                  ·
                    refine ⟨1044784222509804343567543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572182520052289832360229 1044784222509804343567543)
                    ·
                      rfl

theorem cell22_3052065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3052065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052065 prefixEnd_3052065 := by exact prefixLift 3052065
  have htrace : WordTrace (prefixWord ++ tailWord_3052065) baseStart_3052065 baseEnd_3052065 := by
    simpa [prefixWord, tailWord_3052065, baseEnd_3052065] using wordTrace_append hprefix tailTrace_3052065
  have hstable : (prefixWord ++ tailWord_3052065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052065).length < 2 ^ (prefixWord ++ tailWord_3052065).sum := by decide
  have hdescent : baseEnd_3052065 < baseStart_3052065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052080 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_3052080 : Nat := 118140960795 + 3052080 * 2 ^ 59
def prefixEnd_3052080 : Nat := 4983230072969 + 3 ^ 40 * 3052080 * 2
def baseEnd_3052080 : Nat := 348263119105449768147499

theorem tailTrace_3052080 : CollatzResearch.WordTrace tailWord_3052080 prefixEnd_3052080 348263119105449768147499 := by
  unfold tailWord_3052080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55659251391421444304988847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74212335188561925739985129 55659251391421444304988847)
  ·
    refine ⟨83488877087132166457483271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55659251391421444304988847 83488877087132166457483271)
    ·
      refine ⟨125233315630698249686224907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83488877087132166457483271 125233315630698249686224907)
      ·
        refine ⟨187849973446047374529337361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125233315630698249686224907 187849973446047374529337361)
        ·
          refine ⟨140887480084535530897003021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187849973446047374529337361 140887480084535530897003021)
          ·
            refine ⟨52832805031700824086376133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140887480084535530897003021 52832805031700824086376133)
            ·
              refine ⟨9906150943443904516195525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52832805031700824086376133 9906150943443904516195525)
              ·
                refine ⟨1857403301895732096786661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9906150943443904516195525 1857403301895732096786661)
                ·
                  refine ⟨348263119105449768147499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857403301895732096786661 348263119105449768147499)
                  ·
                    rfl

theorem cell22_3052080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_3052080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052080 prefixEnd_3052080 := by exact prefixLift 3052080
  have htrace : WordTrace (prefixWord ++ tailWord_3052080) baseStart_3052080 baseEnd_3052080 := by
    simpa [prefixWord, tailWord_3052080, baseEnd_3052080] using wordTrace_append hprefix tailTrace_3052080
  have hstable : (prefixWord ++ tailWord_3052080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052080).length < 2 ^ (prefixWord ++ tailWord_3052080).sum := by decide
  have hdescent : baseEnd_3052080 < baseStart_3052080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052108 : List Nat := [2, 2, 1, 3, 1, 2, 3, 8]
def baseStart_3052108 : Nat := 118140960795 + 3052108 * 2 ^ 59
def prefixEnd_3052108 : Nat := 4983230072969 + 3 ^ 40 * 3052108 * 2
def baseEnd_3052108 : Nat := 116088771365396284971379

theorem tailTrace_3052108 : CollatzResearch.WordTrace tailWord_3052108 prefixEnd_3052108 116088771365396284971379 := by
  unfold tailWord_3052108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55659762013370724695998489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74213016017827632927997985 55659762013370724695998489)
  ·
    refine ⟨41744821510028043521998867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55659762013370724695998489 41744821510028043521998867)
    ·
      refine ⟨62617232265042065282998301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41744821510028043521998867 62617232265042065282998301)
      ·
        refine ⟨23481462099390774481124363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62617232265042065282998301 23481462099390774481124363)
        ·
          refine ⟨35222193149086161721686545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23481462099390774481124363 35222193149086161721686545)
          ·
            refine ⟨26416644861814621291264909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35222193149086161721686545 26416644861814621291264909)
            ·
              refine ⟨9906241823180482984224341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26416644861814621291264909 9906241823180482984224341)
              ·
                refine ⟨116088771365396284971379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9906241823180482984224341 116088771365396284971379)
                ·
                  rfl

theorem cell22_3052108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_3052108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052108 prefixEnd_3052108 := by exact prefixLift 3052108
  have htrace : WordTrace (prefixWord ++ tailWord_3052108) baseStart_3052108 baseEnd_3052108 := by
    simpa [prefixWord, tailWord_3052108, baseEnd_3052108] using wordTrace_append hprefix tailTrace_3052108
  have hstable : (prefixWord ++ tailWord_3052108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052108).length < 2 ^ (prefixWord ++ tailWord_3052108).sum := by decide
  have hdescent : baseEnd_3052108 < baseStart_3052108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052146 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_3052146 : Nat := 118140960795 + 3052146 * 2 ^ 59
def prefixEnd_3052146 : Nat := 4983230072969 + 3 ^ 40 * 3052146 * 2
def baseEnd_3052146 : Nat := 1044811950465147132292295

theorem tailTrace_3052146 : CollatzResearch.WordTrace tailWord_3052146 prefixEnd_3052146 1044811950465147132292295 := by
  unfold tailWord_3052146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830227500150945470470073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74213940000402521254586861 27830227500150945470470073)
  ·
    refine ⟨20872670625113209102852555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27830227500150945470470073 20872670625113209102852555)
    ·
      refine ⟨31309005937669813654278833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20872670625113209102852555 31309005937669813654278833)
      ·
        refine ⟨23481754453252360240709125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31309005937669813654278833 23481754453252360240709125)
        ·
          refine ⟨4402828959984817545132961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23481754453252360240709125 4402828959984817545132961)
          ·
            refine ⟨3302121719988613158849721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402828959984817545132961 3302121719988613158849721)
            ·
              refine ⟨2476591289991459869137291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302121719988613158849721 2476591289991459869137291)
              ·
                refine ⟨3714886934987189803705937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476591289991459869137291 3714886934987189803705937)
                ·
                  refine ⟨2786165201240392352779453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714886934987189803705937 2786165201240392352779453)
                  ·
                    refine ⟨1044811950465147132292295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786165201240392352779453 1044811950465147132292295)
                    ·
                      rfl

theorem cell22_3052146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_3052146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052146 prefixEnd_3052146 := by exact prefixLift 3052146
  have htrace : WordTrace (prefixWord ++ tailWord_3052146) baseStart_3052146 baseEnd_3052146 := by
    simpa [prefixWord, tailWord_3052146, baseEnd_3052146] using wordTrace_append hprefix tailTrace_3052146
  have hstable : (prefixWord ++ tailWord_3052146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052146).length < 2 ^ (prefixWord ++ tailWord_3052146).sum := by decide
  have hdescent : baseEnd_3052146 < baseStart_3052146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052174 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3052174 : Nat := 118140960795 + 3052174 * 2 ^ 59
def prefixEnd_3052174 : Nat := 4983230072969 + 3 ^ 40 * 3052174 * 2
def baseEnd_3052174 : Nat := 1044821535437364392592209

theorem tailTrace_3052174 : CollatzResearch.WordTrace tailWord_3052174 prefixEnd_3052174 1044821535437364392592209 := by
  unfold tailWord_3052174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915241405562792832987447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74214620829668228442599717 13915241405562792832987447)
  ·
    refine ⟨20872862108344189249481171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13915241405562792832987447 20872862108344189249481171)
    ·
      refine ⟨31309293162516283874221757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20872862108344189249481171 31309293162516283874221757)
      ·
        refine ⟨11740984935943606452833159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31309293162516283874221757 11740984935943606452833159)
        ·
          refine ⟨17611477403915409679249739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740984935943606452833159 17611477403915409679249739)
          ·
            refine ⟨26417216105873114518874609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17611477403915409679249739 26417216105873114518874609)
            ·
              refine ⟨19812912079404835889155957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26417216105873114518874609 19812912079404835889155957)
              ·
                refine ⟨1857460507444203364608371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19812912079404835889155957 1857460507444203364608371)
                ·
                  refine ⟨2786190761166305046912557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857460507444203364608371 2786190761166305046912557)
                  ·
                    refine ⟨1044821535437364392592209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786190761166305046912557 1044821535437364392592209)
                    ·
                      rfl

theorem cell22_3052174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3052174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052174 prefixEnd_3052174 := by exact prefixLift 3052174
  have htrace : WordTrace (prefixWord ++ tailWord_3052174) baseStart_3052174 baseEnd_3052174 := by
    simpa [prefixWord, tailWord_3052174, baseEnd_3052174] using wordTrace_append hprefix tailTrace_3052174
  have hstable : (prefixWord ++ tailWord_3052174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052174).length < 2 ^ (prefixWord ++ tailWord_3052174).sum := by decide
  have hdescent : baseEnd_3052174 < baseStart_3052174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052232 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_3052232 : Nat := 118140960795 + 3052232 * 2 ^ 59
def prefixEnd_3052232 : Nat := 4983230072969 + 3 ^ 40 * 3052232 * 2
def baseEnd_3052232 : Nat := 348280463340890524880677

theorem tailTrace_3052232 : CollatzResearch.WordTrace tailWord_3052232 prefixEnd_3052232 348280463340890524880677 := by
  unfold tailWord_3052232
  simp only [CollatzResearch.WordTrace]
  refine ⟨55662023339146109284755475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74216031118861479046340633 55662023339146109284755475)
  ·
    refine ⟨83493035008719163927133213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55662023339146109284755475 83493035008719163927133213)
    ·
      refine ⟨31309888128269686472674955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83493035008719163927133213 31309888128269686472674955)
      ·
        refine ⟨46964832192404529709012433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31309888128269686472674955 46964832192404529709012433)
        ·
          refine ⟨35223624144303397281759325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46964832192404529709012433 35223624144303397281759325)
          ·
            refine ⟨13208859054113773980659747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35223624144303397281759325 13208859054113773980659747)
            ·
              refine ⟨19813288581170660970989621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13208859054113773980659747 19813288581170660970989621)
              ·
                refine ⟨1857495804484749466030277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19813288581170660970989621 1857495804484749466030277)
                ·
                  refine ⟨348280463340890524880677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857495804484749466030277 348280463340890524880677)
                  ·
                    rfl

theorem cell22_3052232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_3052232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052232 prefixEnd_3052232 := by exact prefixLift 3052232
  have htrace : WordTrace (prefixWord ++ tailWord_3052232) baseStart_3052232 baseEnd_3052232 := by
    simpa [prefixWord, tailWord_3052232, baseEnd_3052232] using wordTrace_append hprefix tailTrace_3052232
  have hstable : (prefixWord ++ tailWord_3052232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052232).length < 2 ^ (prefixWord ++ tailWord_3052232).sum := by decide
  have hdescent : baseEnd_3052232 < baseStart_3052232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052234 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_3052234 : Nat := 118140960795 + 3052234 * 2 ^ 59
def prefixEnd_3052234 : Nat := 4983230072969 + 3 ^ 40 * 3052234 * 2
def baseEnd_3052234 : Nat := 1044842074663544236092025

theorem tailTrace_3052234 : CollatzResearch.WordTrace tailWord_3052234 prefixEnd_3052234 1044842074663544236092025 := by
  unfold tailWord_3052234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27831029906071243227770939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74216079749523315274055837 27831029906071243227770939)
  ·
    refine ⟨41746544859106864841656409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27831029906071243227770939 41746544859106864841656409)
    ·
      refine ⟨31309908644330148631242307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41746544859106864841656409 31309908644330148631242307)
      ·
        refine ⟨46964862966495222946863461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31309908644330148631242307 46964862966495222946863461)
        ·
          refine ⟨8805911806217854302536899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46964862966495222946863461 8805911806217854302536899)
          ·
            refine ⟨13208867709326781453805349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805911806217854302536899 13208867709326781453805349)
            ·
              refine ⟨2476662695498771522588503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13208867709326781453805349 2476662695498771522588503)
              ·
                refine ⟨3714994043248157283882755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476662695498771522588503 3714994043248157283882755)
                ·
                  refine ⟨5572491064872235925824133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714994043248157283882755 5572491064872235925824133)
                  ·
                    refine ⟨1044842074663544236092025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572491064872235925824133 1044842074663544236092025)
                    ·
                      rfl

theorem cell22_3052234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_3052234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052234 prefixEnd_3052234 := by exact prefixLift 3052234
  have htrace : WordTrace (prefixWord ++ tailWord_3052234) baseStart_3052234 baseEnd_3052234 := by
    simpa [prefixWord, tailWord_3052234, baseEnd_3052234] using wordTrace_append hprefix tailTrace_3052234
  have hstable : (prefixWord ++ tailWord_3052234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052234).length < 2 ^ (prefixWord ++ tailWord_3052234).sum := by decide
  have hdescent : baseEnd_3052234 < baseStart_3052234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052247 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 4, 3]
def baseStart_3052247 : Nat := 118140960795 + 3052247 * 2 ^ 59
def prefixEnd_3052247 : Nat := 4983230072969 + 3 ^ 40 * 3052247 * 2
def baseEnd_3052247 : Nat := 1044846524829216535516985

theorem tailTrace_3052247 : CollatzResearch.WordTrace tailWord_3052247 prefixEnd_3052247 1044846524829216535516985 := by
  unfold tailWord_3052247
  simp only [CollatzResearch.WordTrace]
  refine ⟨111324593773237876131306995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74216395848825250754204663 111324593773237876131306995)
  ·
    refine ⟨166986890659856814196960493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111324593773237876131306995 166986890659856814196960493)
    ·
      refine ⟨62620083997446305323860185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166986890659856814196960493 62620083997446305323860185)
      ·
        refine ⟨46965062998084728992895139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62620083997446305323860185 46965062998084728992895139)
        ·
          refine ⟨70447594497127093489342709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46965062998084728992895139 70447594497127093489342709)
          ·
            refine ⟨6604461984105665014625879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70447594497127093489342709 6604461984105665014625879)
            ·
              refine ⟨9906692976158497521938819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604461984105665014625879 9906692976158497521938819)
              ·
                refine ⟨14860039464237746282908229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906692976158497521938819 14860039464237746282908229)
                ·
                  refine ⟨2786257399544577428045293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14860039464237746282908229 2786257399544577428045293)
                  ·
                    refine ⟨1044846524829216535516985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786257399544577428045293 1044846524829216535516985)
                    ·
                      rfl

theorem cell22_3052247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_3052247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052247 prefixEnd_3052247 := by exact prefixLift 3052247
  have htrace : WordTrace (prefixWord ++ tailWord_3052247) baseStart_3052247 baseEnd_3052247 := by
    simpa [prefixWord, tailWord_3052247, baseEnd_3052247] using wordTrace_append hprefix tailTrace_3052247
  have hstable : (prefixWord ++ tailWord_3052247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052247).length < 2 ^ (prefixWord ++ tailWord_3052247).sum := by decide
  have hdescent : baseEnd_3052247 < baseStart_3052247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052264 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3052264 : Nat := 118140960795 + 3052264 * 2 ^ 59
def prefixEnd_3052264 : Nat := 4983230072969 + 3 ^ 40 * 3052264 * 2
def baseEnd_3052264 : Nat := 1044852344276634157841933

theorem tailTrace_3052264 : CollatzResearch.WordTrace tailWord_3052264 prefixEnd_3052264 1044852344276634157841933 := by
  unfold tailWord_3052264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55662606907088144017337923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74216809209450858689783897 55662606907088144017337923)
  ·
    refine ⟨83493910360632216026006885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55662606907088144017337923 83493910360632216026006885)
    ·
      refine ⟨15655108192618540504876291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83493910360632216026006885 15655108192618540504876291)
      ·
        refine ⟨23482662288927810757314437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15655108192618540504876291 23482662288927810757314437)
        ·
          refine ⟨4402999179173964516996457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23482662288927810757314437 4402999179173964516996457)
          ·
            refine ⟨3302249384380473387747343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402999179173964516996457 3302249384380473387747343)
            ·
              refine ⟨4953374076570710081621015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302249384380473387747343 4953374076570710081621015)
              ·
                refine ⟨7430061114856065122431523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953374076570710081621015 7430061114856065122431523)
                ·
                  refine ⟨11145091672284097683647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430061114856065122431523 11145091672284097683647285)
                  ·
                    refine ⟨1044852344276634157841933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11145091672284097683647285 1044852344276634157841933)
                    ·
                      rfl

theorem cell22_3052264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3052264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052264 prefixEnd_3052264 := by exact prefixLift 3052264
  have htrace : WordTrace (prefixWord ++ tailWord_3052264) baseStart_3052264 baseEnd_3052264 := by
    simpa [prefixWord, tailWord_3052264, baseEnd_3052264] using wordTrace_append hprefix tailTrace_3052264
  have hstable : (prefixWord ++ tailWord_3052264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052264).length < 2 ^ (prefixWord ++ tailWord_3052264).sum := by decide
  have hdescent : baseEnd_3052264 < baseStart_3052264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052305 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 7]
def baseStart_3052305 : Nat := 118140960795 + 3052305 * 2 ^ 59
def prefixEnd_3052305 : Nat := 4983230072969 + 3 ^ 40 * 3052305 * 2
def baseEnd_3052305 : Nat := 348288793138174572522269

theorem tailTrace_3052305 : CollatzResearch.WordTrace tailWord_3052305 prefixEnd_3052305 348288793138174572522269 := by
  unfold tailWord_3052305
  simp only [CollatzResearch.WordTrace]
  refine ⟨111326709207027752036918369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74217806138018501357945579 111326709207027752036918369)
  ·
    refine ⟨83495031905270814027688777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111326709207027752036918369 83495031905270814027688777)
    ·
      refine ⟨62621273928953110520766583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83495031905270814027688777 62621273928953110520766583)
      ·
        refine ⟨93931910893429665781149875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62621273928953110520766583 93931910893429665781149875)
        ·
          refine ⟨140897866340144498671724813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93931910893429665781149875 140897866340144498671724813)
          ·
            refine ⟨52836699877554187001896805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140897866340144498671724813 52836699877554187001896805)
            ·
              refine ⟨9906881227041410062855651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52836699877554187001896805 9906881227041410062855651)
              ·
                refine ⟨14860321840562115094283477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906881227041410062855651 14860321840562115094283477)
                ·
                  refine ⟨348288793138174572522269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14860321840562115094283477 348288793138174572522269)
                  ·
                    rfl

theorem cell22_3052305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_3052305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052305 prefixEnd_3052305 := by exact prefixLift 3052305
  have htrace : WordTrace (prefixWord ++ tailWord_3052305) baseStart_3052305 baseEnd_3052305 := by
    simpa [prefixWord, tailWord_3052305, baseEnd_3052305] using wordTrace_append hprefix tailTrace_3052305
  have hstable : (prefixWord ++ tailWord_3052305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052305).length < 2 ^ (prefixWord ++ tailWord_3052305).sum := by decide
  have hdescent : baseEnd_3052305 < baseStart_3052305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052352 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_3052352 : Nat := 118140960795 + 3052352 * 2 ^ 59
def prefixEnd_3052352 : Nat := 4983230072969 + 3 ^ 40 * 3052352 * 2
def baseEnd_3052352 : Nat := 1044882468475031261641663

theorem tailTrace_3052352 : CollatzResearch.WordTrace tailWord_3052352 prefixEnd_3052352 1044882468475031261641663 := by
  unfold tailWord_3052352
  simp only [CollatzResearch.WordTrace]
  refine ⟨55664211718928739531939655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74218948958571652709252873 55664211718928739531939655)
  ·
    refine ⟨83496317578393109297909483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55664211718928739531939655 83496317578393109297909483)
    ·
      refine ⟨125244476367589663946864225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83496317578393109297909483 125244476367589663946864225)
      ·
        refine ⟨93933357275692247960148169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125244476367589663946864225 93933357275692247960148169)
        ·
          refine ⟨70450017956769185970111127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93933357275692247960148169 70450017956769185970111127)
          ·
            refine ⟨105675026935153778955166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70450017956769185970111127 105675026935153778955166691)
            ·
              refine ⟨158512540402730668432750037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105675026935153778955166691 158512540402730668432750037)
              ·
                refine ⟨3715137665689000041392579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158512540402730668432750037 3715137665689000041392579)
                ·
                  refine ⟨5572706498533500062088869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715137665689000041392579 5572706498533500062088869)
                  ·
                    refine ⟨1044882468475031261641663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572706498533500062088869 1044882468475031261641663)
                    ·
                      rfl

theorem cell22_3052352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_3052352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052352 prefixEnd_3052352 := by exact prefixLift 3052352
  have htrace : WordTrace (prefixWord ++ tailWord_3052352) baseStart_3052352 baseEnd_3052352 := by
    simpa [prefixWord, tailWord_3052352, baseEnd_3052352] using wordTrace_append hprefix tailTrace_3052352
  have hstable : (prefixWord ++ tailWord_3052352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052352).length < 2 ^ (prefixWord ++ tailWord_3052352).sum := by decide
  have hdescent : baseEnd_3052352 < baseStart_3052352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052395 : List Nat := [1, 1, 1, 1, 2, 2, 4, 10]
def baseStart_3052395 : Nat := 118140960795 + 3052395 * 2 ^ 59
def prefixEnd_3052395 : Nat := 4983230072969 + 3 ^ 40 * 3052395 * 2
def baseEnd_3052395 : Nat := 116099687583754831424059

theorem tailTrace_3052395 : CollatzResearch.WordTrace tailWord_3052395 prefixEnd_3052395 116099687583754831424059 := by
  unfold tailWord_3052395
  simp only [CollatzResearch.WordTrace]
  refine ⟨111329991776701697407694639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74219994517801131605129759 111329991776701697407694639)
  ·
    refine ⟨166994987665052546111541959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111329991776701697407694639 166994987665052546111541959)
    ·
      refine ⟨250492481497578819167312939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166994987665052546111541959 250492481497578819167312939)
      ·
        refine ⟨375738722246368228750969409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250492481497578819167312939 375738722246368228750969409)
        ·
          refine ⟨281804041684776171563227057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375738722246368228750969409 281804041684776171563227057)
          ·
            refine ⟨211353031263582128672420293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281804041684776171563227057 211353031263582128672420293)
            ·
              refine ⟨39628693361921649126078805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211353031263582128672420293 39628693361921649126078805)
              ·
                refine ⟨116099687583754831424059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39628693361921649126078805 116099687583754831424059)
                ·
                  rfl

theorem cell22_3052395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_3052395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052395 prefixEnd_3052395 := by exact prefixLift 3052395
  have htrace : WordTrace (prefixWord ++ tailWord_3052395) baseStart_3052395 baseEnd_3052395 := by
    simpa [prefixWord, tailWord_3052395, baseEnd_3052395] using wordTrace_append hprefix tailTrace_3052395
  have hstable : (prefixWord ++ tailWord_3052395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052395).length < 2 ^ (prefixWord ++ tailWord_3052395).sum := by decide
  have hdescent : baseEnd_3052395 < baseStart_3052395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052418 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3052418 : Nat := 118140960795 + 3052418 * 2 ^ 59
def prefixEnd_3052418 : Nat := 4983230072969 + 3 ^ 40 * 3052418 * 2
def baseEnd_3052418 : Nat := 348301687207943029830487

theorem tailTrace_3052418 : CollatzResearch.WordTrace tailWord_3052418 prefixEnd_3052418 348301687207943029830487 := by
  unfold tailWord_3052418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27832707663904593083945477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74220553770412248223854605 27832707663904593083945477)
  ·
    refine ⟨5218632686982111203239777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27832707663904593083945477 5218632686982111203239777)
    ·
      refine ⟨3913974515236583402429833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5218632686982111203239777 3913974515236583402429833)
      ·
        refine ⟨2935480886427437551822375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3913974515236583402429833 2935480886427437551822375)
        ·
          refine ⟨4403221329641156327733563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935480886427437551822375 4403221329641156327733563)
          ·
            refine ⟨6604831994461734491600345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403221329641156327733563 6604831994461734491600345)
            ·
              refine ⟨4953623995846300868700259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6604831994461734491600345 4953623995846300868700259)
              ·
                refine ⟨7430435993769451303050389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953623995846300868700259 7430435993769451303050389)
                ·
                  refine ⟨348301687207943029830487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7430435993769451303050389 348301687207943029830487)
                  ·
                    rfl

theorem cell22_3052418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3052418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052418 prefixEnd_3052418 := by exact prefixLift 3052418
  have htrace : WordTrace (prefixWord ++ tailWord_3052418) baseStart_3052418 baseEnd_3052418 := by
    simpa [prefixWord, tailWord_3052418, baseEnd_3052418] using wordTrace_append hprefix tailTrace_3052418
  have hstable : (prefixWord ++ tailWord_3052418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052418).length < 2 ^ (prefixWord ++ tailWord_3052418).sum := by decide
  have hdescent : baseEnd_3052418 < baseStart_3052418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052491 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 5]
def baseStart_3052491 : Nat := 118140960795 + 3052491 * 2 ^ 59
def prefixEnd_3052491 : Nat := 4983230072969 + 3 ^ 40 * 3052491 * 2
def baseEnd_3052491 : Nat := 348310017005227077472079

theorem tailTrace_3052491 : CollatzResearch.WordTrace tailWord_3052491 prefixEnd_3052491 348310017005227077472079 := by
  unfold tailWord_3052491
  simp only [CollatzResearch.WordTrace]
  refine ⟨111333493184353905803189327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74222328789569270535459551 111333493184353905803189327)
  ·
    refine ⟨167000239776530858704783991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111333493184353905803189327 167000239776530858704783991)
    ·
      refine ⟨250500359664796288057175987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167000239776530858704783991 250500359664796288057175987)
      ·
        refine ⟨375750539497194432085763981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250500359664796288057175987 375750539497194432085763981)
        ·
          refine ⟨140906452311447912032161493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375750539497194432085763981 140906452311447912032161493)
          ·
            refine ⟨3302494976049560438253785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 140906452311447912032161493 3302494976049560438253785)
            ·
              refine ⟨2476871232037170328690339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302494976049560438253785 2476871232037170328690339)
              ·
                refine ⟨3715306848055755493035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476871232037170328690339 3715306848055755493035509)
                ·
                  refine ⟨348310017005227077472079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3715306848055755493035509 348310017005227077472079)
                  ·
                    rfl

theorem cell22_3052491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 5].length) (baseStart_3052491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052491 prefixEnd_3052491 := by exact prefixLift 3052491
  have htrace : WordTrace (prefixWord ++ tailWord_3052491) baseStart_3052491 baseEnd_3052491 := by
    simpa [prefixWord, tailWord_3052491, baseEnd_3052491] using wordTrace_append hprefix tailTrace_3052491
  have hstable : (prefixWord ++ tailWord_3052491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052491).length < 2 ^ (prefixWord ++ tailWord_3052491).sum := by decide
  have hdescent : baseEnd_3052491 < baseStart_3052491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052504 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_3052504 : Nat := 118140960795 + 3052504 * 2 ^ 59
def prefixEnd_3052504 : Nat := 4983230072969 + 3 ^ 40 * 3052504 * 2
def baseEnd_3052504 : Nat := 1044934501181353531841197

theorem tailTrace_3052504 : CollatzResearch.WordTrace tailWord_3052504 prefixEnd_3052504 1044934501181353531841197 := by
  unfold tailWord_3052504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55666983666653404511706283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74222644888871206015608377 55666983666653404511706283)
  ·
    refine ⟨83500475499980106767559425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55666983666653404511706283 83500475499980106767559425)
    ·
      refine ⟨62625356624985080075669569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83500475499980106767559425 62625356624985080075669569)
      ·
        refine ⟨46969017468738810056752177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62625356624985080075669569 46969017468738810056752177)
        ·
          refine ⟨35226763101554107542564133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46969017468738810056752177 35226763101554107542564133)
          ·
            refine ⟨6605018081541395164230775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35226763101554107542564133 6605018081541395164230775)
            ·
              refine ⟨9907527122312092746346163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605018081541395164230775 9907527122312092746346163)
              ·
                refine ⟨14861290683468139119519245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907527122312092746346163 14861290683468139119519245)
                ·
                  refine ⟨5572984006300552169819717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14861290683468139119519245 5572984006300552169819717)
                  ·
                    refine ⟨1044934501181353531841197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572984006300552169819717 1044934501181353531841197)
                    ·
                      rfl

theorem cell22_3052504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_3052504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052504 prefixEnd_3052504 := by exact prefixLift 3052504
  have htrace : WordTrace (prefixWord ++ tailWord_3052504) baseStart_3052504 baseEnd_3052504 := by
    simpa [prefixWord, tailWord_3052504, baseEnd_3052504] using wordTrace_append hprefix tailTrace_3052504
  have hstable : (prefixWord ++ tailWord_3052504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052504).length < 2 ^ (prefixWord ++ tailWord_3052504).sum := by decide
  have hdescent : baseEnd_3052504 < baseStart_3052504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052551 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3052551 : Nat := 118140960795 + 3052551 * 2 ^ 59
def prefixEnd_3052551 : Nat := 4983230072969 + 3 ^ 40 * 3052551 * 2
def baseEnd_3052551 : Nat := 1044950590241861075916053

theorem tailTrace_3052551 : CollatzResearch.WordTrace tailWord_3052551 prefixEnd_3052551 1044950590241861075916053 := by
  unfold tailWord_3052551
  simp only [CollatzResearch.WordTrace]
  refine ⟨111335681564136536050373507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74223787709424357366915671 111335681564136536050373507)
  ·
    refine ⟨167003522346204804075560261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111335681564136536050373507 167003522346204804075560261)
    ·
      refine ⟨31313160439913400764167549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167003522346204804075560261 31313160439913400764167549)
      ·
        refine ⟨11742435164967525286562831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31313160439913400764167549 11742435164967525286562831)
        ·
          refine ⟨17613652747451287929844247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742435164967525286562831 17613652747451287929844247)
          ·
            refine ⟨26420479121176931894766371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613652747451287929844247 26420479121176931894766371)
            ·
              refine ⟨39630718681765397842149557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26420479121176931894766371 39630718681765397842149557)
              ·
                refine ⟨3715379876415506047701521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39630718681765397842149557 3715379876415506047701521)
                ·
                  refine ⟨2786534907311629535776141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715379876415506047701521 2786534907311629535776141)
                  ·
                    refine ⟨1044950590241861075916053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786534907311629535776141 1044950590241861075916053)
                    ·
                      rfl

theorem cell22_3052551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3052551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052551 prefixEnd_3052551 := by exact prefixLift 3052551
  have htrace : WordTrace (prefixWord ++ tailWord_3052551) baseStart_3052551 baseEnd_3052551 := by
    simpa [prefixWord, tailWord_3052551, baseEnd_3052551] using wordTrace_append hprefix tailTrace_3052551
  have hstable : (prefixWord ++ tailWord_3052551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052551).length < 2 ^ (prefixWord ++ tailWord_3052551).sum := by decide
  have hdescent : baseEnd_3052551 < baseStart_3052551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052673 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3052673 : Nat := 118140960795 + 3052673 * 2 ^ 59
def prefixEnd_3052673 : Nat := 4983230072969 + 3 ^ 40 * 3052673 * 2
def baseEnd_3052673 : Nat := 1044992353335093424365679

theorem tailTrace_3052673 : CollatzResearch.WordTrace tailWord_3052673 prefixEnd_3052673 1044992353335093424365679 := by
  unfold tailWord_3052673
  simp only [CollatzResearch.WordTrace]
  refine ⟨111340131269694550886314673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74226754179796367257543115 111340131269694550886314673)
  ·
    refine ⟨83505098452270913164736005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111340131269694550886314673 83505098452270913164736005)
    ·
      refine ⟨15657205959800796218388001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83505098452270913164736005 15657205959800796218388001)
      ·
        refine ⟨11742904469850597163791001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15657205959800796218388001 11742904469850597163791001)
        ·
          refine ⟨8807178352387947872843251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742904469850597163791001 8807178352387947872843251)
          ·
            refine ⟨13210767528581921809264877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807178352387947872843251 13210767528581921809264877)
            ·
              refine ⟨4954037823218220678474329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13210767528581921809264877 4954037823218220678474329)
              ·
                refine ⟨3715528367413665508855747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954037823218220678474329 3715528367413665508855747)
                ·
                  refine ⟨5573292551120498263283621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715528367413665508855747 5573292551120498263283621)
                  ·
                    refine ⟨1044992353335093424365679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573292551120498263283621 1044992353335093424365679)
                    ·
                      rfl

theorem cell22_3052673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3052673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052673 prefixEnd_3052673 := by exact prefixLift 3052673
  have htrace : WordTrace (prefixWord ++ tailWord_3052673) baseStart_3052673 baseEnd_3052673 := by
    simpa [prefixWord, tailWord_3052673, baseEnd_3052673] using wordTrace_append hprefix tailTrace_3052673
  have hstable : (prefixWord ++ tailWord_3052673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052673).length < 2 ^ (prefixWord ++ tailWord_3052673).sum := by decide
  have hdescent : baseEnd_3052673 < baseStart_3052673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052684 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_3052684 : Nat := 118140960795 + 3052684 * 2 ^ 59
def prefixEnd_3052684 : Nat := 4983230072969 + 3 ^ 40 * 3052684 * 2
def baseEnd_3052684 : Nat := 1044996118859893062340645

theorem tailTrace_3052684 : CollatzResearch.WordTrace tailWord_3052684 prefixEnd_3052684 1044996118859893062340645 := by
  unfold tailWord_3052684
  simp only [CollatzResearch.WordTrace]
  refine ⟨55670266236327349882482553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74227021648436466509976737 55670266236327349882482553)
  ·
    refine ⟨41752699677245512411861915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55670266236327349882482553 41752699677245512411861915)
    ·
      refine ⟨62629049515868268617792873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41752699677245512411861915 62629049515868268617792873)
      ·
        refine ⟨46971787136901201463344655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62629049515868268617792873 46971787136901201463344655)
        ·
          refine ⟨70457680705351802195016983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46971787136901201463344655 70457680705351802195016983)
          ·
            refine ⟨105686521058027703292525475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70457680705351802195016983 105686521058027703292525475)
            ·
              refine ⟨158529781587041554938788213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105686521058027703292525475 158529781587041554938788213)
              ·
                refine ⟨14862167023785145775511395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158529781587041554938788213 14862167023785145775511395)
                ·
                  refine ⟨22293250535677718663267093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14862167023785145775511395 22293250535677718663267093)
                  ·
                    refine ⟨1044996118859893062340645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22293250535677718663267093 1044996118859893062340645)
                    ·
                      rfl

theorem cell22_3052684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_3052684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052684 prefixEnd_3052684 := by exact prefixLift 3052684
  have htrace : WordTrace (prefixWord ++ tailWord_3052684) baseStart_3052684 baseEnd_3052684 := by
    simpa [prefixWord, tailWord_3052684, baseEnd_3052684] using wordTrace_append hprefix tailTrace_3052684
  have hstable : (prefixWord ++ tailWord_3052684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052684).length < 2 ^ (prefixWord ++ tailWord_3052684).sum := by decide
  have hdescent : baseEnd_3052684 < baseStart_3052684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052686 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3052686 : Nat := 118140960795 + 3052686 * 2 ^ 59
def prefixEnd_3052686 : Nat := 4983230072969 + 3 ^ 40 * 3052686 * 2
def baseEnd_3052686 : Nat := 1044996803500765723790639

theorem tailTrace_3052686 : CollatzResearch.WordTrace tailWord_3052686 prefixEnd_3052686 1044996803500765723790639 := by
  unfold tailWord_3052686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917575677330931763317239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74227070279098302737691941 13917575677330931763317239)
  ·
    refine ⟨20876363515996397644975859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917575677330931763317239 20876363515996397644975859)
    ·
      refine ⟨31314545273994596467463789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20876363515996397644975859 31314545273994596467463789)
      ·
        refine ⟨11742954477747973675298921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31314545273994596467463789 11742954477747973675298921)
        ·
          refine ⟨8807215858310980256474191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742954477747973675298921 8807215858310980256474191)
          ·
            refine ⟨13210823787466470384711287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807215858310980256474191 13210823787466470384711287)
            ·
              refine ⟨19816235681199705577066931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210823787466470384711287 19816235681199705577066931)
              ·
                refine ⟨29724353521799558365600397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19816235681199705577066931 29724353521799558365600397)
                ·
                  refine ⟨11146632570674834387100149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29724353521799558365600397 11146632570674834387100149)
                  ·
                    refine ⟨1044996803500765723790639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11146632570674834387100149 1044996803500765723790639)
                    ·
                      rfl

theorem cell22_3052686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3052686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052686 prefixEnd_3052686 := by exact prefixLift 3052686
  have htrace : WordTrace (prefixWord ++ tailWord_3052686) baseStart_3052686 baseEnd_3052686 := by
    simpa [prefixWord, tailWord_3052686, baseEnd_3052686] using wordTrace_append hprefix tailTrace_3052686
  have hstable : (prefixWord ++ tailWord_3052686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052686).length < 2 ^ (prefixWord ++ tailWord_3052686).sum := by decide
  have hdescent : baseEnd_3052686 < baseStart_3052686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052690 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3052690 : Nat := 118140960795 + 3052690 * 2 ^ 59
def prefixEnd_3052690 : Nat := 4983230072969 + 3 ^ 40 * 3052690 * 2
def baseEnd_3052690 : Nat := 1044998172782511046690627

theorem tailTrace_3052690 : CollatzResearch.WordTrace tailWord_3052690 prefixEnd_3052690 1044998172782511046690627 := by
  unfold tailWord_3052690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835187827658240697420881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74227167540421975193122349 27835187827658240697420881)
  ·
    refine ⟨20876390870743680523065661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27835187827658240697420881 20876390870743680523065661)
    ·
      refine ⟨7828646576528880196149623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20876390870743680523065661 7828646576528880196149623)
      ·
        refine ⟨11742969864793320294224435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828646576528880196149623 11742969864793320294224435)
        ·
          refine ⟨17614454797189980441336653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742969864793320294224435 17614454797189980441336653)
          ·
            refine ⟨6605420548946242665501245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17614454797189980441336653 6605420548946242665501245)
            ·
              refine ⟨2477032705854840999562967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605420548946242665501245 2477032705854840999562967)
              ·
                refine ⟨3715549058782261499344451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477032705854840999562967 3715549058782261499344451)
                ·
                  refine ⟨5573323588173392249016677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715549058782261499344451 5573323588173392249016677)
                  ·
                    refine ⟨1044998172782511046690627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573323588173392249016677 1044998172782511046690627)
                    ·
                      rfl

theorem cell22_3052690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3052690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052690 prefixEnd_3052690 := by exact prefixLift 3052690
  have htrace : WordTrace (prefixWord ++ tailWord_3052690) baseStart_3052690 baseEnd_3052690 := by
    simpa [prefixWord, tailWord_3052690, baseEnd_3052690] using wordTrace_append hprefix tailTrace_3052690
  have hstable : (prefixWord ++ tailWord_3052690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052690).length < 2 ^ (prefixWord ++ tailWord_3052690).sum := by decide
  have hdescent : baseEnd_3052690 < baseStart_3052690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052701 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3052701 : Nat := 118140960795 + 3052701 * 2 ^ 59
def prefixEnd_3052701 : Nat := 4983230072969 + 3 ^ 40 * 3052701 * 2
def baseEnd_3052701 : Nat := 1045001938307310684665593

theorem tailTrace_3052701 : CollatzResearch.WordTrace tailWord_3052701 prefixEnd_3052701 1045001938307310684665593 := by
  unfold tailWord_3052701
  simp only [CollatzResearch.WordTrace]
  refine ⟨111341152513593111668333957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74227435009062074445555971 111341152513593111668333957)
  ·
    refine ⟨20876466096298708437812617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111341152513593111668333957 20876466096298708437812617)
    ·
      refine ⟨15657349572224031328359463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20876466096298708437812617 15657349572224031328359463)
      ·
        refine ⟨23486024358336046992539195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15657349572224031328359463 23486024358336046992539195)
        ·
          refine ⟨35229036537504070488808793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23486024358336046992539195 35229036537504070488808793)
          ·
            refine ⟨26421777403128052866606595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35229036537504070488808793 26421777403128052866606595)
            ·
              refine ⟨39632666104692079299909893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26421777403128052866606595 39632666104692079299909893)
              ·
                refine ⟨7431124894629764868733105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39632666104692079299909893 7431124894629764868733105)
                ·
                  refine ⟨5573343670972323651549829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7431124894629764868733105 5573343670972323651549829)
                  ·
                    refine ⟨1045001938307310684665593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573343670972323651549829 1045001938307310684665593)
                    ·
                      rfl

theorem cell22_3052701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3052701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052701 prefixEnd_3052701 := by exact prefixLift 3052701
  have htrace : WordTrace (prefixWord ++ tailWord_3052701) baseStart_3052701 baseEnd_3052701 := by
    simpa [prefixWord, tailWord_3052701, baseEnd_3052701] using wordTrace_append hprefix tailTrace_3052701
  have hstable : (prefixWord ++ tailWord_3052701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052701).length < 2 ^ (prefixWord ++ tailWord_3052701).sum := by decide
  have hdescent : baseEnd_3052701 < baseStart_3052701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052776 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3052776 : Nat := 118140960795 + 3052776 * 2 ^ 59
def prefixEnd_3052776 : Nat := 4983230072969 + 3 ^ 40 * 3052776 * 2
def baseEnd_3052776 : Nat := 1045027612340035489040363

theorem tailTrace_3052776 : CollatzResearch.WordTrace tailWord_3052776 prefixEnd_3052776 1045027612340035489040363 := by
  unfold tailWord_3052776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55671943994160699738657091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74229258658880932984876121 55671943994160699738657091)
  ·
    refine ⟨83507915991241049607985637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55671943994160699738657091 83507915991241049607985637)
    ·
      refine ⟨15657734248357696801497307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83507915991241049607985637 15657734248357696801497307)
      ·
        refine ⟨23486601372536545202245961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15657734248357696801497307 23486601372536545202245961)
        ·
          refine ⟨17614951029402408901684471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23486601372536545202245961 17614951029402408901684471)
          ·
            refine ⟨26422426544103613352526707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17614951029402408901684471 26422426544103613352526707)
            ·
              refine ⟨39633639816155420028790061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26422426544103613352526707 39633639816155420028790061)
              ·
                refine ⟨14862614931058282510796273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39633639816155420028790061 14862614931058282510796273)
                ·
                  refine ⟨11146961198293711883097205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14862614931058282510796273 11146961198293711883097205)
                  ·
                    refine ⟨1045027612340035489040363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11146961198293711883097205 1045027612340035489040363)
                    ·
                      rfl

theorem cell22_3052776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3052776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052776 prefixEnd_3052776 := by exact prefixLift 3052776
  have htrace : WordTrace (prefixWord ++ tailWord_3052776) baseStart_3052776 baseEnd_3052776 := by
    simpa [prefixWord, tailWord_3052776, baseEnd_3052776] using wordTrace_append hprefix tailTrace_3052776
  have hstable : (prefixWord ++ tailWord_3052776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052776).length < 2 ^ (prefixWord ++ tailWord_3052776).sum := by decide
  have hdescent : baseEnd_3052776 < baseStart_3052776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052842 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3052842 : Nat := 118140960795 + 3052842 * 2 ^ 59
def prefixEnd_3052842 : Nat := 4983230072969 + 3 ^ 40 * 3052842 * 2
def baseEnd_3052842 : Nat := 1045050205488833316890161

theorem tailTrace_3052842 : CollatzResearch.WordTrace tailWord_3052842 prefixEnd_3052842 1045050205488833316890161 := by
  unfold tailWord_3052842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836573801520573187304195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74230863470721528499477853 27836573801520573187304195)
  ·
    refine ⟨41754860702280859780956293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27836573801520573187304195 41754860702280859780956293)
    ·
      refine ⟨7829036381677661208929305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41754860702280859780956293 7829036381677661208929305)
      ·
        refine ⟨5871777286258245906696979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829036381677661208929305 5871777286258245906696979)
        ·
          refine ⟨8807665929387368860045469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871777286258245906696979 8807665929387368860045469)
          ·
            refine ⟨3302874723520263322517051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8807665929387368860045469 3302874723520263322517051)
            ·
              refine ⟨4954312085280394983775577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302874723520263322517051 4954312085280394983775577)
              ·
                refine ⟨3715734063960296237831683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954312085280394983775577 3715734063960296237831683)
                ·
                  refine ⟨5573601095940444356747525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715734063960296237831683 5573601095940444356747525)
                  ·
                    refine ⟨1045050205488833316890161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573601095940444356747525 1045050205488833316890161)
                    ·
                      rfl

theorem cell22_3052842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3052842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052842 prefixEnd_3052842 := by exact prefixLift 3052842
  have htrace : WordTrace (prefixWord ++ tailWord_3052842) baseStart_3052842 baseEnd_3052842 := by
    simpa [prefixWord, tailWord_3052842, baseEnd_3052842] using wordTrace_append hprefix tailTrace_3052842
  have hstable : (prefixWord ++ tailWord_3052842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052842).length < 2 ^ (prefixWord ++ tailWord_3052842).sum := by decide
  have hdescent : baseEnd_3052842 < baseStart_3052842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052851 : List Nat := [1, 1, 1, 2, 5, 2, 2, 8]
def baseStart_3052851 : Nat := 118140960795 + 3052851 * 2 ^ 59
def prefixEnd_3052851 : Nat := 4983230072969 + 3 ^ 40 * 3052851 * 2
def baseEnd_3052851 : Nat := 116117031819195588157237

theorem tailTrace_3052851 : CollatzResearch.WordTrace tailWord_3052851 prefixEnd_3052851 116117031819195588157237 := by
  unfold tailWord_3052851
  simp only [CollatzResearch.WordTrace]
  refine ⟨111346623463049687286294407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74231082308699791524196271 111346623463049687286294407)
  ·
    refine ⟨167019935194574530929441611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111346623463049687286294407 167019935194574530929441611)
    ·
      refine ⟨250529902791861796394162417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167019935194574530929441611 250529902791861796394162417)
      ·
        refine ⟨187897427093896347295621813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250529902791861796394162417 187897427093896347295621813)
        ·
          refine ⟨17615383790052782558964545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187897427093896347295621813 17615383790052782558964545)
          ·
            refine ⟨13211537842539586919223409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17615383790052782558964545 13211537842539586919223409)
            ·
              refine ⟨9908653381904690189417557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13211537842539586919223409 9908653381904690189417557)
              ·
                refine ⟨116117031819195588157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9908653381904690189417557 116117031819195588157237)
                ·
                  rfl

theorem cell22_3052851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_3052851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052851 prefixEnd_3052851 := by exact prefixLift 3052851
  have htrace : WordTrace (prefixWord ++ tailWord_3052851) baseStart_3052851 baseEnd_3052851 := by
    simpa [prefixWord, tailWord_3052851, baseEnd_3052851] using wordTrace_append hprefix tailTrace_3052851
  have hstable : (prefixWord ++ tailWord_3052851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052851).length < 2 ^ (prefixWord ++ tailWord_3052851).sum := by decide
  have hdescent : baseEnd_3052851 < baseStart_3052851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052853 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3052853 : Nat := 118140960795 + 3052853 * 2 ^ 59
def prefixEnd_3052853 : Nat := 4983230072969 + 3 ^ 40 * 3052853 * 2
def baseEnd_3052853 : Nat := 1045053971013632954865127

theorem tailTrace_3052853 : CollatzResearch.WordTrace tailWord_3052853 prefixEnd_3052853 1045053971013632954865127 := by
  unfold tailWord_3052853
  simp only [CollatzResearch.WordTrace]
  refine ⟨111346696409042441627867213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74231130939361627751911475 111346696409042441627867213)
  ·
    refine ⟨41755011153390915610450205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111346696409042441627867213 41755011153390915610450205)
    ·
      refine ⟨15658129182521593353918827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41755011153390915610450205 15658129182521593353918827)
      ·
        refine ⟨23487193773782390030878241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15658129182521593353918827 23487193773782390030878241)
        ·
          refine ⟨17615395330336792523158681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23487193773782390030878241 17615395330336792523158681)
          ·
            refine ⟨13211546497752594392369011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17615395330336792523158681 13211546497752594392369011)
            ·
              refine ⟨19817319746628891588553517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13211546497752594392369011 19817319746628891588553517)
              ·
                refine ⟨7431494904985834345707569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19817319746628891588553517 7431494904985834345707569)
                ·
                  refine ⟨5573621178739375759280677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7431494904985834345707569 5573621178739375759280677)
                  ·
                    refine ⟨1045053971013632954865127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573621178739375759280677 1045053971013632954865127)
                    ·
                      rfl

theorem cell22_3052853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3052853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052853 prefixEnd_3052853 := by exact prefixLift 3052853
  have htrace : WordTrace (prefixWord ++ tailWord_3052853) baseStart_3052853 baseEnd_3052853 := by
    simpa [prefixWord, tailWord_3052853, baseEnd_3052853] using wordTrace_append hprefix tailTrace_3052853
  have hstable : (prefixWord ++ tailWord_3052853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052853).length < 2 ^ (prefixWord ++ tailWord_3052853).sum := by decide
  have hdescent : baseEnd_3052853 < baseStart_3052853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052868 : List Nat := [2, 3, 4, 1, 1, 11]
def baseStart_3052868 : Nat := 118140960795 + 3052868 * 2 ^ 59
def prefixEnd_3052868 : Nat := 4983230072969 + 3 ^ 40 * 3052868 * 2
def baseEnd_3052868 : Nat := 12901964269384912540001

theorem tailTrace_3052868 : CollatzResearch.WordTrace tailWord_3052868 prefixEnd_3052868 12901964269384912540001 := by
  unfold tailWord_3052868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55673621751994049594831629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74231495669325399459775505 55673621751994049594831629)
  ·
    refine ⟨20877608156997768598061861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55673621751994049594831629 20877608156997768598061861)
    ·
      refine ⟨3914551529437081612136599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20877608156997768598061861 3914551529437081612136599)
      ·
        refine ⟨5871827294155622418204899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914551529437081612136599 5871827294155622418204899)
        ·
          refine ⟨8807740941233433627307349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871827294155622418204899 8807740941233433627307349)
          ·
            refine ⟨12901964269384912540001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8807740941233433627307349 12901964269384912540001)
            ·
              rfl

theorem cell22_3052868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 11].length) (baseStart_3052868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052868 prefixEnd_3052868 := by exact prefixLift 3052868
  have htrace : WordTrace (prefixWord ++ tailWord_3052868) baseStart_3052868 baseEnd_3052868 := by
    simpa [prefixWord, tailWord_3052868, baseEnd_3052868] using wordTrace_append hprefix tailTrace_3052868
  have hstable : (prefixWord ++ tailWord_3052868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052868).length < 2 ^ (prefixWord ++ tailWord_3052868).sum := by decide
  have hdescent : baseEnd_3052868 < baseStart_3052868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052881 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3052881 : Nat := 118140960795 + 3052881 * 2 ^ 59
def prefixEnd_3052881 : Nat := 4983230072969 + 3 ^ 40 * 3052881 * 2
def baseEnd_3052881 : Nat := 1045063555985850215165041

theorem tailTrace_3052881 : CollatzResearch.WordTrace tailWord_3052881 prefixEnd_3052881 1045063555985850215165041 := by
  unfold tailWord_3052881
  simp only [CollatzResearch.WordTrace]
  refine ⟨111347717652941002409886497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74231811768627334939924331 111347717652941002409886497)
  ·
    refine ⟨83510788239705751807414873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111347717652941002409886497 83510788239705751807414873)
    ·
      refine ⟨62633091179779313855561155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83510788239705751807414873 62633091179779313855561155)
      ·
        refine ⟨93949636769668970783341733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62633091179779313855561155 93949636769668970783341733)
        ·
          refine ⟨17615556894312932021876575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93949636769668970783341733 17615556894312932021876575)
          ·
            refine ⟨26423335341469398032814863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615556894312932021876575 26423335341469398032814863)
            ·
              refine ⟨39635003012204097049222295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26423335341469398032814863 39635003012204097049222295)
              ·
                refine ⟨59452504518306145573833443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39635003012204097049222295 59452504518306145573833443)
                ·
                  refine ⟨89178756777459218360750165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59452504518306145573833443 89178756777459218360750165)
                  ·
                    refine ⟨1045063555985850215165041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89178756777459218360750165 1045063555985850215165041)
                    ·
                      rfl

theorem cell22_3052881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3052881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052881 prefixEnd_3052881 := by exact prefixLift 3052881
  have htrace : WordTrace (prefixWord ++ tailWord_3052881) baseStart_3052881 baseEnd_3052881 := by
    simpa [prefixWord, tailWord_3052881, baseEnd_3052881] using wordTrace_append hprefix tailTrace_3052881
  have hstable : (prefixWord ++ tailWord_3052881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052881).length < 2 ^ (prefixWord ++ tailWord_3052881).sum := by decide
  have hdescent : baseEnd_3052881 < baseStart_3052881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052883 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 3, 3]
def baseStart_3052883 : Nat := 118140960795 + 3052883 * 2 ^ 59
def prefixEnd_3052883 : Nat := 4983230072969 + 3 ^ 40 * 3052883 * 2
def baseEnd_3052883 : Nat := 1045064240626722876615035

theorem tailTrace_3052883 : CollatzResearch.WordTrace tailWord_3052883 prefixEnd_3052883 1045064240626722876615035 := by
  unfold tailWord_3052883
  simp only [CollatzResearch.WordTrace]
  refine ⟨111347790598933756751459303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74231860399289171167639535 111347790598933756751459303)
  ·
    refine ⟨167021685898400635127188955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111347790598933756751459303 167021685898400635127188955)
    ·
      refine ⟨250532528847600952690783433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167021685898400635127188955 250532528847600952690783433)
      ·
        refine ⟨187899396635700714518087575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250532528847600952690783433 187899396635700714518087575)
        ·
          refine ⟨281849094953551071777131363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187899396635700714518087575 281849094953551071777131363)
          ·
            refine ⟨422773642430326607665697045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281849094953551071777131363 422773642430326607665697045)
            ·
              refine ⟨19817514488921559734329549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 422773642430326607665697045 19817514488921559734329549)
              ·
                refine ⟨7431567933345584900373581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19817514488921559734329549 7431567933345584900373581)
                ·
                  refine ⟨2786837975004594337640093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7431567933345584900373581 2786837975004594337640093)
                  ·
                    refine ⟨1045064240626722876615035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786837975004594337640093 1045064240626722876615035)
                    ·
                      rfl

theorem cell22_3052883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].length) (baseStart_3052883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052883 prefixEnd_3052883 := by exact prefixLift 3052883
  have htrace : WordTrace (prefixWord ++ tailWord_3052883) baseStart_3052883 baseEnd_3052883 := by
    simpa [prefixWord, tailWord_3052883, baseEnd_3052883] using wordTrace_append hprefix tailTrace_3052883
  have hstable : (prefixWord ++ tailWord_3052883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052883).length < 2 ^ (prefixWord ++ tailWord_3052883).sum := by decide
  have hdescent : baseEnd_3052883 < baseStart_3052883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052898 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3052898 : Nat := 118140960795 + 3052898 * 2 ^ 59
def prefixEnd_3052898 : Nat := 4983230072969 + 3 ^ 40 * 3052898 * 2
def baseEnd_3052898 : Nat := 1045069375433267837489989

theorem tailTrace_3052898 : CollatzResearch.WordTrace tailWord_3052898 prefixEnd_3052898 1045069375433267837489989 := by
  unfold tailWord_3052898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27837084423469853578313837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74232225129252942875503565 27837084423469853578313837)
  ·
    refine ⟨10438906658801195091867689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27837084423469853578313837 10438906658801195091867689)
    ·
      refine ⟨7829179994100896318900767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10438906658801195091867689 7829179994100896318900767)
      ·
        refine ⟨11743769991151344478351151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829179994100896318900767 11743769991151344478351151)
        ·
          refine ⟨17615654986727016717526727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11743769991151344478351151 17615654986727016717526727)
          ·
            refine ⟨26423482480090525076290091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615654986727016717526727 26423482480090525076290091)
            ·
              refine ⟨39635223720135787614435137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26423482480090525076290091 39635223720135787614435137)
              ·
                refine ⟨29726417790101840710826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39635223720135787614435137 29726417790101840710826353)
                ·
                  refine ⟨22294813342576380533119765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29726417790101840710826353 22294813342576380533119765)
                  ·
                    refine ⟨1045069375433267837489989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22294813342576380533119765 1045069375433267837489989)
                    ·
                      rfl

theorem cell22_3052898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3052898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052898 prefixEnd_3052898 := by exact prefixLift 3052898
  have htrace : WordTrace (prefixWord ++ tailWord_3052898) baseStart_3052898 baseEnd_3052898 := by
    simpa [prefixWord, tailWord_3052898, baseEnd_3052898] using wordTrace_append hprefix tailTrace_3052898
  have hstable : (prefixWord ++ tailWord_3052898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052898).length < 2 ^ (prefixWord ++ tailWord_3052898).sum := by decide
  have hdescent : baseEnd_3052898 < baseStart_3052898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052900 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3052900 : Nat := 118140960795 + 3052900 * 2 ^ 59
def prefixEnd_3052900 : Nat := 4983230072969 + 3 ^ 40 * 3052900 * 2
def baseEnd_3052900 : Nat := 1045070060074140498939983

theorem tailTrace_3052900 : CollatzResearch.WordTrace tailWord_3052900 prefixEnd_3052900 1045070060074140498939983 := by
  unfold tailWord_3052900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55674205319936084327414077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74232273759914779103218769 55674205319936084327414077)
  ·
    refine ⟨20877826994976031622780279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55674205319936084327414077 20877826994976031622780279)
    ·
      refine ⟨31316740492464047434170419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20877826994976031622780279 31316740492464047434170419)
      ·
        refine ⟨46975110738696071151255629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31316740492464047434170419 46975110738696071151255629)
        ·
          refine ⟨17615666527011026681720861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46975110738696071151255629 17615666527011026681720861)
          ·
            refine ⟨6605874947629135005645323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17615666527011026681720861 6605874947629135005645323)
            ·
              refine ⟨9908812421443702508467985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605874947629135005645323 9908812421443702508467985)
              ·
                refine ⟨7431609316082776881350989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9908812421443702508467985 7431609316082776881350989)
                ·
                  refine ⟨2786853493531041330506621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7431609316082776881350989 2786853493531041330506621)
                  ·
                    refine ⟨1045070060074140498939983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786853493531041330506621 1045070060074140498939983)
                    ·
                      rfl

theorem cell22_3052900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3052900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052900 prefixEnd_3052900 := by exact prefixLift 3052900
  have htrace : WordTrace (prefixWord ++ tailWord_3052900) baseStart_3052900 baseEnd_3052900 := by
    simpa [prefixWord, tailWord_3052900, baseEnd_3052900] using wordTrace_append hprefix tailTrace_3052900
  have hstable : (prefixWord ++ tailWord_3052900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052900).length < 2 ^ (prefixWord ++ tailWord_3052900).sum := by decide
  have hdescent : baseEnd_3052900 < baseStart_3052900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052911 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3052911 : Nat := 118140960795 + 3052911 * 2 ^ 59
def prefixEnd_3052911 : Nat := 4983230072969 + 3 ^ 40 * 3052911 * 2
def baseEnd_3052911 : Nat := 1045073825598940136914949

theorem tailTrace_3052911 : CollatzResearch.WordTrace tailWord_3052911 prefixEnd_3052911 1045073825598940136914949 := by
  unfold tailWord_3052911
  simp only [CollatzResearch.WordTrace]
  refine ⟨111348811842832317533478587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74232541228554878355652391 111348811842832317533478587)
  ·
    refine ⟨167023217764248476300217881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111348811842832317533478587 167023217764248476300217881)
    ·
      refine ⟨125267413323186357225163411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167023217764248476300217881 125267413323186357225163411)
      ·
        refine ⟨187901119984779535837745117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125267413323186357225163411 187901119984779535837745117)
        ·
          refine ⟨70462919994292325939154419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187901119984779535837745117 70462919994292325939154419)
          ·
            refine ⟨105694379991438488908731629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70462919994292325939154419 105694379991438488908731629)
            ·
              refine ⟨39635392496789433340774361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105694379991438488908731629 39635392496789433340774361)
              ·
                refine ⟨29726544372592075005580771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39635392496789433340774361 29726544372592075005580771)
                ·
                  refine ⟨44589816558888112508371157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29726544372592075005580771 44589816558888112508371157)
                  ·
                    refine ⟨1045073825598940136914949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44589816558888112508371157 1045073825598940136914949)
                    ·
                      rfl

theorem cell22_3052911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3052911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052911 prefixEnd_3052911 := by exact prefixLift 3052911
  have htrace : WordTrace (prefixWord ++ tailWord_3052911) baseStart_3052911 baseEnd_3052911 := by
    simpa [prefixWord, tailWord_3052911, baseEnd_3052911] using wordTrace_append hprefix tailTrace_3052911
  have hstable : (prefixWord ++ tailWord_3052911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052911).length < 2 ^ (prefixWord ++ tailWord_3052911).sum := by decide
  have hdescent : baseEnd_3052911 < baseStart_3052911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052960 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_3052960 : Nat := 118140960795 + 3052960 * 2 ^ 59
def prefixEnd_3052960 : Nat := 4983230072969 + 3 ^ 40 * 3052960 * 2
def baseEnd_3052960 : Nat := 1045090599300320342439799

theorem tailTrace_3052960 : CollatzResearch.WordTrace tailWord_3052960 prefixEnd_3052960 1045090599300320342439799 := by
  unfold tailWord_3052960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675299509827399451006167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74233732679769865934674889 55675299509827399451006167)
  ·
    refine ⟨83512949264741099176509251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55675299509827399451006167 83512949264741099176509251)
    ·
      refine ⟨125269423897111648764763877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83512949264741099176509251 125269423897111648764763877)
      ·
        refine ⟨23488016980708434143393227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125269423897111648764763877 23488016980708434143393227)
        ·
          refine ⟨35232025471062651215089841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23488016980708434143393227 35232025471062651215089841)
          ·
            refine ⟨26424019103296988411317381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35232025471062651215089841 26424019103296988411317381)
            ·
              refine ⟨4954503581868185327122009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26424019103296988411317381 4954503581868185327122009)
              ·
                refine ⟨3715877686401138995341507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954503581868185327122009 3715877686401138995341507)
                ·
                  refine ⟨5573816529601708493012261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715877686401138995341507 5573816529601708493012261)
                  ·
                    refine ⟨1045090599300320342439799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573816529601708493012261 1045090599300320342439799)
                    ·
                      rfl

theorem cell22_3052960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_3052960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052960 prefixEnd_3052960 := by exact prefixLift 3052960
  have htrace : WordTrace (prefixWord ++ tailWord_3052960) baseStart_3052960 baseEnd_3052960 := by
    simpa [prefixWord, tailWord_3052960, baseEnd_3052960] using wordTrace_append hprefix tailTrace_3052960
  have hstable : (prefixWord ++ tailWord_3052960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052960).length < 2 ^ (prefixWord ++ tailWord_3052960).sum := by decide
  have hdescent : baseEnd_3052960 < baseStart_3052960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052968 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3052968 : Nat := 118140960795 + 3052968 * 2 ^ 59
def prefixEnd_3052968 : Nat := 4983230072969 + 3 ^ 40 * 3052968 * 2
def baseEnd_3052968 : Nat := 1045093337863810988239775

theorem tailTrace_3052968 : CollatzResearch.WordTrace tailWord_3052968 prefixEnd_3052968 1045093337863810988239775 := by
  unfold tailWord_3052968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675445401812908134151779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74233927202417210845535705 55675445401812908134151779)
  ·
    refine ⟨83513168102719362201227669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55675445401812908134151779 83513168102719362201227669)
    ·
      refine ⟨3914679754814970103182547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83513168102719362201227669 3914679754814970103182547)
      ·
        refine ⟨5872019632222455154773821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914679754814970103182547 5872019632222455154773821)
        ·
          refine ⟨2202007362083420683040183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5872019632222455154773821 2202007362083420683040183)
          ·
            refine ⟨3303011043125131024560275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202007362083420683040183 3303011043125131024560275)
            ·
              refine ⟨4954516564687696536840413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303011043125131024560275 4954516564687696536840413)
              ·
                refine ⟨1857943711757886201315155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4954516564687696536840413 1857943711757886201315155)
                ·
                  refine ⟨2786915567636829301972733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857943711757886201315155 2786915567636829301972733)
                  ·
                    refine ⟨1045093337863810988239775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786915567636829301972733 1045093337863810988239775)
                    ·
                      rfl

theorem cell22_3052968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3052968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3052968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3052968 prefixEnd_3052968 := by exact prefixLift 3052968
  have htrace : WordTrace (prefixWord ++ tailWord_3052968) baseStart_3052968 baseEnd_3052968 := by
    simpa [prefixWord, tailWord_3052968, baseEnd_3052968] using wordTrace_append hprefix tailTrace_3052968
  have hstable : (prefixWord ++ tailWord_3052968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052968).length < 2 ^ (prefixWord ++ tailWord_3052968).sum := by decide
  have hdescent : baseEnd_3052968 < baseStart_3052968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053007 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 2, 3]
def baseStart_3053007 : Nat := 118140960795 + 3053007 * 2 ^ 59
def prefixEnd_3053007 : Nat := 4983230072969 + 3 ^ 40 * 3053007 * 2
def baseEnd_3053007 : Nat := 1045106688360827886514655

theorem tailTrace_3053007 : CollatzResearch.WordTrace tailWord_3053007 prefixEnd_3053007 1045106688360827886514655 := by
  unfold tailWord_3053007
  simp only [CollatzResearch.WordTrace]
  refine ⟨111352313250484525928973275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74234875500323017285982183 111352313250484525928973275)
  ·
    refine ⟨167028469875726788893459913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111352313250484525928973275 167028469875726788893459913)
    ·
      refine ⟨125271352406795091670094935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167028469875726788893459913 125271352406795091670094935)
      ·
        refine ⟨187907028610192637505142403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125271352406795091670094935 187907028610192637505142403)
        ·
          refine ⟨281860542915288956257713605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187907028610192637505142403 281860542915288956257713605)
          ·
            refine ⟨52848851796616679298321301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281860542915288956257713605 52848851796616679298321301)
            ·
              refine ⟨2477289927966406842108811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52848851796616679298321301 2477289927966406842108811)
              ·
                refine ⟨3715934891949610263163217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477289927966406842108811 3715934891949610263163217)
                ·
                  refine ⟨2786951168962207697372413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715934891949610263163217 2786951168962207697372413)
                  ·
                    refine ⟨1045106688360827886514655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786951168962207697372413 1045106688360827886514655)
                    ·
                      rfl

theorem cell22_3053007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_3053007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053007 prefixEnd_3053007 := by exact prefixLift 3053007
  have htrace : WordTrace (prefixWord ++ tailWord_3053007) baseStart_3053007 baseEnd_3053007 := by
    simpa [prefixWord, tailWord_3053007, baseEnd_3053007] using wordTrace_append hprefix tailTrace_3053007
  have hstable : (prefixWord ++ tailWord_3053007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053007).length < 2 ^ (prefixWord ++ tailWord_3053007).sum := by decide
  have hdescent : baseEnd_3053007 < baseStart_3053007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053054 : List Nat := [4, 2, 2, 3, 1, 2, 1, 7]
def baseStart_3053054 : Nat := 118140960795 + 3053054 * 2 ^ 59
def prefixEnd_3053054 : Nat := 4983230072969 + 3 ^ 40 * 3053054 * 2
def baseEnd_3053054 : Nat := 116124753046815047843279

theorem tailTrace_3053054 : CollatzResearch.WordTrace tailWord_3053054 prefixEnd_3053054 116124753046815047843279 := by
  unfold tailWord_3053054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919253435164281619491777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74236018320876168637289477 13919253435164281619491777)
  ·
    refine ⟨10439440076373211214618833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13919253435164281619491777 10439440076373211214618833)
    ·
      refine ⟨7829580057279908410964125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10439440076373211214618833 7829580057279908410964125)
      ·
        refine ⟨2936092521479965654111547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7829580057279908410964125 2936092521479965654111547)
        ·
          refine ⟨4404138782219948481167321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936092521479965654111547 4404138782219948481167321)
          ·
            refine ⟨3303104086664961360875491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4404138782219948481167321 3303104086664961360875491)
            ·
              refine ⟨4954656129997442041313237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303104086664961360875491 4954656129997442041313237)
              ·
                refine ⟨116124753046815047843279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4954656129997442041313237 116124753046815047843279)
                ·
                  rfl

theorem cell22_3053054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_3053054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053054 prefixEnd_3053054 := by exact prefixLift 3053054
  have htrace : WordTrace (prefixWord ++ tailWord_3053054) baseStart_3053054 baseEnd_3053054 := by
    simpa [prefixWord, tailWord_3053054, baseEnd_3053054] using wordTrace_append hprefix tailTrace_3053054
  have hstable : (prefixWord ++ tailWord_3053054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053054).length < 2 ^ (prefixWord ++ tailWord_3053054).sum := by decide
  have hdescent : baseEnd_3053054 < baseStart_3053054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053093 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 10]
def baseStart_3053093 : Nat := 118140960795 + 3053093 * 2 ^ 59
def prefixEnd_3053093 : Nat := 4983230072969 + 3 ^ 40 * 3053093 * 2
def baseEnd_3053093 : Nat := 348378709306117442954797

theorem tailTrace_3053093 : CollatzResearch.WordTrace tailWord_3053093 prefixEnd_3053093 348378709306117442954797 := by
  unfold tailWord_3053093
  simp only [CollatzResearch.WordTrace]
  refine ⟨111355449928172962616603933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74236966618781975077735955 111355449928172962616603933)
  ·
    refine ⟨41758293723064860981226475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111355449928172962616603933 41758293723064860981226475)
    ·
      refine ⟨62637440584597291471839713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41758293723064860981226475 62637440584597291471839713)
      ·
        refine ⟨46978080438447968603879785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62637440584597291471839713 46978080438447968603879785)
        ·
          refine ⟨35233560328835976452909839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46978080438447968603879785 35233560328835976452909839)
          ·
            refine ⟨52850340493253964679364759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35233560328835976452909839 52850340493253964679364759)
            ·
              refine ⟨79275510739880947019047139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52850340493253964679364759 79275510739880947019047139)
              ·
                refine ⟨118913266109821420528570709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79275510739880947019047139 118913266109821420528570709)
                ·
                  refine ⟨348378709306117442954797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118913266109821420528570709 348378709306117442954797)
                  ·
                    rfl

theorem cell22_3053093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_3053093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053093 prefixEnd_3053093 := by exact prefixLift 3053093
  have htrace : WordTrace (prefixWord ++ tailWord_3053093) baseStart_3053093 baseEnd_3053093 := by
    simpa [prefixWord, tailWord_3053093, baseEnd_3053093] using wordTrace_append hprefix tailTrace_3053093
  have hstable : (prefixWord ++ tailWord_3053093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053093).length < 2 ^ (prefixWord ++ tailWord_3053093).sum := by decide
  have hdescent : baseEnd_3053093 < baseStart_3053093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053140 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3053140 : Nat := 118140960795 + 3053140 * 2 ^ 59
def prefixEnd_3053140 : Nat := 4983230072969 + 3 ^ 40 * 3053140 * 2
def baseEnd_3053140 : Nat := 1045152216978859872939247

theorem tailTrace_3053140 : CollatzResearch.WordTrace tailWord_3053140 prefixEnd_3053140 1045152216978859872939247 := by
  unfold tailWord_3053140
  simp only [CollatzResearch.WordTrace]
  refine ⟨55678582079501344821782437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74238109439335126429043249 55678582079501344821782437)
  ·
    refine ⟨10439734139906502154084207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55678582079501344821782437 10439734139906502154084207)
    ·
      refine ⟨15659601209859753231126311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439734139906502154084207 15659601209859753231126311)
      ·
        refine ⟨23489401814789629846689467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15659601209859753231126311 23489401814789629846689467)
        ·
          refine ⟨35234102722184444770034201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23489401814789629846689467 35234102722184444770034201)
          ·
            refine ⟨26425577041638333577525651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35234102722184444770034201 26425577041638333577525651)
            ·
              refine ⟨39638365562457500366288477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26425577041638333577525651 39638365562457500366288477)
              ·
                refine ⟨14864387085921562637358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39638365562457500366288477 14864387085921562637358179)
                ·
                  refine ⟨22296580628882343956037269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14864387085921562637358179 22296580628882343956037269)
                  ·
                    refine ⟨1045152216978859872939247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22296580628882343956037269 1045152216978859872939247)
                    ·
                      rfl

theorem cell22_3053140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3053140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053140 prefixEnd_3053140 := by exact prefixLift 3053140
  have htrace : WordTrace (prefixWord ++ tailWord_3053140) baseStart_3053140 baseEnd_3053140 := by
    simpa [prefixWord, tailWord_3053140, baseEnd_3053140] using wordTrace_append hprefix tailTrace_3053140
  have hstable : (prefixWord ++ tailWord_3053140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053140).length < 2 ^ (prefixWord ++ tailWord_3053140).sum := by decide
  have hdescent : baseEnd_3053140 < baseStart_3053140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053155 : List Nat := [1, 1, 1, 5, 1, 5, 8]
def baseStart_3053155 : Nat := 118140960795 + 3053155 * 2 ^ 59
def prefixEnd_3053155 : Nat := 4983230072969 + 3 ^ 40 * 3053155 * 2
def baseEnd_3053155 : Nat := 38709531547607586437563

theorem tailTrace_3053155 : CollatzResearch.WordTrace tailWord_3053155 prefixEnd_3053155 38709531547607586437563 := by
  unfold tailWord_3053155
  simp only [CollatzResearch.WordTrace]
  refine ⟨111357711253948347205360919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74238474169298898136907279 111357711253948347205360919)
  ·
    refine ⟨167036566880922520808041379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111357711253948347205360919 167036566880922520808041379)
    ·
      refine ⟨250554850321383781212062069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167036566880922520808041379 250554850321383781212062069)
      ·
        refine ⟨23489517217629729488630819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250554850321383781212062069 23489517217629729488630819)
        ·
          refine ⟨35234275826444594232946229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23489517217629729488630819 35234275826444594232946229)
          ·
            refine ⟨3303213358729180709338709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35234275826444594232946229 3303213358729180709338709)
            ·
              refine ⟨38709531547607586437563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3303213358729180709338709 38709531547607586437563)
              ·
                rfl

theorem cell22_3053155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 8].length) (baseStart_3053155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053155 prefixEnd_3053155 := by exact prefixLift 3053155
  have htrace : WordTrace (prefixWord ++ tailWord_3053155) baseStart_3053155 baseEnd_3053155 := by
    simpa [prefixWord, tailWord_3053155, baseEnd_3053155] using wordTrace_append hprefix tailTrace_3053155
  have hstable : (prefixWord ++ tailWord_3053155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053155).length < 2 ^ (prefixWord ++ tailWord_3053155).sum := by decide
  have hdescent : baseEnd_3053155 < baseStart_3053155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053157 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_3053157 : Nat := 118140960795 + 3053157 * 2 ^ 59
def prefixEnd_3053157 : Nat := 4983230072969 + 3 ^ 40 * 3053157 * 2
def baseEnd_3053157 : Nat := 1045158036426277495264195

theorem tailTrace_3053157 : CollatzResearch.WordTrace tailWord_3053157 prefixEnd_3053157 1045158036426277495264195 := by
  unfold tailWord_3053157
  simp only [CollatzResearch.WordTrace]
  refine ⟨111357784199941101546933725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74238522799960734364622483 111357784199941101546933725)
  ·
    refine ⟨41759169074977913080100147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111357784199941101546933725 41759169074977913080100147)
    ·
      refine ⟨62638753612466869620150221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41759169074977913080100147 62638753612466869620150221)
      ·
        refine ⟨23489532604675076107556333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62638753612466869620150221 23489532604675076107556333)
        ·
          refine ⟨8808574726753153540333625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23489532604675076107556333 8808574726753153540333625)
          ·
            refine ⟨6606431045064865155250219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8808574726753153540333625 6606431045064865155250219)
            ·
              refine ⟨9909646567597297732875329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606431045064865155250219 9909646567597297732875329)
              ·
                refine ⟨7432234925697973299656497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9909646567597297732875329 7432234925697973299656497)
                ·
                  refine ⟨5574176194273479974742373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7432234925697973299656497 5574176194273479974742373)
                  ·
                    refine ⟨1045158036426277495264195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574176194273479974742373 1045158036426277495264195)
                    ·
                      rfl

theorem cell22_3053157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_3053157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053157 prefixEnd_3053157 := by exact prefixLift 3053157
  have htrace : WordTrace (prefixWord ++ tailWord_3053157) baseStart_3053157 baseEnd_3053157 := by
    simpa [prefixWord, tailWord_3053157, baseEnd_3053157] using wordTrace_append hprefix tailTrace_3053157
  have hstable : (prefixWord ++ tailWord_3053157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053157).length < 2 ^ (prefixWord ++ tailWord_3053157).sum := by decide
  have hdescent : baseEnd_3053157 < baseStart_3053157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053217 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 5]
def baseStart_3053217 : Nat := 118140960795 + 3053217 * 2 ^ 59
def prefixEnd_3053217 : Nat := 4983230072969 + 3 ^ 40 * 3053217 * 2
def baseEnd_3053217 : Nat := 348392858550819112921337

theorem tailTrace_3053217 : CollatzResearch.WordTrace tailWord_3053217 prefixEnd_3053217 348392858550819112921337 := by
  unfold tailWord_3053217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111359972579723731794117905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74239981719815821196078603 111359972579723731794117905)
  ·
    refine ⟨83519979434792798845588429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111359972579723731794117905 83519979434792798845588429)
    ·
      refine ⟨31319992288047299567095661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83519979434792798845588429 31319992288047299567095661)
      ·
        refine ⟨11744997108017737337660873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31319992288047299567095661 11744997108017737337660873)
        ·
          refine ⟨8808747831013303003245655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744997108017737337660873 8808747831013303003245655)
          ·
            refine ⟨13213121746519954504868483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8808747831013303003245655 13213121746519954504868483)
            ·
              refine ⟨19819682619779931757302725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13213121746519954504868483 19819682619779931757302725)
              ·
                refine ⟨3716190491208737204494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19819682619779931757302725 3716190491208737204494261)
                ·
                  refine ⟨348392858550819112921337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3716190491208737204494261 348392858550819112921337)
                  ·
                    rfl

theorem cell22_3053217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_3053217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053217 prefixEnd_3053217 := by exact prefixLift 3053217
  have htrace : WordTrace (prefixWord ++ tailWord_3053217) baseStart_3053217 baseEnd_3053217 := by
    simpa [prefixWord, tailWord_3053217, baseEnd_3053217] using wordTrace_append hprefix tailTrace_3053217
  have hstable : (prefixWord ++ tailWord_3053217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053217).length < 2 ^ (prefixWord ++ tailWord_3053217).sum := by decide
  have hdescent : baseEnd_3053217 < baseStart_3053217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053221 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_3053221 : Nat := 118140960795 + 3053221 * 2 ^ 59
def prefixEnd_3053221 : Nat := 4983230072969 + 3 ^ 40 * 3053221 * 2
def baseEnd_3053221 : Nat := 1045179944934202661663999

theorem tailTrace_3053221 : CollatzResearch.WordTrace tailWord_3053221 prefixEnd_3053221 1045179944934202661663999 := by
  unfold tailWord_3053221
  simp only [CollatzResearch.WordTrace]
  refine ⟨111360118471709240477263517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74240078981139493651509011 111360118471709240477263517)
  ·
    refine ⟨41760044426890965178973819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111360118471709240477263517 41760044426890965178973819)
    ·
      refine ⟨62640066640336447768460729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41760044426890965178973819 62640066640336447768460729)
      ·
        refine ⟨46980049980252335826345547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62640066640336447768460729 46980049980252335826345547)
        ·
          refine ⟨70470074970378503739518321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46980049980252335826345547 70470074970378503739518321)
          ·
            refine ⟨52852556227783877804638741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70470074970378503739518321 52852556227783877804638741)
            ·
              refine ⟨2477463573177369272092441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52852556227783877804638741 2477463573177369272092441)
              ·
                refine ⟨1858097679883026954069331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477463573177369272092441 1858097679883026954069331)
                ·
                  refine ⟨2787146519824540431103997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858097679883026954069331 2787146519824540431103997)
                  ·
                    refine ⟨1045179944934202661663999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787146519824540431103997 1045179944934202661663999)
                    ·
                      rfl

theorem cell22_3053221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_3053221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053221 prefixEnd_3053221 := by exact prefixLift 3053221
  have htrace : WordTrace (prefixWord ++ tailWord_3053221) baseStart_3053221 baseEnd_3053221 := by
    simpa [prefixWord, tailWord_3053221, baseEnd_3053221] using wordTrace_append hprefix tailTrace_3053221
  have hstable : (prefixWord ++ tailWord_3053221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053221).length < 2 ^ (prefixWord ++ tailWord_3053221).sum := by decide
  have hdescent : baseEnd_3053221 < baseStart_3053221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053247 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 1, 4]
def baseStart_3053247 : Nat := 118140960795 + 3053247 * 2 ^ 59
def prefixEnd_3053247 : Nat := 4983230072969 + 3 ^ 40 * 3053247 * 2
def baseEnd_3053247 : Nat := 1045188845265547260513919

theorem tailTrace_3053247 : CollatzResearch.WordTrace tailWord_3053247 prefixEnd_3053247 1045188845265547260513919 := by
  unfold tailWord_3053247
  simp only [CollatzResearch.WordTrace]
  refine ⟨111361066769615046917709995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74240711179743364611806663 111361066769615046917709995)
  ·
    refine ⟨167041600154422570376564993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111361066769615046917709995 167041600154422570376564993)
    ·
      refine ⟨125281200115816927782423745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167041600154422570376564993 125281200115816927782423745)
      ·
        refine ⟨93960900086862695836817809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125281200115816927782423745 93960900086862695836817809)
        ·
          refine ⟨70470675065147021877613357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93960900086862695836817809 70470675065147021877613357)
          ·
            refine ⟨26426503149430133204105009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70470675065147021877613357 26426503149430133204105009)
            ·
              refine ⟨19819877362072599903078757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26426503149430133204105009 19819877362072599903078757)
              ·
                refine ⟨3716227005388612481827267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19819877362072599903078757 3716227005388612481827267)
                ·
                  refine ⟨5574340508082918722740901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716227005388612481827267 5574340508082918722740901)
                  ·
                    refine ⟨1045188845265547260513919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574340508082918722740901 1045188845265547260513919)
                    ·
                      rfl

theorem cell22_3053247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_3053247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053247 prefixEnd_3053247 := by exact prefixLift 3053247
  have htrace : WordTrace (prefixWord ++ tailWord_3053247) baseStart_3053247 baseEnd_3053247 := by
    simpa [prefixWord, tailWord_3053247, baseEnd_3053247] using wordTrace_append hprefix tailTrace_3053247
  have hstable : (prefixWord ++ tailWord_3053247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053247).length < 2 ^ (prefixWord ++ tailWord_3053247).sum := by decide
  have hdescent : baseEnd_3053247 < baseStart_3053247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053429 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3053429 : Nat := 118140960795 + 3053429 * 2 ^ 59
def prefixEnd_3053429 : Nat := 4983230072969 + 3 ^ 40 * 3053429 * 2
def baseEnd_3053429 : Nat := 1045251147584959452463361

theorem tailTrace_3053429 : CollatzResearch.WordTrace tailWord_3053429 prefixEnd_3053429 1045251147584959452463361 := by
  unfold tailWord_3053429
  simp only [CollatzResearch.WordTrace]
  refine ⟨111367704854955692000835341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74245136569970461333890227 111367704854955692000835341)
  ·
    refine ⟨41762889320608384500313253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111367704854955692000835341 41762889320608384500313253)
    ·
      refine ⟨7830541747614072093808735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41762889320608384500313253 7830541747614072093808735)
      ·
        refine ⟨11745812621421108140713103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830541747614072093808735 11745812621421108140713103)
        ·
          refine ⟨17618718932131662211069655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11745812621421108140713103 17618718932131662211069655)
          ·
            refine ⟨26428078398197493316604483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17618718932131662211069655 26428078398197493316604483)
            ·
              refine ⟨39642117597296239974906725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26428078398197493316604483 39642117597296239974906725)
              ·
                refine ⟨7432897049493044995295011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39642117597296239974906725 7432897049493044995295011)
                ·
                  refine ⟨11149345574239567492942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7432897049493044995295011 11149345574239567492942517)
                  ·
                    refine ⟨1045251147584959452463361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11149345574239567492942517 1045251147584959452463361)
                    ·
                      rfl

theorem cell22_3053429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3053429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053429 prefixEnd_3053429 := by exact prefixLift 3053429
  have htrace : WordTrace (prefixWord ++ tailWord_3053429) baseStart_3053429 baseEnd_3053429 := by
    simpa [prefixWord, tailWord_3053429, baseEnd_3053429] using wordTrace_append hprefix tailTrace_3053429
  have hstable : (prefixWord ++ tailWord_3053429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053429).length < 2 ^ (prefixWord ++ tailWord_3053429).sum := by decide
  have hdescent : baseEnd_3053429 < baseStart_3053429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053444 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3053444 : Nat := 118140960795 + 3053444 * 2 ^ 59
def prefixEnd_3053444 : Nat := 4983230072969 + 3 ^ 40 * 3053444 * 2
def baseEnd_3053444 : Nat := 1045256282391504413338315

theorem tailTrace_3053444 : CollatzResearch.WordTrace tailWord_3053444 prefixEnd_3053444 1045256282391504413338315 := by
  unfold tailWord_3053444
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684125974950674781315693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74245501299934233041754257 55684125974950674781315693)
  ·
    refine ⟨20881547240606503042993385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55684125974950674781315693 20881547240606503042993385)
    ·
      refine ⟨15661160430454877282245039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20881547240606503042993385 15661160430454877282245039)
      ·
        refine ⟨23491740645682315923367559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661160430454877282245039 23491740645682315923367559)
        ·
          refine ⟨35237610968523473885051339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491740645682315923367559 35237610968523473885051339)
          ·
            refine ⟨52856416452785210827577009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35237610968523473885051339 52856416452785210827577009)
            ·
              refine ⟨39642312339588908120682757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52856416452785210827577009 39642312339588908120682757)
              ·
                refine ⟨7432933563672920272628017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39642312339588908120682757 7432933563672920272628017)
                ·
                  refine ⟨5574700172754690204471013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7432933563672920272628017 5574700172754690204471013)
                  ·
                    refine ⟨1045256282391504413338315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574700172754690204471013 1045256282391504413338315)
                    ·
                      rfl

theorem cell22_3053444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3053444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053444 prefixEnd_3053444 := by exact prefixLift 3053444
  have htrace : WordTrace (prefixWord ++ tailWord_3053444) baseStart_3053444 baseEnd_3053444 := by
    simpa [prefixWord, tailWord_3053444, baseEnd_3053444] using wordTrace_append hprefix tailTrace_3053444
  have hstable : (prefixWord ++ tailWord_3053444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053444).length < 2 ^ (prefixWord ++ tailWord_3053444).sum := by decide
  have hdescent : baseEnd_3053444 < baseStart_3053444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053463 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 2, 3]
def baseStart_3053463 : Nat := 118140960795 + 3053463 * 2 ^ 59
def prefixEnd_3053463 : Nat := 4983230072969 + 3 ^ 40 * 3053463 * 2
def baseEnd_3053463 : Nat := 1045262786479794697113257

theorem tailTrace_3053463 : CollatzResearch.WordTrace tailWord_3053463 prefixEnd_3053463 1045262786479794697113257 := by
  unfold tailWord_3053463
  simp only [CollatzResearch.WordTrace]
  refine ⟨111368944936832515807573043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74245963291221677205048695 111368944936832515807573043)
  ·
    refine ⟨167053417405248773711359565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111368944936832515807573043 167053417405248773711359565)
    ·
      refine ⟨62645031526968290141759837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167053417405248773711359565 62645031526968290141759837)
      ·
        refine ⟨23491886822613108803159939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62645031526968290141759837 23491886822613108803159939)
        ·
          refine ⟨35237830233919663204739909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491886822613108803159939 35237830233919663204739909)
          ·
            refine ⟨6607093168859936850888733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35237830233919663204739909 6607093168859936850888733)
            ·
              refine ⟨2477659938322476319083275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6607093168859936850888733 2477659938322476319083275)
              ·
                refine ⟨3716489907483714478624913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477659938322476319083275 3716489907483714478624913)
                ·
                  refine ⟨2787367430612785858968685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716489907483714478624913 2787367430612785858968685)
                  ·
                    refine ⟨1045262786479794697113257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787367430612785858968685 1045262786479794697113257)
                    ·
                      rfl

theorem cell22_3053463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_3053463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053463 prefixEnd_3053463 := by exact prefixLift 3053463
  have htrace : WordTrace (prefixWord ++ tailWord_3053463) baseStart_3053463 baseEnd_3053463 := by
    simpa [prefixWord, tailWord_3053463, baseEnd_3053463] using wordTrace_append hprefix tailTrace_3053463
  have hstable : (prefixWord ++ tailWord_3053463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053463).length < 2 ^ (prefixWord ++ tailWord_3053463).sum := by decide
  have hdescent : baseEnd_3053463 < baseStart_3053463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053476 : List Nat := [2, 3, 1, 2, 1, 5, 2, 6]
def baseStart_3053476 : Nat := 118140960795 + 3053476 * 2 ^ 59
def prefixEnd_3053476 : Nat := 4983230072969 + 3 ^ 40 * 3053476 * 2
def baseEnd_3053476 : Nat := 116140804071718555170913

theorem tailTrace_3053476 : CollatzResearch.WordTrace tailWord_3053476 prefixEnd_3053476 116140804071718555170913 := by
  unfold tailWord_3053476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684709542892709513898141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74246279390523612685197521 55684709542892709513898141)
  ·
    refine ⟨20881766078584766067711803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55684709542892709513898141 20881766078584766067711803)
    ·
      refine ⟨31322649117877149101567705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20881766078584766067711803 31322649117877149101567705)
      ·
        refine ⟨23491986838407861826175779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31322649117877149101567705 23491986838407861826175779)
        ·
          refine ⟨35237980257611792739263669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491986838407861826175779 35237980257611792739263669)
          ·
            refine ⟨3303560649151105569305969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35237980257611792739263669 3303560649151105569305969)
            ·
              refine ⟨2477670486863329176979477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303560649151105569305969 2477670486863329176979477)
              ·
                refine ⟨116140804071718555170913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2477670486863329176979477 116140804071718555170913)
                ·
                  rfl

theorem cell22_3053476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_3053476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053476 prefixEnd_3053476 := by exact prefixLift 3053476
  have htrace : WordTrace (prefixWord ++ tailWord_3053476) baseStart_3053476 baseEnd_3053476 := by
    simpa [prefixWord, tailWord_3053476, baseEnd_3053476] using wordTrace_append hprefix tailTrace_3053476
  have hstable : (prefixWord ++ tailWord_3053476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053476).length < 2 ^ (prefixWord ++ tailWord_3053476).sum := by decide
  have hdescent : baseEnd_3053476 < baseStart_3053476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053487 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 9]
def baseStart_3053487 : Nat := 118140960795 + 3053487 * 2 ^ 59
def prefixEnd_3053487 : Nat := 4983230072969 + 3 ^ 40 * 3053487 * 2
def baseEnd_3053487 : Nat := 348423667390088878171061

theorem tailTrace_3053487 : CollatzResearch.WordTrace tailWord_3053487 prefixEnd_3053487 348423667390088878171061 := by
  unfold tailWord_3053487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111369820288745567906446715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74246546859163711937631143 111369820288745567906446715)
  ·
    refine ⟨167054730433118351859670073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111369820288745567906446715 167054730433118351859670073)
    ·
      refine ⟨125291047824838763894752555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167054730433118351859670073 125291047824838763894752555)
      ·
        refine ⟨187936571737258145842128833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125291047824838763894752555 187936571737258145842128833)
        ·
          refine ⟨140952428802943609381596625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187936571737258145842128833 140952428802943609381596625)
          ·
            refine ⟨105714321602207707036197469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140952428802943609381596625 105714321602207707036197469)
            ·
              refine ⟨39642870600827890138574051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105714321602207707036197469 39642870600827890138574051)
              ·
                refine ⟨59464305901241835207861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39642870600827890138574051 59464305901241835207861077)
                ·
                  refine ⟨348423667390088878171061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59464305901241835207861077 348423667390088878171061)
                  ·
                    rfl

theorem cell22_3053487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_3053487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053487 prefixEnd_3053487 := by exact prefixLift 3053487
  have htrace : WordTrace (prefixWord ++ tailWord_3053487) baseStart_3053487 baseEnd_3053487 := by
    simpa [prefixWord, tailWord_3053487, baseEnd_3053487] using wordTrace_append hprefix tailTrace_3053487
  have hstable : (prefixWord ++ tailWord_3053487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053487).length < 2 ^ (prefixWord ++ tailWord_3053487).sum := by decide
  have hdescent : baseEnd_3053487 < baseStart_3053487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053504 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_3053504 : Nat := 118140960795 + 3053504 * 2 ^ 59
def prefixEnd_3053504 : Nat := 4983230072969 + 3 ^ 40 * 3053504 * 2
def baseEnd_3053504 : Nat := 348425607205894752279377

theorem tailTrace_3053504 : CollatzResearch.WordTrace tailWord_3053504 prefixEnd_3053504 348425607205894752279377 := by
  unfold tailWord_3053504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55685220164841989904907783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74246960219789319873210377 55685220164841989904907783)
  ·
    refine ⟨83527830247262984857361675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55685220164841989904907783 83527830247262984857361675)
    ·
      refine ⟨125291745370894477286042513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83527830247262984857361675 125291745370894477286042513)
      ·
        refine ⟨93968809028170857964531885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125291745370894477286042513 93968809028170857964531885)
        ·
          refine ⟨35238303385564071736699457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93968809028170857964531885 35238303385564071736699457)
          ·
            refine ⟨26428727539173053802524593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35238303385564071736699457 26428727539173053802524593)
            ·
              refine ⟨19821545654379790351893445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26428727539173053802524593 19821545654379790351893445)
              ·
                refine ⟨3716539810196210690980021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19821545654379790351893445 3716539810196210690980021)
                ·
                  refine ⟨348425607205894752279377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3716539810196210690980021 348425607205894752279377)
                  ·
                    rfl

theorem cell22_3053504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_3053504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053504 prefixEnd_3053504 := by exact prefixLift 3053504
  have htrace : WordTrace (prefixWord ++ tailWord_3053504) baseStart_3053504 baseEnd_3053504 := by
    simpa [prefixWord, tailWord_3053504, baseEnd_3053504] using wordTrace_append hprefix tailTrace_3053504
  have hstable : (prefixWord ++ tailWord_3053504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053504).length < 2 ^ (prefixWord ++ tailWord_3053504).sum := by decide
  have hdescent : baseEnd_3053504 < baseStart_3053504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053564 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3053564 : Nat := 118140960795 + 3053564 * 2 ^ 59
def prefixEnd_3053564 : Nat := 4983230072969 + 3 ^ 40 * 3053564 * 2
def baseEnd_3053564 : Nat := 1045297360843864100337947

theorem tailTrace_3053564 : CollatzResearch.WordTrace tailWord_3053564 prefixEnd_3053564 1045297360843864100337947 := by
  unfold tailWord_3053564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686314354733305028499873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74248419139644406704666497 55686314354733305028499873)
  ·
    refine ⟨41764735766049978771374905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55686314354733305028499873 41764735766049978771374905)
    ·
      refine ⟨31323551824537484078531179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41764735766049978771374905 31323551824537484078531179)
      ·
        refine ⟨46985327736806226117796769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31323551824537484078531179 46985327736806226117796769)
        ·
          refine ⟨35238995802604669588347577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46985327736806226117796769 35238995802604669588347577)
          ·
            refine ⟨26429246851953502191260683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35238995802604669588347577 26429246851953502191260683)
            ·
              refine ⟨39643870277930253286891025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26429246851953502191260683 39643870277930253286891025)
              ·
                refine ⟨29732902708447689965168269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39643870277930253286891025 29732902708447689965168269)
                ·
                  refine ⟨11149838515667883736938101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29732902708447689965168269 11149838515667883736938101)
                  ·
                    refine ⟨1045297360843864100337947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11149838515667883736938101 1045297360843864100337947)
                    ·
                      rfl

theorem cell22_3053564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3053564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053564 prefixEnd_3053564 := by exact prefixLift 3053564
  have htrace : WordTrace (prefixWord ++ tailWord_3053564) baseStart_3053564 baseEnd_3053564 := by
    simpa [prefixWord, tailWord_3053564, baseEnd_3053564] using wordTrace_append hprefix tailTrace_3053564
  have hstable : (prefixWord ++ tailWord_3053564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053564).length < 2 ^ (prefixWord ++ tailWord_3053564).sum := by decide
  have hdescent : baseEnd_3053564 < baseStart_3053564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053579 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_3053579 : Nat := 118140960795 + 3053579 * 2 ^ 59
def prefixEnd_3053579 : Nat := 4983230072969 + 3 ^ 40 * 3053579 * 2
def baseEnd_3053579 : Nat := 1045302495650409061212901

theorem tailTrace_3053579 : CollatzResearch.WordTrace tailWord_3053579 prefixEnd_3053579 1045302495650409061212901 := by
  unfold tailWord_3053579
  simp only [CollatzResearch.WordTrace]
  refine ⟨111373175804412267618795791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74248783869608178412530527 111373175804412267618795791)
  ·
    refine ⟨167059763706618401428193687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111373175804412267618795791 167059763706618401428193687)
    ·
      refine ⟨250589645559927602142290531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167059763706618401428193687 250589645559927602142290531)
      ·
        refine ⟨375884468339891403213435797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250589645559927602142290531 375884468339891403213435797)
        ·
          refine ⟨17619584453432409525629803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 375884468339891403213435797 17619584453432409525629803)
          ·
            refine ⟨26429376680148614288444705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17619584453432409525629803 26429376680148614288444705)
            ·
              refine ⟨19822032510111460716333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26429376680148614288444705 19822032510111460716333529)
              ·
                refine ⟨14866524382583595537250147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19822032510111460716333529 14866524382583595537250147)
                ·
                  refine ⟨22299786573875393305875221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14866524382583595537250147 22299786573875393305875221)
                  ·
                    refine ⟨1045302495650409061212901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22299786573875393305875221 1045302495650409061212901)
                    ·
                      rfl

theorem cell22_3053579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_3053579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053579 prefixEnd_3053579 := by exact prefixLift 3053579
  have htrace : WordTrace (prefixWord ++ tailWord_3053579) baseStart_3053579 baseEnd_3053579 := by
    simpa [prefixWord, tailWord_3053579, baseEnd_3053579] using wordTrace_append hprefix tailTrace_3053579
  have hstable : (prefixWord ++ tailWord_3053579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053579).length < 2 ^ (prefixWord ++ tailWord_3053579).sum := by decide
  have hdescent : baseEnd_3053579 < baseStart_3053579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053596 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3053596 : Nat := 118140960795 + 3053596 * 2 ^ 59
def prefixEnd_3053596 : Nat := 4983230072969 + 3 ^ 40 * 3053596 * 2
def baseEnd_3053596 : Nat := 1045308315097826683537849

theorem tailTrace_3053596 : CollatzResearch.WordTrace tailWord_3053596 prefixEnd_3053596 1045308315097826683537849 := by
  unfold tailWord_3053596
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686897922675339761082321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74249197230233786348109761 55686897922675339761082321)
  ·
    refine ⟨41765173442006504820811741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55686897922675339761082321 41765173442006504820811741)
    ·
      refine ⟨15661940040752439307804403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41765173442006504820811741 15661940040752439307804403)
      ·
        refine ⟨23492910061128658961706605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661940040752439307804403 23492910061128658961706605)
        ·
          refine ⟨8809841272923247110639977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23492910061128658961706605 8809841272923247110639977)
          ·
            refine ⟨6607380954692435332979983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8809841272923247110639977 6607380954692435332979983)
            ·
              refine ⟨9911071432038652999469975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607380954692435332979983 9911071432038652999469975)
              ·
                refine ⟨14866607148057979499204963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9911071432038652999469975 14866607148057979499204963)
                ·
                  refine ⟨22299910722086969248807445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14866607148057979499204963 22299910722086969248807445)
                  ·
                    refine ⟨1045308315097826683537849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22299910722086969248807445 1045308315097826683537849)
                    ·
                      rfl

theorem cell22_3053596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3053596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053596 prefixEnd_3053596 := by exact prefixLift 3053596
  have htrace : WordTrace (prefixWord ++ tailWord_3053596) baseStart_3053596 baseEnd_3053596 := by
    simpa [prefixWord, tailWord_3053596, baseEnd_3053596] using wordTrace_append hprefix tailTrace_3053596
  have hstable : (prefixWord ++ tailWord_3053596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053596).length < 2 ^ (prefixWord ++ tailWord_3053596).sum := by decide
  have hdescent : baseEnd_3053596 < baseStart_3053596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053662 : List Nat := [4, 4, 1, 1, 3, 1, 8]
def baseStart_3053662 : Nat := 118140960795 + 3053662 * 2 ^ 59
def prefixEnd_3053662 : Nat := 4983230072969 + 3 ^ 40 * 3053662 * 2
def baseEnd_3053662 : Nat := 38715959564689796718061

theorem tailTrace_3053662 : CollatzResearch.WordTrace tailWord_3053662 prefixEnd_3053662 38715959564689796718061 := by
  unfold tailWord_3053662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922025382888946599258405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74250802042074381862711493 13922025382888946599258405)
  ·
    refine ⟨2610379759291677487360951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13922025382888946599258405 2610379759291677487360951)
    ·
      refine ⟨3915569638937516231041427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610379759291677487360951 3915569638937516231041427)
      ·
        refine ⟨5873354458406274346562141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915569638937516231041427 5873354458406274346562141)
        ·
          refine ⟨2202507921902352879960803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5873354458406274346562141 2202507921902352879960803)
          ·
            refine ⟨3303761882853529319941205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202507921902352879960803 3303761882853529319941205)
            ·
              refine ⟨38715959564689796718061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3303761882853529319941205 38715959564689796718061)
              ·
                rfl

theorem cell22_3053662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 8].length) (baseStart_3053662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053662 prefixEnd_3053662 := by exact prefixLift 3053662
  have htrace : WordTrace (prefixWord ++ tailWord_3053662) baseStart_3053662 baseEnd_3053662 := by
    simpa [prefixWord, tailWord_3053662, baseEnd_3053662] using wordTrace_append hprefix tailTrace_3053662
  have hstable : (prefixWord ++ tailWord_3053662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053662).length < 2 ^ (prefixWord ++ tailWord_3053662).sum := by decide
  have hdescent : baseEnd_3053662 < baseStart_3053662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053677 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3053677 : Nat := 118140960795 + 3053677 * 2 ^ 59
def prefixEnd_3053677 : Nat := 4983230072969 + 3 ^ 40 * 3053677 * 2
def baseEnd_3053677 : Nat := 1045336043053169472262601

theorem tailTrace_3053677 : CollatzResearch.WordTrace tailWord_3053677 prefixEnd_3053677 1045336043053169472262601 := by
  unfold tailWord_3053677
  simp only [CollatzResearch.WordTrace]
  refine ⟨111376750158057230355863285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74251166772038153570575523 111376750158057230355863285)
  ·
    refine ⟨10441570327317865345862183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111376750158057230355863285 10441570327317865345862183)
    ·
      refine ⟨15662355490976798018793275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10441570327317865345862183 15662355490976798018793275)
      ·
        refine ⟨23493533236465197028189913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15662355490976798018793275 23493533236465197028189913)
        ·
          refine ⟨17620149927348897771142435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23493533236465197028189913 17620149927348897771142435)
          ·
            refine ⟨26430224891023346656713653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17620149927348897771142435 26430224891023346656713653)
            ·
              refine ⟨2477833583533438749066905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26430224891023346656713653 2477833583533438749066905)
              ·
                refine ⟨1858375187650079061800179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477833583533438749066905 1858375187650079061800179)
                ·
                  refine ⟨2787562781475118592700269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858375187650079061800179 2787562781475118592700269)
                  ·
                    refine ⟨1045336043053169472262601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787562781475118592700269 1045336043053169472262601)
                    ·
                      rfl

theorem cell22_3053677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3053677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053677 prefixEnd_3053677 := by exact prefixLift 3053677
  have htrace : WordTrace (prefixWord ++ tailWord_3053677) baseStart_3053677 baseEnd_3053677 := by
    simpa [prefixWord, tailWord_3053677, baseEnd_3053677] using wordTrace_append hprefix tailTrace_3053677
  have hstable : (prefixWord ++ tailWord_3053677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053677).length < 2 ^ (prefixWord ++ tailWord_3053677).sum := by decide
  have hdescent : baseEnd_3053677 < baseStart_3053677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053703 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3053703 : Nat := 118140960795 + 3053703 * 2 ^ 59
def prefixEnd_3053703 : Nat := 4983230072969 + 3 ^ 40 * 3053703 * 2
def baseEnd_3053703 : Nat := 1045344943384514071112521

theorem tailTrace_3053703 : CollatzResearch.WordTrace tailWord_3053703 prefixEnd_3053703 1045344943384514071112521 := by
  unfold tailWord_3053703
  simp only [CollatzResearch.WordTrace]
  refine ⟨111377698455963036796309763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74251798970642024530873175 111377698455963036796309763)
  ·
    refine ⟨167066547683944555194464645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111377698455963036796309763 167066547683944555194464645)
    ·
      refine ⟨31324977690739604098962121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167066547683944555194464645 31324977690739604098962121)
      ·
        refine ⟨23493733268054703074221591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31324977690739604098962121 23493733268054703074221591)
        ·
          refine ⟨35240599902082054611332387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23493733268054703074221591 35240599902082054611332387)
          ·
            refine ⟨52860899853123081916998581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35240599902082054611332387 52860899853123081916998581)
            ·
              refine ⟨4955709361230288929718617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52860899853123081916998581 4955709361230288929718617)
              ·
                refine ⟨3716782020922716697288963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4955709361230288929718617 3716782020922716697288963)
                ·
                  refine ⟨5575173031384075045933445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716782020922716697288963 5575173031384075045933445)
                  ·
                    refine ⟨1045344943384514071112521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575173031384075045933445 1045344943384514071112521)
                    ·
                      rfl

theorem cell22_3053703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3053703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053703 prefixEnd_3053703 := by exact prefixLift 3053703
  have htrace : WordTrace (prefixWord ++ tailWord_3053703) baseStart_3053703 baseEnd_3053703 := by
    simpa [prefixWord, tailWord_3053703, baseEnd_3053703] using wordTrace_append hprefix tailTrace_3053703
  have hstable : (prefixWord ++ tailWord_3053703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053703).length < 2 ^ (prefixWord ++ tailWord_3053703).sum := by decide
  have hdescent : baseEnd_3053703 < baseStart_3053703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053821 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3053821 : Nat := 118140960795 + 3053821 * 2 ^ 59
def prefixEnd_3053821 : Nat := 4983230072969 + 3 ^ 40 * 3053821 * 2
def baseEnd_3053821 : Nat := 1045385337196001096662159

theorem tailTrace_3053821 : CollatzResearch.WordTrace tailWord_3053821 prefixEnd_3053821 1045385337196001096662159 := by
  unfold tailWord_3053821
  simp only [CollatzResearch.WordTrace]
  refine ⟨111382002269535542949105317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74254668179690361966070211 111382002269535542949105317)
  ·
    refine ⟨20884125425537914302957247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111382002269535542949105317 20884125425537914302957247)
    ·
      refine ⟨31326188138306871454435871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20884125425537914302957247 31326188138306871454435871)
      ·
        refine ⟨46989282207460307181653807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31326188138306871454435871 46989282207460307181653807)
        ·
          refine ⟨70483923311190460772480711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46989282207460307181653807 70483923311190460772480711)
          ·
            refine ⟨105725884966785691158721067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70483923311190460772480711 105725884966785691158721067)
            ·
              refine ⟨158588827450178536738081601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105725884966785691158721067 158588827450178536738081601)
              ·
                refine ⟨118941620587633902553561201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158588827450178536738081601 118941620587633902553561201)
                ·
                  refine ⟨89206215440725426915170901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118941620587633902553561201 89206215440725426915170901)
                  ·
                    refine ⟨1045385337196001096662159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89206215440725426915170901 1045385337196001096662159)
                    ·
                      rfl

theorem cell22_3053821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3053821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053821 prefixEnd_3053821 := by exact prefixLift 3053821
  have htrace : WordTrace (prefixWord ++ tailWord_3053821) baseStart_3053821 baseEnd_3053821 := by
    simpa [prefixWord, tailWord_3053821, baseEnd_3053821] using wordTrace_append hprefix tailTrace_3053821
  have hstable : (prefixWord ++ tailWord_3053821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053821).length < 2 ^ (prefixWord ++ tailWord_3053821).sum := by decide
  have hdescent : baseEnd_3053821 < baseStart_3053821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053889 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3053889 : Nat := 118140960795 + 3053889 * 2 ^ 59
def prefixEnd_3053889 : Nat := 4983230072969 + 3 ^ 40 * 3053889 * 2
def baseEnd_3053889 : Nat := 1045408614985671585961951

theorem tailTrace_3053889 : CollatzResearch.WordTrace tailWord_3053889 prefixEnd_3053889 1045408614985671585961951 := by
  unfold tailWord_3053889
  simp only [CollatzResearch.WordTrace]
  refine ⟨111384482433289190562580721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74256321622192793708387147 111384482433289190562580721)
  ·
    refine ⟨83538361824966892921935541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111384482433289190562580721 83538361824966892921935541)
    ·
      refine ⟨7831721421090646211431457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83538361824966892921935541 7831721421090646211431457)
      ·
        refine ⟨5873791065817984658573593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7831721421090646211431457 5873791065817984658573593)
        ·
          refine ⟨4405343299363488493930195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5873791065817984658573593 4405343299363488493930195)
          ·
            refine ⟨6608014949045232740895293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405343299363488493930195 6608014949045232740895293)
            ·
              refine ⟨2478005605891962277835735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6608014949045232740895293 2478005605891962277835735)
              ·
                refine ⟨3717008408837943416753603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478005605891962277835735 3717008408837943416753603)
                ·
                  refine ⟨5575512613256915125130405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717008408837943416753603 5575512613256915125130405)
                  ·
                    refine ⟨1045408614985671585961951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575512613256915125130405 1045408614985671585961951)
                    ·
                      rfl

theorem cell22_3053889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3053889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053889 prefixEnd_3053889 := by exact prefixLift 3053889
  have htrace : WordTrace (prefixWord ++ tailWord_3053889) baseStart_3053889 baseEnd_3053889 := by
    simpa [prefixWord, tailWord_3053889, baseEnd_3053889] using wordTrace_append hprefix tailTrace_3053889
  have hstable : (prefixWord ++ tailWord_3053889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053889).length < 2 ^ (prefixWord ++ tailWord_3053889).sum := by decide
  have hdescent : baseEnd_3053889 < baseStart_3053889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053947 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 1, 3]
def baseStart_3053947 : Nat := 118140960795 + 3053947 * 2 ^ 59
def prefixEnd_3053947 : Nat := 4983230072969 + 3 ^ 40 * 3053947 * 2
def baseEnd_3053947 : Nat := 1045428469570978768011773

theorem tailTrace_3053947 : CollatzResearch.WordTrace tailWord_3053947 prefixEnd_3053947 1045428469570978768011773 := by
  unfold tailWord_3053947
  simp only [CollatzResearch.WordTrace]
  refine ⟨111386597867079066468192095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74257731911386044312128063 111386597867079066468192095)
  ·
    refine ⟨167079896800618599702288143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111386597867079066468192095 167079896800618599702288143)
    ·
      refine ⟨250619845200927899553432215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167079896800618599702288143 250619845200927899553432215)
      ·
        refine ⟨375929767801391849330148323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250619845200927899553432215 375929767801391849330148323)
        ·
          refine ⟨563894651702087773995222485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375929767801391849330148323 563894651702087773995222485)
          ·
            refine ⟨13216280899267682203013027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 563894651702087773995222485 13216280899267682203013027)
            ·
              refine ⟨19824421348901523304519541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216280899267682203013027 19824421348901523304519541)
              ·
                refine ⟨1858539501459517809798707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19824421348901523304519541 1858539501459517809798707)
                ·
                  refine ⟨2787809252189276714698061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858539501459517809798707 2787809252189276714698061)
                  ·
                    refine ⟨1045428469570978768011773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787809252189276714698061 1045428469570978768011773)
                    ·
                      rfl

theorem cell22_3053947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 3].length) (baseStart_3053947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3053947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3053947 prefixEnd_3053947 := by exact prefixLift 3053947
  have htrace : WordTrace (prefixWord ++ tailWord_3053947) baseStart_3053947 baseEnd_3053947 := by
    simpa [prefixWord, tailWord_3053947, baseEnd_3053947] using wordTrace_append hprefix tailTrace_3053947
  have hstable : (prefixWord ++ tailWord_3053947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053947).length < 2 ^ (prefixWord ++ tailWord_3053947).sum := by decide
  have hdescent : baseEnd_3053947 < baseStart_3053947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054189 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3054189 : Nat := 118140960795 + 3054189 * 2 ^ 59
def prefixEnd_3054189 : Nat := 4983230072969 + 3 ^ 40 * 3054189 * 2
def baseEnd_3054189 : Nat := 1045511311116570803461031

theorem tailTrace_3054189 : CollatzResearch.WordTrace tailWord_3054189 prefixEnd_3054189 1045511311116570803461031 := by
  unfold tailWord_3054189
  simp only [CollatzResearch.WordTrace]
  refine ⟨111395424332202341798501621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74263616221468227865667747 111395424332202341798501621)
  ·
    refine ⟨10443321031143969543609527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111395424332202341798501621 10443321031143969543609527)
    ·
      refine ⟨15664981546715954315414291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10443321031143969543609527 15664981546715954315414291)
      ·
        refine ⟨23497472320073931473121437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15664981546715954315414291 23497472320073931473121437)
        ·
          refine ⟨8811552120027724302420539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23497472320073931473121437 8811552120027724302420539)
          ·
            refine ⟨13217328180041586453630809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811552120027724302420539 13217328180041586453630809)
            ·
              refine ⟨9912996135031189840223107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13217328180041586453630809 9912996135031189840223107)
              ·
                refine ⟨14869494202546784760334661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9912996135031189840223107 14869494202546784760334661)
                ·
                  refine ⟨2788030162977522142562749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14869494202546784760334661 2788030162977522142562749)
                  ·
                    refine ⟨1045511311116570803461031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788030162977522142562749 1045511311116570803461031)
                    ·
                      rfl

theorem cell22_3054189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3054189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054189 prefixEnd_3054189 := by exact prefixLift 3054189
  have htrace : WordTrace (prefixWord ++ tailWord_3054189) baseStart_3054189 baseEnd_3054189 := by
    simpa [prefixWord, tailWord_3054189, baseEnd_3054189] using wordTrace_append hprefix tailTrace_3054189
  have hstable : (prefixWord ++ tailWord_3054189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054189).length < 2 ^ (prefixWord ++ tailWord_3054189).sum := by decide
  have hdescent : baseEnd_3054189 < baseStart_3054189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054217 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_3054217 : Nat := 118140960795 + 3054217 * 2 ^ 59
def prefixEnd_3054217 : Nat := 4983230072969 + 3 ^ 40 * 3054217 * 2
def baseEnd_3054217 : Nat := 1045520896088788063760945

theorem tailTrace_3054217 : CollatzResearch.WordTrace tailWord_3054217 prefixEnd_3054217 1045520896088788063760945 := by
  unfold tailWord_3054217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111396445576100902580520905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74264297050733935053680603 111396445576100902580520905)
  ·
    refine ⟨83547334182075676935390679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111396445576100902580520905 83547334182075676935390679)
    ·
      refine ⟨125321001273113515403086019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83547334182075676935390679 125321001273113515403086019)
      ·
        refine ⟨187981501909670273104629029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125321001273113515403086019 187981501909670273104629029)
        ·
          refine ⟨35246531608063176207117943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187981501909670273104629029 35246531608063176207117943)
          ·
            refine ⟨52869797412094764310676915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35246531608063176207117943 52869797412094764310676915)
            ·
              refine ⟨79304696118142146466015373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52869797412094764310676915 79304696118142146466015373)
              ·
                refine ⟨29739261044303304924755765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79304696118142146466015373 29739261044303304924755765)
                ·
                  refine ⟨2788055722903434836695853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29739261044303304924755765 2788055722903434836695853)
                  ·
                    refine ⟨1045520896088788063760945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788055722903434836695853 1045520896088788063760945)
                    ·
                      rfl

theorem cell22_3054217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_3054217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054217 prefixEnd_3054217 := by exact prefixLift 3054217
  have htrace : WordTrace (prefixWord ++ tailWord_3054217) baseStart_3054217 baseEnd_3054217 := by
    simpa [prefixWord, tailWord_3054217, baseEnd_3054217] using wordTrace_append hprefix tailTrace_3054217
  have hstable : (prefixWord ++ tailWord_3054217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054217).length < 2 ^ (prefixWord ++ tailWord_3054217).sum := by decide
  have hdescent : baseEnd_3054217 < baseStart_3054217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054309 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 6]
def baseStart_3054309 : Nat := 118140960795 + 3054309 * 2 ^ 59
def prefixEnd_3054309 : Nat := 4983230072969 + 3 ^ 40 * 3054309 * 2
def baseEnd_3054309 : Nat := 348517463189643496820221

theorem tailTrace_3054309 : CollatzResearch.WordTrace tailWord_3054309 prefixEnd_3054309 348517463189643496820221 := by
  unfold tailWord_3054309
  simp only [CollatzResearch.WordTrace]
  refine ⟨111399801091767602292869981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74266534061178401528579987 111399801091767602292869981)
  ·
    refine ⟨41774925409412850859826243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111399801091767602292869981 41774925409412850859826243)
    ·
      refine ⟨62662388114119276289739365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41774925409412850859826243 62662388114119276289739365)
      ·
        refine ⟨11749197771397364304326131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62662388114119276289739365 11749197771397364304326131)
        ·
          refine ⟨17623796657096046456489197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749197771397364304326131 17623796657096046456489197)
          ·
            refine ⟨6608923746411017421183449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17623796657096046456489197 6608923746411017421183449)
            ·
              refine ⟨4956692809808263065887587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6608923746411017421183449 4956692809808263065887587)
              ·
                refine ⟨7435039214712394598831381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956692809808263065887587 7435039214712394598831381)
                ·
                  refine ⟨348517463189643496820221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7435039214712394598831381 348517463189643496820221)
                  ·
                    rfl

theorem cell22_3054309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_3054309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054309 prefixEnd_3054309 := by exact prefixLift 3054309
  have htrace : WordTrace (prefixWord ++ tailWord_3054309) baseStart_3054309 baseEnd_3054309 := by
    simpa [prefixWord, tailWord_3054309, baseEnd_3054309] using wordTrace_append hprefix tailTrace_3054309
  have hstable : (prefixWord ++ tailWord_3054309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054309).length < 2 ^ (prefixWord ++ tailWord_3054309).sum := by decide
  have hdescent : baseEnd_3054309 < baseStart_3054309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054343 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 4]
def baseStart_3054343 : Nat := 118140960795 + 3054343 * 2 ^ 59
def prefixEnd_3054343 : Nat := 4983230072969 + 3 ^ 40 * 3054343 * 2
def baseEnd_3054343 : Nat := 348521342821255245036853

theorem tailTrace_3054343 : CollatzResearch.WordTrace tailWord_3054343 prefixEnd_3054343 348521342821255245036853 := by
  unfold tailWord_3054343
  simp only [CollatzResearch.WordTrace]
  refine ⟨111401041173644426099607683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74267360782429617399738455 111401041173644426099607683)
  ·
    refine ⟨167101561760466639149411525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111401041173644426099607683 167101561760466639149411525)
    ·
      refine ⟨31331542830087494840514661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167101561760466639149411525 31331542830087494840514661)
      ·
        refine ⟨5874664280641405282596499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31331542830087494840514661 5874664280641405282596499)
        ·
          refine ⟨8811996420962107923894749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874664280641405282596499 8811996420962107923894749)
          ·
            refine ⟨3304498657860790471460531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8811996420962107923894749 3304498657860790471460531)
            ·
              refine ⟨4956747986791185707190797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304498657860790471460531 4956747986791185707190797)
              ·
                refine ⟨1858780495046694640196549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4956747986791185707190797 1858780495046694640196549)
                ·
                  refine ⟨348521342821255245036853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858780495046694640196549 348521342821255245036853)
                  ·
                    rfl

theorem cell22_3054343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 4].length) (baseStart_3054343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054343 prefixEnd_3054343 := by exact prefixLift 3054343
  have htrace : WordTrace (prefixWord ++ tailWord_3054343) baseStart_3054343 baseEnd_3054343 := by
    simpa [prefixWord, tailWord_3054343, baseEnd_3054343] using wordTrace_append hprefix tailTrace_3054343
  have hstable : (prefixWord ++ tailWord_3054343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054343).length < 2 ^ (prefixWord ++ tailWord_3054343).sum := by decide
  have hdescent : baseEnd_3054343 < baseStart_3054343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054420 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3054420 : Nat := 118140960795 + 3054420 * 2 ^ 59
def prefixEnd_3054420 : Nat := 4983230072969 + 3 ^ 40 * 3054420 * 2
def baseEnd_3054420 : Nat := 1045590387137363200935323

theorem tailTrace_3054420 : CollatzResearch.WordTrace tailWord_3054420 prefixEnd_3054420 1045590387137363200935323 := by
  unfold tailWord_3054420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55701924797182734125080357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74269233062910312166773809 55701924797182734125080357)
  ·
    refine ⟨10444110899471762648452567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55701924797182734125080357 10444110899471762648452567)
    ·
      refine ⟨15666166349207643972678851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10444110899471762648452567 15666166349207643972678851)
      ·
        refine ⟨23499249523811465959018277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15666166349207643972678851 23499249523811465959018277)
        ·
          refine ⟨4406109285714649867315927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23499249523811465959018277 4406109285714649867315927)
          ·
            refine ⟨6609163928571974800973891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406109285714649867315927 6609163928571974800973891)
            ·
              refine ⟨9913745892857962201460837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6609163928571974800973891 9913745892857962201460837)
              ·
                refine ⟨1858827354910867912773907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9913745892857962201460837 1858827354910867912773907)
                ·
                  refine ⟨2788241032366301869160861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858827354910867912773907 2788241032366301869160861)
                  ·
                    refine ⟨1045590387137363200935323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788241032366301869160861 1045590387137363200935323)
                    ·
                      rfl

theorem cell22_3054420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3054420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054420 prefixEnd_3054420 := by exact prefixLift 3054420
  have htrace : WordTrace (prefixWord ++ tailWord_3054420) baseStart_3054420 baseEnd_3054420 := by
    simpa [prefixWord, tailWord_3054420, baseEnd_3054420] using wordTrace_append hprefix tailTrace_3054420
  have hstable : (prefixWord ++ tailWord_3054420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054420).length < 2 ^ (prefixWord ++ tailWord_3054420).sum := by decide
  have hdescent : baseEnd_3054420 < baseStart_3054420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054444 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_3054444 : Nat := 118140960795 + 3054444 * 2 ^ 59
def prefixEnd_3054444 : Nat := 4983230072969 + 3 ^ 40 * 3054444 * 2
def baseEnd_3054444 : Nat := 348532867609278379445083

theorem tailTrace_3054444 : CollatzResearch.WordTrace tailWord_3054444 prefixEnd_3054444 348532867609278379445083 := by
  unfold tailWord_3054444
  simp only [CollatzResearch.WordTrace]
  refine ⟨55702362473139260174517193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74269816630852346899356257 55702362473139260174517193)
  ·
    refine ⟨41776771854854445130887895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55702362473139260174517193 41776771854854445130887895)
    ·
      refine ⟨62665157782281667696331843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41776771854854445130887895 62665157782281667696331843)
      ·
        refine ⟨93997736673422501544497765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62665157782281667696331843 93997736673422501544497765)
        ·
          refine ⟨17624575626266719039593331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93997736673422501544497765 17624575626266719039593331)
          ·
            refine ⟨26436863439400078559389997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17624575626266719039593331 26436863439400078559389997)
            ·
              refine ⟨9913823789775029459771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26436863439400078559389997 9913823789775029459771249)
              ·
                refine ⟨7435367842331272094828437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9913823789775029459771249 7435367842331272094828437)
                ·
                  refine ⟨348532867609278379445083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7435367842331272094828437 348532867609278379445083)
                  ·
                    rfl

theorem cell22_3054444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_3054444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054444 prefixEnd_3054444 := by exact prefixLift 3054444
  have htrace : WordTrace (prefixWord ++ tailWord_3054444) baseStart_3054444 baseEnd_3054444 := by
    simpa [prefixWord, tailWord_3054444, baseEnd_3054444] using wordTrace_append hprefix tailTrace_3054444
  have hstable : (prefixWord ++ tailWord_3054444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054444).length < 2 ^ (prefixWord ++ tailWord_3054444).sum := by decide
  have hdescent : baseEnd_3054444 < baseStart_3054444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054459 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_3054459 : Nat := 118140960795 + 3054459 * 2 ^ 59
def prefixEnd_3054459 : Nat := 4983230072969 + 3 ^ 40 * 3054459 * 2
def baseEnd_3054459 : Nat := 1045603737634380099210203

theorem tailTrace_3054459 : CollatzResearch.WordTrace tailWord_3054459 prefixEnd_3054459 1045603737634380099210203 := by
  unfold tailWord_3054459
  simp only [CollatzResearch.WordTrace]
  refine ⟨111405272041224177910830431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74270181360816118607220287 111405272041224177910830431)
  ·
    refine ⟨167107908061836266866245647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111405272041224177910830431 167107908061836266866245647)
    ·
      refine ⟨250661862092754400299368471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167107908061836266866245647 250661862092754400299368471)
      ·
        refine ⟨375992793139131600449052707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250661862092754400299368471 375992793139131600449052707)
        ·
          refine ⟨563989189708697400673579061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375992793139131600449052707 563989189708697400673579061)
          ·
            refine ⟨52873986535190381313148037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 563989189708697400673579061 52873986535190381313148037)
            ·
              refine ⟨9913872475348196496215257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52873986535190381313148037 9913872475348196496215257)
              ·
                refine ⟨7435404356511147372161443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9913872475348196496215257 7435404356511147372161443)
                ·
                  refine ⟨11153106534766721058242165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435404356511147372161443 11153106534766721058242165)
                  ·
                    refine ⟨1045603737634380099210203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11153106534766721058242165 1045603737634380099210203)
                    ·
                      rfl

theorem cell22_3054459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_3054459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054459 prefixEnd_3054459 := by exact prefixLift 3054459
  have htrace : WordTrace (prefixWord ++ tailWord_3054459) baseStart_3054459 baseEnd_3054459 := by
    simpa [prefixWord, tailWord_3054459, baseEnd_3054459] using wordTrace_append hprefix tailTrace_3054459
  have hstable : (prefixWord ++ tailWord_3054459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054459).length < 2 ^ (prefixWord ++ tailWord_3054459).sum := by decide
  have hdescent : baseEnd_3054459 < baseStart_3054459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054461 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 4]
def baseStart_3054461 : Nat := 118140960795 + 3054461 * 2 ^ 59
def prefixEnd_3054461 : Nat := 4983230072969 + 3 ^ 40 * 3054461 * 2
def baseEnd_3054461 : Nat := 348534807425084253553399

theorem tailTrace_3054461 : CollatzResearch.WordTrace tailWord_3054461 prefixEnd_3054461 348534807425084253553399 := by
  unfold tailWord_3054461
  simp only [CollatzResearch.WordTrace]
  refine ⟨111405344987216932252403237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74270229991477954834935491 111405344987216932252403237)
  ·
    refine ⟨20888502185103174797325607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111405344987216932252403237 20888502185103174797325607)
    ·
      refine ⟨31332753277654762195988411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20888502185103174797325607 31332753277654762195988411)
      ·
        refine ⟨46999129916482143293982617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31332753277654762195988411 46999129916482143293982617)
        ·
          refine ⟨35249347437361607470486963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46999129916482143293982617 35249347437361607470486963)
          ·
            refine ⟨52874021156042411205730445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35249347437361607470486963 52874021156042411205730445)
            ·
              refine ⟨19827757933515904202148917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52874021156042411205730445 19827757933515904202148917)
              ·
                refine ⟨1858852306267116018951461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19827757933515904202148917 1858852306267116018951461)
                ·
                  refine ⟨348534807425084253553399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858852306267116018951461 348534807425084253553399)
                  ·
                    rfl

theorem cell22_3054461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_3054461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054461 prefixEnd_3054461 := by exact prefixLift 3054461
  have htrace : WordTrace (prefixWord ++ tailWord_3054461) baseStart_3054461 baseEnd_3054461 := by
    simpa [prefixWord, tailWord_3054461, baseEnd_3054461] using wordTrace_append hprefix tailTrace_3054461
  have hstable : (prefixWord ++ tailWord_3054461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054461).length < 2 ^ (prefixWord ++ tailWord_3054461).sum := by decide
  have hdescent : baseEnd_3054461 < baseStart_3054461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054611 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 6, 3]
def baseStart_3054611 : Nat := 118140960795 + 3054611 * 2 ^ 59
def prefixEnd_3054611 : Nat := 4983230072969 + 3 ^ 40 * 3054611 * 2
def baseEnd_3054611 : Nat := 1045655770340702369409737

theorem tailTrace_3054611 : CollatzResearch.WordTrace tailWord_3054611 prefixEnd_3054611 1045655770340702369409737 := by
  unfold tailWord_3054611
  simp only [CollatzResearch.WordTrace]
  refine ⟨111410815936673507870363687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74273877291115671913575791 111410815936673507870363687)
  ·
    refine ⟨167116223905010261805545531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111410815936673507870363687 167116223905010261805545531)
    ·
      refine ⟨250674335857515392708318297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167116223905010261805545531 250674335857515392708318297)
      ·
        refine ⟨188005751893136544531238723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250674335857515392708318297 188005751893136544531238723)
        ·
          refine ⟨282008627839704816796858085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188005751893136544531238723 282008627839704816796858085)
          ·
            refine ⟨52876617719944653149410891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282008627839704816796858085 52876617719944653149410891)
            ·
              refine ⟨79314926579916979724116337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52876617719944653149410891 79314926579916979724116337)
              ·
                refine ⟨59486194934937734793087253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79314926579916979724116337 59486194934937734793087253)
                ·
                  refine ⟨2788415387575206318425965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59486194934937734793087253 2788415387575206318425965)
                  ·
                    refine ⟨1045655770340702369409737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788415387575206318425965 1045655770340702369409737)
                    ·
                      rfl

theorem cell22_3054611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].length) (baseStart_3054611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054611 prefixEnd_3054611 := by exact prefixLift 3054611
  have htrace : WordTrace (prefixWord ++ tailWord_3054611) baseStart_3054611 baseEnd_3054611 := by
    simpa [prefixWord, tailWord_3054611, baseEnd_3054611] using wordTrace_append hprefix tailTrace_3054611
  have hstable : (prefixWord ++ tailWord_3054611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054611).length < 2 ^ (prefixWord ++ tailWord_3054611).sum := by decide
  have hdescent : baseEnd_3054611 < baseStart_3054611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054628 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3054628 : Nat := 118140960795 + 3054628 * 2 ^ 59
def prefixEnd_3054628 : Nat := 4983230072969 + 3 ^ 40 * 3054628 * 2
def baseEnd_3054628 : Nat := 1045661589788119991734685

theorem tailTrace_3054628 : CollatzResearch.WordTrace tailWord_3054628 prefixEnd_3054628 1045661589788119991734685 := by
  unfold tailWord_3054628
  simp only [CollatzResearch.WordTrace]
  refine ⟨55705717988805959886866269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74274290651741279849155025 55705717988805959886866269)
  ·
    refine ⟨20889644245802234957574851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55705717988805959886866269 20889644245802234957574851)
    ·
      refine ⟨31334466368703352436362277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20889644245802234957574851 31334466368703352436362277)
      ·
        refine ⟨5875212444131878581817927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31334466368703352436362277 5875212444131878581817927)
        ·
          refine ⟨8812818666197817872726891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875212444131878581817927 8812818666197817872726891)
          ·
            refine ⟨13219227999296726809090337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812818666197817872726891 13219227999296726809090337)
            ·
              refine ⟨9914420999472545106817753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13219227999296726809090337 9914420999472545106817753)
              ·
                refine ⟨7435815749604408830113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9914420999472545106817753 7435815749604408830113315)
                ·
                  refine ⟨11153723624406613245169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435815749604408830113315 11153723624406613245169973)
                  ·
                    refine ⟨1045661589788119991734685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11153723624406613245169973 1045661589788119991734685)
                    ·
                      rfl

theorem cell22_3054628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3054628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054628 prefixEnd_3054628 := by exact prefixLift 3054628
  have htrace : WordTrace (prefixWord ++ tailWord_3054628) baseStart_3054628 baseEnd_3054628 := by
    simpa [prefixWord, tailWord_3054628, baseEnd_3054628] using wordTrace_append hprefix tailTrace_3054628
  have hstable : (prefixWord ++ tailWord_3054628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054628).length < 2 ^ (prefixWord ++ tailWord_3054628).sum := by decide
  have hdescent : baseEnd_3054628 < baseStart_3054628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054662 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3054662 : Nat := 118140960795 + 3054662 * 2 ^ 59
def prefixEnd_3054662 : Nat := 4983230072969 + 3 ^ 40 * 3054662 * 2
def baseEnd_3054662 : Nat := 1045673228682955236384581

theorem tailTrace_3054662 : CollatzResearch.WordTrace tailWord_3054662 prefixEnd_3054662 1045673228682955236384581 := by
  unfold tailWord_3054662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481646126859023236889695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74275117372992495720313493 3481646126859023236889695)
  ·
    refine ⟨5222469190288534855334543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481646126859023236889695 5222469190288534855334543)
    ·
      refine ⟨7833703785432802283001815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222469190288534855334543 7833703785432802283001815)
      ·
        refine ⟨11750555678149203424502723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833703785432802283001815 11750555678149203424502723)
        ·
          refine ⟨17625833517223805136754085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11750555678149203424502723 17625833517223805136754085)
          ·
            refine ⟨3304843784479463463141391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17625833517223805136754085 3304843784479463463141391)
            ·
              refine ⟨4957265676719195194712087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304843784479463463141391 4957265676719195194712087)
              ·
                refine ⟨7435898515078792792068131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957265676719195194712087 7435898515078792792068131)
                ·
                  refine ⟨11153847772618189188102197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435898515078792792068131 11153847772618189188102197)
                  ·
                    refine ⟨1045673228682955236384581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11153847772618189188102197 1045673228682955236384581)
                    ·
                      rfl

theorem cell22_3054662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3054662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054662 prefixEnd_3054662 := by exact prefixLift 3054662
  have htrace : WordTrace (prefixWord ++ tailWord_3054662) baseStart_3054662 baseEnd_3054662 := by
    simpa [prefixWord, tailWord_3054662, baseEnd_3054662] using wordTrace_append hprefix tailTrace_3054662
  have hstable : (prefixWord ++ tailWord_3054662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054662).length < 2 ^ (prefixWord ++ tailWord_3054662).sum := by decide
  have hdescent : baseEnd_3054662 < baseStart_3054662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054673 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_3054673 : Nat := 118140960795 + 3054673 * 2 ^ 59
def prefixEnd_3054673 : Nat := 4983230072969 + 3 ^ 40 * 3054673 * 2
def baseEnd_3054673 : Nat := 1045676994207754874359547

theorem tailTrace_3054673 : CollatzResearch.WordTrace tailWord_3054673 prefixEnd_3054673 1045676994207754874359547 := by
  unfold tailWord_3054673
  simp only [CollatzResearch.WordTrace]
  refine ⟨111413077262448892459120673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74275384841632594972747115 111413077262448892459120673)
  ·
    refine ⟨83559807946836669344340505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111413077262448892459120673 83559807946836669344340505)
    ·
      refine ⟨62669855960127502008255379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83559807946836669344340505 62669855960127502008255379)
      ·
        refine ⟨94004783940191253012383069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62669855960127502008255379 94004783940191253012383069)
        ·
          refine ⟨35251793977571719879643651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94004783940191253012383069 35251793977571719879643651)
          ·
            refine ⟨52877690966357579819465477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35251793977571719879643651 52877690966357579819465477)
            ·
              refine ⟨9914567056192046216149777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52877690966357579819465477 9914567056192046216149777)
              ·
                refine ⟨7435925292144034662112333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9914567056192046216149777 7435925292144034662112333)
                ·
                  refine ⟨2788471984554012998292125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7435925292144034662112333 2788471984554012998292125)
                  ·
                    refine ⟨1045676994207754874359547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788471984554012998292125 1045676994207754874359547)
                    ·
                      rfl

theorem cell22_3054673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_3054673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054673 prefixEnd_3054673 := by exact prefixLift 3054673
  have htrace : WordTrace (prefixWord ++ tailWord_3054673) baseStart_3054673 baseEnd_3054673 := by
    simpa [prefixWord, tailWord_3054673, baseEnd_3054673] using wordTrace_append hprefix tailTrace_3054673
  have hstable : (prefixWord ++ tailWord_3054673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054673).length < 2 ^ (prefixWord ++ tailWord_3054673).sum := by decide
  have hdescent : baseEnd_3054673 < baseStart_3054673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054731 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 6]
def baseStart_3054731 : Nat := 118140960795 + 3054731 * 2 ^ 59
def prefixEnd_3054731 : Nat := 4983230072969 + 3 ^ 40 * 3054731 * 2
def baseEnd_3054731 : Nat := 348565616264354018803123

theorem tailTrace_3054731 : CollatzResearch.WordTrace tailWord_3054731 prefixEnd_3054731 348565616264354018803123 := by
  unfold tailWord_3054731
  simp only [CollatzResearch.WordTrace]
  refine ⟨111415192696238768364732047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74276795130825845576488031 111415192696238768364732047)
  ·
    refine ⟨167122789044358152547098071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111415192696238768364732047 167122789044358152547098071)
    ·
      refine ⟨250684183566537228820647107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167122789044358152547098071 250684183566537228820647107)
      ·
        refine ⟨376026275349805843230970661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250684183566537228820647107 376026275349805843230970661)
        ·
          refine ⟨70504926628088595605806999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376026275349805843230970661 70504926628088595605806999)
          ·
            refine ⟨105757389942132893408710499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70504926628088595605806999 105757389942132893408710499)
            ·
              refine ⟨158636084913199340113065749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105757389942132893408710499 158636084913199340113065749)
              ·
                refine ⟨7436066480306219067799957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158636084913199340113065749 7436066480306219067799957)
                ·
                  refine ⟨348565616264354018803123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7436066480306219067799957 348565616264354018803123)
                  ·
                    rfl

theorem cell22_3054731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_3054731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054731 prefixEnd_3054731 := by exact prefixLift 3054731
  have htrace : WordTrace (prefixWord ++ tailWord_3054731) baseStart_3054731 baseEnd_3054731 := by
    simpa [prefixWord, tailWord_3054731, baseEnd_3054731] using wordTrace_append hprefix tailTrace_3054731
  have hstable : (prefixWord ++ tailWord_3054731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054731).length < 2 ^ (prefixWord ++ tailWord_3054731).sum := by decide
  have hdescent : baseEnd_3054731 < baseStart_3054731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054776 : List Nat := [2, 1, 2, 1, 2, 1, 2, 11]
def baseStart_3054776 : Nat := 118140960795 + 3054776 * 2 ^ 59
def prefixEnd_3054776 : Nat := 4983230072969 + 3 ^ 40 * 3054776 * 2
def baseEnd_3054776 : Nat := 116190250356966326559359

theorem tailTrace_3054776 : CollatzResearch.WordTrace tailWord_3054776 prefixEnd_3054776 116190250356966326559359 := by
  unfold tailWord_3054776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55708416990537870525060091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74277889320717160700080121 55708416990537870525060091)
  ·
    refine ⟨83562625485806805787590137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55708416990537870525060091 83562625485806805787590137)
    ·
      refine ⟨62671969114355104340692603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83562625485806805787590137 62671969114355104340692603)
      ·
        refine ⟨94007953671532656511038905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62671969114355104340692603 94007953671532656511038905)
        ·
          refine ⟨70505965253649492383279179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94007953671532656511038905 70505965253649492383279179)
          ·
            refine ⟨105758947880474238574918769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70505965253649492383279179 105758947880474238574918769)
            ·
              refine ⟨79319210910355678931189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105758947880474238574918769 79319210910355678931189077)
              ·
                refine ⟨116190250356966326559359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79319210910355678931189077 116190250356966326559359)
                ·
                  rfl

theorem cell22_3054776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_3054776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054776 prefixEnd_3054776 := by exact prefixLift 3054776
  have htrace : WordTrace (prefixWord ++ tailWord_3054776) baseStart_3054776 baseEnd_3054776 := by
    simpa [prefixWord, tailWord_3054776, baseEnd_3054776] using wordTrace_append hprefix tailTrace_3054776
  have hstable : (prefixWord ++ tailWord_3054776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054776).length < 2 ^ (prefixWord ++ tailWord_3054776).sum := by decide
  have hdescent : baseEnd_3054776 < baseStart_3054776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054780 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_3054780 : Nat := 118140960795 + 3054780 * 2 ^ 59
def prefixEnd_3054780 : Nat := 4983230072969 + 3 ^ 40 * 3054780 * 2
def baseEnd_3054780 : Nat := 1045713622494442261934219

theorem tailTrace_3054780 : CollatzResearch.WordTrace tailWord_3054780 prefixEnd_3054780 1045713622494442261934219 := by
  unfold tailWord_3054780
  simp only [CollatzResearch.WordTrace]
  refine ⟨55708489936530624866632897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74277986582040833155510529 55708489936530624866632897)
  ·
    refine ⟨41781367452397968649974673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55708489936530624866632897 41781367452397968649974673)
    ·
      refine ⟨31336025589298476487481005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41781367452397968649974673 31336025589298476487481005)
      ·
        refine ⟨11751009595986928682805377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31336025589298476487481005 11751009595986928682805377)
        ·
          refine ⟨8813257196990196512104033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11751009595986928682805377 8813257196990196512104033)
          ·
            refine ⟨6609942897742647384078025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8813257196990196512104033 6609942897742647384078025)
            ·
              refine ⟨4957457173306985538058519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609942897742647384078025 4957457173306985538058519)
              ·
                refine ⟨7436185759960478307087779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957457173306985538058519 7436185759960478307087779)
                ·
                  refine ⟨11154278639940717460631669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436185759960478307087779 11154278639940717460631669)
                  ·
                    refine ⟨1045713622494442261934219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11154278639940717460631669 1045713622494442261934219)
                    ·
                      rfl

theorem cell22_3054780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_3054780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054780 prefixEnd_3054780 := by exact prefixLift 3054780
  have htrace : WordTrace (prefixWord ++ tailWord_3054780) baseStart_3054780 baseEnd_3054780 := by
    simpa [prefixWord, tailWord_3054780, baseEnd_3054780] using wordTrace_append hprefix tailTrace_3054780
  have hstable : (prefixWord ++ tailWord_3054780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054780).length < 2 ^ (prefixWord ++ tailWord_3054780).sum := by decide
  have hdescent : baseEnd_3054780 < baseStart_3054780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054859 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 1, 3]
def baseStart_3054859 : Nat := 118140960795 + 3054859 * 2 ^ 59
def prefixEnd_3054859 : Nat := 4983230072969 + 3 ^ 40 * 3054859 * 2
def baseEnd_3054859 : Nat := 1045740665808912389208977

theorem tailTrace_3054859 : CollatzResearch.WordTrace tailWord_3054859 prefixEnd_3054859 1045740665808912389208977 := by
  unfold tailWord_3054859
  simp only [CollatzResearch.WordTrace]
  refine ⟨111419861239775046225391631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74279907493183364150261087 111419861239775046225391631)
  ·
    refine ⟨167129791859662569338087447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111419861239775046225391631 167129791859662569338087447)
    ·
      refine ⟨250694687789493854007131171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167129791859662569338087447 250694687789493854007131171)
      ·
        refine ⟨376042031684240781010696757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250694687789493854007131171 376042031684240781010696757)
        ·
          refine ⟨35253940470397573219752821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 376042031684240781010696757 35253940470397573219752821)
          ·
            refine ⟨3305056919099772489351827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35253940470397573219752821 3305056919099772489351827)
            ·
              refine ⟨4957585378649658734027741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305056919099772489351827 4957585378649658734027741)
              ·
                refine ⟨1859094516993622025260403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4957585378649658734027741 1859094516993622025260403)
                ·
                  refine ⟨2788641775490433037890605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859094516993622025260403 2788641775490433037890605)
                  ·
                    refine ⟨1045740665808912389208977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788641775490433037890605 1045740665808912389208977)
                    ·
                      rfl

theorem cell22_3054859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 3].length) (baseStart_3054859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054859 prefixEnd_3054859 := by exact prefixLift 3054859
  have htrace : WordTrace (prefixWord ++ tailWord_3054859) baseStart_3054859 baseEnd_3054859 := by
    simpa [prefixWord, tailWord_3054859, baseEnd_3054859] using wordTrace_append hprefix tailTrace_3054859
  have hstable : (prefixWord ++ tailWord_3054859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054859).length < 2 ^ (prefixWord ++ tailWord_3054859).sum := by decide
  have hdescent : baseEnd_3054859 < baseStart_3054859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054900 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3054900 : Nat := 118140960795 + 3054900 * 2 ^ 59
def prefixEnd_3054900 : Nat := 4983230072969 + 3 ^ 40 * 3054900 * 2
def baseEnd_3054900 : Nat := 348584900315600649644617

theorem tailTrace_3054900 : CollatzResearch.WordTrace tailWord_3054900 prefixEnd_3054900 348584900315600649644617 := by
  unfold tailWord_3054900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55710678316313255113817077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74280904421751006818422769 55710678316313255113817077)
  ·
    refine ⟨5222876092154367666920351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55710678316313255113817077 5222876092154367666920351)
    ·
      refine ⟨7834314138231551500380527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222876092154367666920351 7834314138231551500380527)
      ·
        refine ⟨11751471207347327250570791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834314138231551500380527 11751471207347327250570791)
        ·
          refine ⟨17627206811020990875856187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11751471207347327250570791 17627206811020990875856187)
          ·
            refine ⟨26440810216531486313784281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17627206811020990875856187 26440810216531486313784281)
            ·
              refine ⟨19830607662398614735338211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26440810216531486313784281 19830607662398614735338211)
              ·
                refine ⟨29745911493597922103007317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19830607662398614735338211 29745911493597922103007317)
                ·
                  refine ⟨348584900315600649644617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29745911493597922103007317 348584900315600649644617)
                  ·
                    rfl

theorem cell22_3054900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3054900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054900 prefixEnd_3054900 := by exact prefixLift 3054900
  have htrace : WordTrace (prefixWord ++ tailWord_3054900) baseStart_3054900 baseEnd_3054900 := by
    simpa [prefixWord, tailWord_3054900, baseEnd_3054900] using wordTrace_append hprefix tailTrace_3054900
  have hstable : (prefixWord ++ tailWord_3054900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054900).length < 2 ^ (prefixWord ++ tailWord_3054900).sum := by decide
  have hdescent : baseEnd_3054900 < baseStart_3054900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054943 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3054943 : Nat := 118140960795 + 3054943 * 2 ^ 59
def prefixEnd_3054943 : Nat := 4983230072969 + 3 ^ 40 * 3054943 * 2
def baseEnd_3054943 : Nat := 1045769420725564170108719

theorem tailTrace_3054943 : CollatzResearch.WordTrace tailWord_3054943 prefixEnd_3054943 1045769420725564170108719 := by
  unfold tailWord_3054943
  simp only [CollatzResearch.WordTrace]
  refine ⟨111422924971470728571449483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74281949980980485714299655 111422924971470728571449483)
  ·
    refine ⟨167134387457206092857174225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111422924971470728571449483 167134387457206092857174225)
    ·
      refine ⟨125350790592904569642880669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167134387457206092857174225 125350790592904569642880669)
      ·
        refine ⟨47006546472339213616080251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125350790592904569642880669 47006546472339213616080251)
        ·
          refine ⟨70509819708508820424120377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47006546472339213616080251 70509819708508820424120377)
          ·
            refine ⟨52882364781381615318090283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70509819708508820424120377 52882364781381615318090283)
            ·
              refine ⟨79323547172072422977135425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52882364781381615318090283 79323547172072422977135425)
              ·
                refine ⟨59492660379054317232851569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79323547172072422977135425 59492660379054317232851569)
                ·
                  refine ⟨44619495284290737924638677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59492660379054317232851569 44619495284290737924638677)
                  ·
                    refine ⟨1045769420725564170108719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44619495284290737924638677 1045769420725564170108719)
                    ·
                      rfl

theorem cell22_3054943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3054943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3054943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3054943 prefixEnd_3054943 := by exact prefixLift 3054943
  have htrace : WordTrace (prefixWord ++ tailWord_3054943) baseStart_3054943 baseEnd_3054943 := by
    simpa [prefixWord, tailWord_3054943, baseEnd_3054943] using wordTrace_append hprefix tailTrace_3054943
  have hstable : (prefixWord ++ tailWord_3054943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054943).length < 2 ^ (prefixWord ++ tailWord_3054943).sum := by decide
  have hdescent : baseEnd_3054943 < baseStart_3054943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055020 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_3055020 : Nat := 118140960795 + 3055020 * 2 ^ 59
def prefixEnd_3055020 : Nat := 4983230072969 + 3 ^ 40 * 3055020 * 2
def baseEnd_3055020 : Nat := 1045795779399161635933483

theorem tailTrace_3055020 : CollatzResearch.WordTrace tailWord_3055020 prefixEnd_3055020 1045795779399161635933483 := by
  unfold tailWord_3055020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55712866696095885361001257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74283822261461180481335009 55712866696095885361001257)
  ·
    refine ⟨41784650022071914020750943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55712866696095885361001257 41784650022071914020750943)
    ·
      refine ⟨62676975033107871031126415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41784650022071914020750943 62676975033107871031126415)
      ·
        refine ⟨94015462549661806546689623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62676975033107871031126415 94015462549661806546689623)
        ·
          refine ⟨141023193824492709820034435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94015462549661806546689623 141023193824492709820034435)
          ·
            refine ⟨211534790736739064730051653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141023193824492709820034435 211534790736739064730051653)
            ·
              refine ⟨39662773263138574636884685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211534790736739064730051653 39662773263138574636884685)
              ·
                refine ⟨14873539973676965488831757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39662773263138574636884685 14873539973676965488831757)
                ·
                  refine ⟨5577577490128862058311909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14873539973676965488831757 5577577490128862058311909)
                  ·
                    refine ⟨1045795779399161635933483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5577577490128862058311909 1045795779399161635933483)
                    ·
                      rfl

theorem cell22_3055020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_3055020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055020 prefixEnd_3055020 := by exact prefixLift 3055020
  have htrace : WordTrace (prefixWord ++ tailWord_3055020) baseStart_3055020 baseEnd_3055020 := by
    simpa [prefixWord, tailWord_3055020, baseEnd_3055020] using wordTrace_append hprefix tailTrace_3055020
  have hstable : (prefixWord ++ tailWord_3055020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055020).length < 2 ^ (prefixWord ++ tailWord_3055020).sum := by decide
  have hdescent : baseEnd_3055020 < baseStart_3055020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055037 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_3055037 : Nat := 118140960795 + 3055037 * 2 ^ 59
def prefixEnd_3055037 : Nat := 4983230072969 + 3 ^ 40 * 3055037 * 2
def baseEnd_3055037 : Nat := 1045801598846579258258431

theorem tailTrace_3055037 : CollatzResearch.WordTrace tailWord_3055037 prefixEnd_3055037 1045801598846579258258431 := by
  unfold tailWord_3055037
  simp only [CollatzResearch.WordTrace]
  refine ⟨111426353433130182625371365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74284235622086788416914243 111426353433130182625371365)
  ·
    refine ⟨20892441268711909242257131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111426353433130182625371365 20892441268711909242257131)
    ·
      refine ⟨31338661903067863863385697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20892441268711909242257131 31338661903067863863385697)
      ·
        refine ⟨23503996427300897897539273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31338661903067863863385697 23503996427300897897539273)
        ·
          refine ⟨17627997320475673423154455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23503996427300897897539273 17627997320475673423154455)
          ·
            refine ⟨26441995980713510134731683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17627997320475673423154455 26441995980713510134731683)
            ·
              refine ⟨39662993971070265202097525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26441995980713510134731683 39662993971070265202097525)
              ·
                refine ⟨3718405684787837362696643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39662993971070265202097525 3718405684787837362696643)
                ·
                  refine ⟨5577608527181756044044965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718405684787837362696643 5577608527181756044044965)
                  ·
                    refine ⟨1045801598846579258258431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5577608527181756044044965 1045801598846579258258431)
                    ·
                      rfl

theorem cell22_3055037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_3055037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055037 prefixEnd_3055037 := by exact prefixLift 3055037
  have htrace : WordTrace (prefixWord ++ tailWord_3055037) baseStart_3055037 baseEnd_3055037 := by
    simpa [prefixWord, tailWord_3055037, baseEnd_3055037] using wordTrace_append hprefix tailTrace_3055037
  have hstable : (prefixWord ++ tailWord_3055037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055037).length < 2 ^ (prefixWord ++ tailWord_3055037).sum := by decide
  have hdescent : baseEnd_3055037 < baseStart_3055037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055052 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_3055052 : Nat := 118140960795 + 3055052 * 2 ^ 59
def prefixEnd_3055052 : Nat := 4983230072969 + 3 ^ 40 * 3055052 * 2
def baseEnd_3055052 : Nat := 348602244551041406377795

theorem tailTrace_3055052 : CollatzResearch.WordTrace tailWord_3055052 prefixEnd_3055052 348602244551041406377795 := by
  unfold tailWord_3055052
  simp only [CollatzResearch.WordTrace]
  refine ⟨55713450264037920093583705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74284600352050560124778273 55713450264037920093583705)
  ·
    refine ⟨41785087698028440070187779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55713450264037920093583705 41785087698028440070187779)
    ·
      refine ⟨62677631547042660105281669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41785087698028440070187779 62677631547042660105281669)
      ·
        refine ⟨11752055915070498769740313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62677631547042660105281669 11752055915070498769740313)
        ·
          refine ⟨8814041936302874077305235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11752055915070498769740313 8814041936302874077305235)
          ·
            refine ⟨13221062904454311115957853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8814041936302874077305235 13221062904454311115957853)
            ·
              refine ⟨4957898589170366668484195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13221062904454311115957853 4957898589170366668484195)
              ·
                refine ⟨7436847883755550002726293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957898589170366668484195 7436847883755550002726293)
                ·
                  refine ⟨348602244551041406377795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7436847883755550002726293 348602244551041406377795)
                  ·
                    rfl

theorem cell22_3055052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_3055052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055052 prefixEnd_3055052 := by exact prefixLift 3055052
  have htrace : WordTrace (prefixWord ++ tailWord_3055052) baseStart_3055052 baseEnd_3055052 := by
    simpa [prefixWord, tailWord_3055052, baseEnd_3055052] using wordTrace_append hprefix tailTrace_3055052
  have hstable : (prefixWord ++ tailWord_3055052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055052).length < 2 ^ (prefixWord ++ tailWord_3055052).sum := by decide
  have hdescent : baseEnd_3055052 < baseStart_3055052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055080 : List Nat := [2, 1, 4, 1, 1, 2, 1, 10]
def baseStart_3055080 : Nat := 118140960795 + 3055080 * 2 ^ 59
def prefixEnd_3055080 : Nat := 4983230072969 + 3 ^ 40 * 3055080 * 2
def baseEnd_3055080 : Nat := 116201813180593497714811

theorem tailTrace_3055080 : CollatzResearch.WordTrace tailWord_3055080 prefixEnd_3055080 116201813180593497714811 := by
  unfold tailWord_3055080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55713960885987200484593347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74285281181316267312791129 55713960885987200484593347)
  ·
    refine ⟨83570941328980800726890021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55713960885987200484593347 83570941328980800726890021)
    ·
      refine ⟨15669551499183900136291879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83570941328980800726890021 15669551499183900136291879)
      ·
        refine ⟨23504327248775850204437819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15669551499183900136291879 23504327248775850204437819)
        ·
          refine ⟨35256490873163775306656729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23504327248775850204437819 35256490873163775306656729)
          ·
            refine ⟨26442368154872831479992547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35256490873163775306656729 26442368154872831479992547)
            ·
              refine ⟨39663552232309247219988821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26442368154872831479992547 39663552232309247219988821)
              ·
                refine ⟨116201813180593497714811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39663552232309247219988821 116201813180593497714811)
                ·
                  rfl

theorem cell22_3055080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_3055080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055080 prefixEnd_3055080 := by exact prefixLift 3055080
  have htrace : WordTrace (prefixWord ++ tailWord_3055080) baseStart_3055080 baseEnd_3055080 := by
    simpa [prefixWord, tailWord_3055080, baseEnd_3055080] using wordTrace_append hprefix tailTrace_3055080
  have hstable : (prefixWord ++ tailWord_3055080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055080).length < 2 ^ (prefixWord ++ tailWord_3055080).sum := by decide
  have hdescent : baseEnd_3055080 < baseStart_3055080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055157 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3055157 : Nat := 118140960795 + 3055157 * 2 ^ 59
def prefixEnd_3055157 : Nat := 4983230072969 + 3 ^ 40 * 3055157 * 2
def baseEnd_3055157 : Nat := 1045842677298938945258063

theorem tailTrace_3055157 : CollatzResearch.WordTrace tailWord_3055157 prefixEnd_3055157 1045842677298938945258063 := by
  unfold tailWord_3055157
  simp only [CollatzResearch.WordTrace]
  refine ⟨111430730192695443119739725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74287153461796962079826483 111430730192695443119739725)
  ·
    refine ⟨41786523822260791169902397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111430730192695443119739725 41786523822260791169902397)
    ·
      refine ⟨15669946433347796688713399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41786523822260791169902397 15669946433347796688713399)
      ·
        refine ⟨23504919650021695033070099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15669946433347796688713399 23504919650021695033070099)
        ·
          refine ⟨35257379475032542549605149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23504919650021695033070099 35257379475032542549605149)
          ·
            refine ⟨13221517303137203456101931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35257379475032542549605149 13221517303137203456101931)
            ·
              refine ⟨19832275954705805184152897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13221517303137203456101931 19832275954705805184152897)
              ·
                refine ⟨14874206966029353888114673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19832275954705805184152897 14874206966029353888114673)
                ·
                  refine ⟨11155655224522015416086005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14874206966029353888114673 11155655224522015416086005)
                  ·
                    refine ⟨1045842677298938945258063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11155655224522015416086005 1045842677298938945258063)
                    ·
                      rfl

theorem cell22_3055157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3055157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055157 prefixEnd_3055157 := by exact prefixLift 3055157
  have htrace : WordTrace (prefixWord ++ tailWord_3055157) baseStart_3055157 baseEnd_3055157 := by
    simpa [prefixWord, tailWord_3055157, baseEnd_3055157] using wordTrace_append hprefix tailTrace_3055157
  have hstable : (prefixWord ++ tailWord_3055157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055157).length < 2 ^ (prefixWord ++ tailWord_3055157).sum := by decide
  have hdescent : baseEnd_3055157 < baseStart_3055157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055159 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 5]
def baseStart_3055159 : Nat := 118140960795 + 3055159 * 2 ^ 59
def prefixEnd_3055159 : Nat := 4983230072969 + 3 ^ 40 * 3055159 * 2
def baseEnd_3055159 : Nat := 348614453979937202236019

theorem tailTrace_3055159 : CollatzResearch.WordTrace tailWord_3055159 prefixEnd_3055159 348614453979937202236019 := by
  unfold tailWord_3055159
  simp only [CollatzResearch.WordTrace]
  refine ⟨111430803138688197461312531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74287202092458798307541687 111430803138688197461312531)
  ·
    refine ⟨167146204708032296191968797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111430803138688197461312531 167146204708032296191968797)
    ·
      refine ⟨62679826765512111071988299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167146204708032296191968797 62679826765512111071988299)
      ·
        refine ⟨94019740148268166607982449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62679826765512111071988299 94019740148268166607982449)
        ·
          refine ⟨70514805111201124955986837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94019740148268166607982449 70514805111201124955986837)
          ·
            refine ⟨3305381489587552732311883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70514805111201124955986837 3305381489587552732311883)
            ·
              refine ⟨4958072234381329098467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305381489587552732311883 4958072234381329098467825)
              ·
                refine ⟨3718554175785996823850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958072234381329098467825 3718554175785996823850869)
                ·
                  refine ⟨348614453979937202236019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3718554175785996823850869 348614453979937202236019)
                  ·
                    rfl

theorem cell22_3055159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].length) (baseStart_3055159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055159 prefixEnd_3055159 := by exact prefixLift 3055159
  have htrace : WordTrace (prefixWord ++ tailWord_3055159) baseStart_3055159 baseEnd_3055159 := by
    simpa [prefixWord, tailWord_3055159, baseEnd_3055159] using wordTrace_append hprefix tailTrace_3055159
  have hstable : (prefixWord ++ tailWord_3055159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055159).length < 2 ^ (prefixWord ++ tailWord_3055159).sum := by decide
  have hdescent : baseEnd_3055159 < baseStart_3055159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055197 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3055197 : Nat := 118140960795 + 3055197 * 2 ^ 59
def prefixEnd_3055197 : Nat := 4983230072969 + 3 ^ 40 * 3055197 * 2
def baseEnd_3055197 : Nat := 1045856370116392174257941

theorem tailTrace_3055197 : CollatzResearch.WordTrace tailWord_3055197 prefixEnd_3055197 1045856370116392174257941 := by
  unfold tailWord_3055197
  simp only [CollatzResearch.WordTrace]
  refine ⟨111432189112550529951195845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74288126075033686634130563 111432189112550529951195845)
  ·
    refine ⟨20893535458603224365849221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111432189112550529951195845 20893535458603224365849221)
    ·
      refine ⟨3917537898488104568596729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20893535458603224365849221 3917537898488104568596729)
      ·
        refine ⟨2938153423866078426447547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917537898488104568596729 2938153423866078426447547)
        ·
          refine ⟨4407230135799117639671321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938153423866078426447547 4407230135799117639671321)
          ·
            refine ⟨3305422601849338229753491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407230135799117639671321 3305422601849338229753491)
            ·
              refine ⟨4958133902774007344630237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305422601849338229753491 4958133902774007344630237)
              ·
                refine ⟨1859300213540252754236339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4958133902774007344630237 1859300213540252754236339)
                ·
                  refine ⟨2788950320310379131354509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859300213540252754236339 2788950320310379131354509)
                  ·
                    refine ⟨1045856370116392174257941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788950320310379131354509 1045856370116392174257941)
                    ·
                      rfl

theorem cell22_3055197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3055197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055197 prefixEnd_3055197 := by exact prefixLift 3055197
  have htrace : WordTrace (prefixWord ++ tailWord_3055197) baseStart_3055197 baseEnd_3055197 := by
    simpa [prefixWord, tailWord_3055197, baseEnd_3055197] using wordTrace_append hprefix tailTrace_3055197
  have hstable : (prefixWord ++ tailWord_3055197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055197).length < 2 ^ (prefixWord ++ tailWord_3055197).sum := by decide
  have hdescent : baseEnd_3055197 < baseStart_3055197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055221 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 6]
def baseStart_3055221 : Nat := 118140960795 + 3055221 * 2 ^ 59
def prefixEnd_3055221 : Nat := 4983230072969 + 3 ^ 40 * 3055221 * 2
def baseEnd_3055221 : Nat := 348621528602288037219289

theorem tailTrace_3055221 : CollatzResearch.WordTrace tailWord_3055221 prefixEnd_3055221 348621528602288037219289 := by
  unfold tailWord_3055221
  simp only [CollatzResearch.WordTrace]
  refine ⟨111433064464463582050069517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74288709642975721366713011 111433064464463582050069517)
  ·
    refine ⟨41787399174173843268776069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111433064464463582050069517 41787399174173843268776069)
    ·
      refine ⟨7835137345157595612895513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41787399174173843268776069 7835137345157595612895513)
      ·
        refine ⟨5876353008868196709671635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7835137345157595612895513 5876353008868196709671635)
        ·
          refine ⟨8814529513302295064507453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5876353008868196709671635 8814529513302295064507453)
          ·
            refine ⟨3305448567488360649190295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8814529513302295064507453 3305448567488360649190295)
            ·
              refine ⟨4958172851232540973785443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305448567488360649190295 4958172851232540973785443)
              ·
                refine ⟨7437259276848811460678165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958172851232540973785443 7437259276848811460678165)
                ·
                  refine ⟨348621528602288037219289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7437259276848811460678165 348621528602288037219289)
                  ·
                    rfl

theorem cell22_3055221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_3055221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055221 prefixEnd_3055221 := by exact prefixLift 3055221
  have htrace : WordTrace (prefixWord ++ tailWord_3055221) baseStart_3055221 baseEnd_3055221 := by
    simpa [prefixWord, tailWord_3055221, baseEnd_3055221] using wordTrace_append hprefix tailTrace_3055221
  have hstable : (prefixWord ++ tailWord_3055221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055221).length < 2 ^ (prefixWord ++ tailWord_3055221).sum := by decide
  have hdescent : baseEnd_3055221 < baseStart_3055221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055232 : List Nat := [2, 1, 1, 2, 1, 4, 4, 7]
def baseStart_3055232 : Nat := 118140960795 + 3055232 * 2 ^ 59
def prefixEnd_3055232 : Nat := 4983230072969 + 3 ^ 40 * 3055232 * 2
def baseEnd_3055232 : Nat := 116207594592407083292537

theorem tailTrace_3055232 : CollatzResearch.WordTrace tailWord_3055232 prefixEnd_3055232 116207594592407083292537 := by
  unfold tailWord_3055232
  simp only [CollatzResearch.WordTrace]
  refine ⟨55716732833711865464359975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74288977111615820619146633 55716732833711865464359975)
  ·
    refine ⟨83575099250567798196539963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55716732833711865464359975 83575099250567798196539963)
    ·
      refine ⟨125362648875851697294809945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83575099250567798196539963 125362648875851697294809945)
      ·
        refine ⟨94021986656888772971107459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125362648875851697294809945 94021986656888772971107459)
        ·
          refine ⟨141032979985333159456661189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94021986656888772971107459 141032979985333159456661189)
          ·
            refine ⟨26443683747249967398123973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141032979985333159456661189 26443683747249967398123973)
            ·
              refine ⟨4958190702609368887148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26443683747249967398123973 4958190702609368887148245)
              ·
                refine ⟨116207594592407083292537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4958190702609368887148245 116207594592407083292537)
                ·
                  rfl

theorem cell22_3055232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_3055232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055232 prefixEnd_3055232 := by exact prefixLift 3055232
  have htrace : WordTrace (prefixWord ++ tailWord_3055232) baseStart_3055232 baseEnd_3055232 := by
    simpa [prefixWord, tailWord_3055232, baseEnd_3055232] using wordTrace_append hprefix tailTrace_3055232
  have hstable : (prefixWord ++ tailWord_3055232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055232).length < 2 ^ (prefixWord ++ tailWord_3055232).sum := by decide
  have hdescent : baseEnd_3055232 < baseStart_3055232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055240 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3055240 : Nat := 118140960795 + 3055240 * 2 ^ 59
def prefixEnd_3055240 : Nat := 4983230072969 + 3 ^ 40 * 3055240 * 2
def baseEnd_3055240 : Nat := 1045871089895154395432809

theorem tailTrace_3055240 : CollatzResearch.WordTrace tailWord_3055240 prefixEnd_3055240 1045871089895154395432809 := by
  unfold tailWord_3055240
  simp only [CollatzResearch.WordTrace]
  refine ⟨55716878725697374147505587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74289171634263165530007449 55716878725697374147505587)
  ·
    refine ⟨83575318088546061221258381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55716878725697374147505587 83575318088546061221258381)
    ·
      refine ⟨31340744283204772957971893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83575318088546061221258381 31340744283204772957971893)
      ·
        refine ⟨2938194776550447464809865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31340744283204772957971893 2938194776550447464809865)
        ·
          refine ⟨2203646082412835598607399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938194776550447464809865 2203646082412835598607399)
          ·
            refine ⟨3305469123619253397911099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203646082412835598607399 3305469123619253397911099)
            ·
              refine ⟨4958203685428880096866649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305469123619253397911099 4958203685428880096866649)
              ·
                refine ⟨3718652764071660072649987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958203685428880096866649 3718652764071660072649987)
                ·
                  refine ⟨5577979146107490108974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718652764071660072649987 5577979146107490108974981)
                  ·
                    refine ⟨1045871089895154395432809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5577979146107490108974981 1045871089895154395432809)
                    ·
                      rfl

theorem cell22_3055240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3055240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055240 prefixEnd_3055240 := by exact prefixLift 3055240
  have htrace : WordTrace (prefixWord ++ tailWord_3055240) baseStart_3055240 baseEnd_3055240 := by
    simpa [prefixWord, tailWord_3055240, baseEnd_3055240] using wordTrace_append hprefix tailTrace_3055240
  have hstable : (prefixWord ++ tailWord_3055240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055240).length < 2 ^ (prefixWord ++ tailWord_3055240).sum := by decide
  have hdescent : baseEnd_3055240 < baseStart_3055240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055266 : List Nat := [3, 3, 1, 4, 2, 9]
def baseStart_3055266 : Nat := 118140960795 + 3055266 * 2 ^ 59
def prefixEnd_3055266 : Nat := 4983230072969 + 3 ^ 40 * 3055266 * 2
def baseEnd_3055266 : Nat := 12912098644771592522009

theorem tailTrace_3055266 : CollatzResearch.WordTrace tailWord_3055266 prefixEnd_3055266 12912098644771592522009 := by
  unfold tailWord_3055266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858676437325138683864413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74289803832867036490305101 27858676437325138683864413)
  ·
    refine ⟨10447003663996927006449155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27858676437325138683864413 10447003663996927006449155)
    ·
      refine ⟨15670505495995390509673733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10447003663996927006449155 15670505495995390509673733)
      ·
        refine ⟨2938219780499135720563825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15670505495995390509673733 2938219780499135720563825)
        ·
          refine ⟨2203664835374351790422869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938219780499135720563825 2203664835374351790422869)
          ·
            refine ⟨12912098644771592522009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2203664835374351790422869 12912098644771592522009)
            ·
              rfl

theorem cell22_3055266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 9].length) (baseStart_3055266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055266 prefixEnd_3055266 := by exact prefixLift 3055266
  have htrace : WordTrace (prefixWord ++ tailWord_3055266) baseStart_3055266 baseEnd_3055266 := by
    simpa [prefixWord, tailWord_3055266, baseEnd_3055266] using wordTrace_append hprefix tailTrace_3055266
  have hstable : (prefixWord ++ tailWord_3055266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055266).length < 2 ^ (prefixWord ++ tailWord_3055266).sum := by decide
  have hdescent : baseEnd_3055266 < baseStart_3055266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055369 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_3055369 : Nat := 118140960795 + 3055369 * 2 ^ 59
def prefixEnd_3055369 : Nat := 4983230072969 + 3 ^ 40 * 3055369 * 2
def baseEnd_3055369 : Nat := 1045915249231441058957413

theorem tailTrace_3055369 : CollatzResearch.WordTrace tailWord_3055369 prefixEnd_3055369 1045915249231441058957413 := by
  unfold tailWord_3055369
  simp only [CollatzResearch.WordTrace]
  refine ⟨111438462467927403326457161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74292308311951602217638107 111438462467927403326457161)
  ·
    refine ⟨83578846850945552494842871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111438462467927403326457161 83578846850945552494842871)
    ·
      refine ⟨125368270276418328742264307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83578846850945552494842871 125368270276418328742264307)
      ·
        refine ⟨188052405414627493113396461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125368270276418328742264307 188052405414627493113396461)
        ·
          refine ⟨70519652030485309917523673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188052405414627493113396461 70519652030485309917523673)
          ·
            refine ⟨52889739022863982438142755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70519652030485309917523673 52889739022863982438142755)
            ·
              refine ⟨79334608534295973657214133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52889739022863982438142755 79334608534295973657214133)
              ·
                refine ⟨7437619550090247530363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79334608534295973657214133 7437619550090247530363825)
                ·
                  refine ⟨5578214662567685647772869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7437619550090247530363825 5578214662567685647772869)
                  ·
                    refine ⟨1045915249231441058957413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578214662567685647772869 1045915249231441058957413)
                    ·
                      rfl

theorem cell22_3055369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_3055369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055369 prefixEnd_3055369 := by exact prefixLift 3055369
  have htrace : WordTrace (prefixWord ++ tailWord_3055369) baseStart_3055369 baseEnd_3055369 := by
    simpa [prefixWord, tailWord_3055369, baseEnd_3055369] using wordTrace_append hprefix tailTrace_3055369
  have hstable : (prefixWord ++ tailWord_3055369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055369).length < 2 ^ (prefixWord ++ tailWord_3055369).sum := by decide
  have hdescent : baseEnd_3055369 < baseStart_3055369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055386 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_3055386 : Nat := 118140960795 + 3055386 * 2 ^ 59
def prefixEnd_3055386 : Nat := 4983230072969 + 3 ^ 40 * 3055386 * 2
def baseEnd_3055386 : Nat := 1045921068678858681282361

theorem tailTrace_3055386 : CollatzResearch.WordTrace tailWord_3055386 prefixEnd_3055386 1045921068678858681282361 := by
  unfold tailWord_3055386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27859770627216453807456503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74292721672577210153217341 27859770627216453807456503)
  ·
    refine ⟨41789655940824680711184755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27859770627216453807456503 41789655940824680711184755)
    ·
      refine ⟨62684483911237021066777133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41789655940824680711184755 62684483911237021066777133)
      ·
        refine ⟨23506681466713882900041425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62684483911237021066777133 23506681466713882900041425)
        ·
          refine ⟨17630011100035412175031069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23506681466713882900041425 17630011100035412175031069)
          ·
            refine ⟨6611254162513279565636651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17630011100035412175031069 6611254162513279565636651)
            ·
              refine ⟨9916881243769919348454977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611254162513279565636651 9916881243769919348454977)
              ·
                refine ⟨7437660932827439511341233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916881243769919348454977 7437660932827439511341233)
                ·
                  refine ⟨5578245699620579633505925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7437660932827439511341233 5578245699620579633505925)
                  ·
                    refine ⟨1045921068678858681282361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578245699620579633505925 1045921068678858681282361)
                    ·
                      rfl

theorem cell22_3055386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_3055386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055386 prefixEnd_3055386 := by exact prefixLift 3055386
  have htrace : WordTrace (prefixWord ++ tailWord_3055386) baseStart_3055386 baseEnd_3055386 := by
    simpa [prefixWord, tailWord_3055386, baseEnd_3055386] using wordTrace_append hprefix tailTrace_3055386
  have hstable : (prefixWord ++ tailWord_3055386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055386).length < 2 ^ (prefixWord ++ tailWord_3055386).sum := by decide
  have hdescent : baseEnd_3055386 < baseStart_3055386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055433 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_3055433 : Nat := 118140960795 + 3055433 * 2 ^ 59
def prefixEnd_3055433 : Nat := 4983230072969 + 3 ^ 40 * 3055433 * 2
def baseEnd_3055433 : Nat := 1045937157739366225357217

theorem tailTrace_3055433 : CollatzResearch.WordTrace tailWord_3055433 prefixEnd_3055433 1045937157739366225357217 := by
  unfold tailWord_3055433
  simp only [CollatzResearch.WordTrace]
  refine ⟨111440796739695542256786953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74293864493130361504524635 111440796739695542256786953)
  ·
    refine ⟨83580597554771656692590215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111440796739695542256786953 83580597554771656692590215)
    ·
      refine ⟨125370896332157485038885323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83580597554771656692590215 125370896332157485038885323)
      ·
        refine ⟨188056344498236227558327985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125370896332157485038885323 188056344498236227558327985)
        ·
          refine ⟨141042258373677170668745989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188056344498236227558327985 141042258373677170668745989)
          ·
            refine ⟨26445423445064469500389873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141042258373677170668745989 26445423445064469500389873)
            ·
              refine ⟨19834067583798352125292405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26445423445064469500389873 19834067583798352125292405)
              ·
                refine ⟨1859443835981095511746163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19834067583798352125292405 1859443835981095511746163)
                ·
                  refine ⟨2789165753971643267619245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859443835981095511746163 2789165753971643267619245)
                  ·
                    refine ⟨1045937157739366225357217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789165753971643267619245 1045937157739366225357217)
                    ·
                      rfl

theorem cell22_3055433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_3055433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055433 prefixEnd_3055433 := by exact prefixLift 3055433
  have htrace : WordTrace (prefixWord ++ tailWord_3055433) baseStart_3055433 baseEnd_3055433 := by
    simpa [prefixWord, tailWord_3055433, baseEnd_3055433] using wordTrace_append hprefix tailTrace_3055433
  have hstable : (prefixWord ++ tailWord_3055433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055433).length < 2 ^ (prefixWord ++ tailWord_3055433).sum := by decide
  have hdescent : baseEnd_3055433 < baseStart_3055433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055504 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_3055504 : Nat := 118140960795 + 3055504 * 2 ^ 59
def prefixEnd_3055504 : Nat := 4983230072969 + 3 ^ 40 * 3055504 * 2
def baseEnd_3055504 : Nat := 1045961462490345706831999

theorem tailTrace_3055504 : CollatzResearch.WordTrace tailWord_3055504 prefixEnd_3055504 1045961462490345706831999 := by
  unfold tailWord_3055504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55721693161219160691310783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74295590881625547588414377 55721693161219160691310783)
  ·
    refine ⟨83582539741828741036966175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55721693161219160691310783 83582539741828741036966175)
    ·
      refine ⟨125373809612743111555449263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83582539741828741036966175 125373809612743111555449263)
      ·
        refine ⟨188060714419114667333173895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125373809612743111555449263 188060714419114667333173895)
        ·
          refine ⟨282091071628672000999760843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188060714419114667333173895 282091071628672000999760843)
          ·
            refine ⟨423136607443008001499641265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282091071628672000999760843 423136607443008001499641265)
            ·
              refine ⟨317352455582256001124730949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423136607443008001499641265 317352455582256001124730949)
              ·
                refine ⟨59503585421673000210887053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317352455582256001124730949 59503585421673000210887053)
                ·
                  refine ⟨22313844533127375079082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59503585421673000210887053 22313844533127375079082645)
                  ·
                    refine ⟨1045961462490345706831999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22313844533127375079082645 1045961462490345706831999)
                    ·
                      rfl

theorem cell22_3055504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_3055504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055504 prefixEnd_3055504 := by exact prefixLift 3055504
  have htrace : WordTrace (prefixWord ++ tailWord_3055504) baseStart_3055504 baseEnd_3055504 := by
    simpa [prefixWord, tailWord_3055504, baseEnd_3055504] using wordTrace_append hprefix tailTrace_3055504
  have hstable : (prefixWord ++ tailWord_3055504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055504).length < 2 ^ (prefixWord ++ tailWord_3055504).sum := by decide
  have hdescent : baseEnd_3055504 < baseStart_3055504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055508 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_3055508 : Nat := 118140960795 + 3055508 * 2 ^ 59
def prefixEnd_3055508 : Nat := 4983230072969 + 3 ^ 40 * 3055508 * 2
def baseEnd_3055508 : Nat := 348654277257363676577329

theorem tailTrace_3055508 : CollatzResearch.WordTrace tailWord_3055508 prefixEnd_3055508 348654277257363676577329 := by
  unfold tailWord_3055508
  simp only [CollatzResearch.WordTrace]
  refine ⟨55721766107211915032883589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74295688142949220043844785 55721766107211915032883589)
  ·
    refine ⟨10447831145102234068665673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55721766107211915032883589 10447831145102234068665673)
    ·
      refine ⟨7835873358826675551499255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10447831145102234068665673 7835873358826675551499255)
      ·
        refine ⟨11753810038240013327248883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835873358826675551499255 11753810038240013327248883)
        ·
          refine ⟨17630715057360019990873325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11753810038240013327248883 17630715057360019990873325)
          ·
            refine ⟨6611518146510007496577497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17630715057360019990873325 6611518146510007496577497)
            ·
              refine ⟨4958638609882505622433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611518146510007496577497 4958638609882505622433123)
              ·
                refine ⟨7437957914823758433649685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958638609882505622433123 7437957914823758433649685)
                ·
                  refine ⟨348654277257363676577329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7437957914823758433649685 348654277257363676577329)
                  ·
                    rfl

theorem cell22_3055508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_3055508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055508 prefixEnd_3055508 := by exact prefixLift 3055508
  have htrace : WordTrace (prefixWord ++ tailWord_3055508) baseStart_3055508 baseEnd_3055508 := by
    simpa [prefixWord, tailWord_3055508, baseEnd_3055508] using wordTrace_append hprefix tailTrace_3055508
  have hstable : (prefixWord ++ tailWord_3055508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055508).length < 2 ^ (prefixWord ++ tailWord_3055508).sum := by decide
  have hdescent : baseEnd_3055508 < baseStart_3055508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055566 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3055566 : Nat := 118140960795 + 3055566 * 2 ^ 59
def prefixEnd_3055566 : Nat := 4983230072969 + 3 ^ 40 * 3055566 * 2
def baseEnd_3055566 : Nat := 1045982686357398211781809

theorem tailTrace_3055566 : CollatzResearch.WordTrace tailWord_3055566 prefixEnd_3055566 1045982686357398211781809 := by
  unfold tailWord_3055566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930705956026713246422319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74297098432142470647585701 13930705956026713246422319)
  ·
    refine ⟨20896058934040069869633479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13930705956026713246422319 20896058934040069869633479)
    ·
      refine ⟨31344088401060104804450219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20896058934040069869633479 31344088401060104804450219)
      ·
        refine ⟨47016132601590157206675329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31344088401060104804450219 47016132601590157206675329)
        ·
          refine ⟨35262099451192617905006497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47016132601590157206675329 35262099451192617905006497)
          ·
            refine ⟨26446574588394463428754873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35262099451192617905006497 26446574588394463428754873)
            ·
              refine ⟨19834930941295847571566155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26446574588394463428754873 19834930941295847571566155)
              ·
                refine ⟨29752396411943771357349233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19834930941295847571566155 29752396411943771357349233)
                ·
                  refine ⟨22314297308957828518011925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29752396411943771357349233 22314297308957828518011925)
                  ·
                    refine ⟨1045982686357398211781809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22314297308957828518011925 1045982686357398211781809)
                    ·
                      rfl

theorem cell22_3055566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3055566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055566 prefixEnd_3055566 := by exact prefixLift 3055566
  have htrace : WordTrace (prefixWord ++ tailWord_3055566) baseStart_3055566 baseEnd_3055566 := by
    simpa [prefixWord, tailWord_3055566, baseEnd_3055566] using wordTrace_append hprefix tailTrace_3055566
  have hstable : (prefixWord ++ tailWord_3055566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055566).length < 2 ^ (prefixWord ++ tailWord_3055566).sum := by decide
  have hdescent : baseEnd_3055566 < baseStart_3055566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055568 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_3055568 : Nat := 118140960795 + 3055568 * 2 ^ 59
def prefixEnd_3055568 : Nat := 4983230072969 + 3 ^ 40 * 3055568 * 2
def baseEnd_3055568 : Nat := 1045983370998270873231803

theorem tailTrace_3055568 : CollatzResearch.WordTrace tailWord_3055568 prefixEnd_3055568 1045983370998270873231803 := by
  unfold tailWord_3055568
  simp only [CollatzResearch.WordTrace]
  refine ⟨55722860297103230156475679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74297147062804306875300905 55722860297103230156475679)
  ·
    refine ⟨83584290445654845234713519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55722860297103230156475679 83584290445654845234713519)
    ·
      refine ⟨125376435668482267852070279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83584290445654845234713519 125376435668482267852070279)
      ·
        refine ⟨188064653502723401778105419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125376435668482267852070279 188064653502723401778105419)
        ·
          refine ⟨282096980254085102667158129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188064653502723401778105419 282096980254085102667158129)
          ·
            refine ⟨211572735190563827000368597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282096980254085102667158129 211572735190563827000368597)
            ·
              refine ⟨4958735981028839695321139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 211572735190563827000368597 4958735981028839695321139)
              ·
                refine ⟨7438103971543259542981709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958735981028839695321139 7438103971543259542981709)
                ·
                  refine ⟨2789288989328722328618141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7438103971543259542981709 2789288989328722328618141)
                  ·
                    refine ⟨1045983370998270873231803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789288989328722328618141 1045983370998270873231803)
                    ·
                      rfl

theorem cell22_3055568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_3055568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055568 prefixEnd_3055568 := by exact prefixLift 3055568
  have htrace : WordTrace (prefixWord ++ tailWord_3055568) baseStart_3055568 baseEnd_3055568 := by
    simpa [prefixWord, tailWord_3055568, baseEnd_3055568] using wordTrace_append hprefix tailTrace_3055568
  have hstable : (prefixWord ++ tailWord_3055568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055568).length < 2 ^ (prefixWord ++ tailWord_3055568).sum := by decide
  have hdescent : baseEnd_3055568 < baseStart_3055568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055662 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3055662 : Nat := 118140960795 + 3055662 * 2 ^ 59
def prefixEnd_3055662 : Nat := 4983230072969 + 3 ^ 40 * 3055662 * 2
def baseEnd_3055662 : Nat := 1046015549119285961381515

theorem tailTrace_3055662 : CollatzResearch.WordTrace tailWord_3055662 prefixEnd_3055662 1046015549119285961381515 := by
  unfold tailWord_3055662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931143631983239295859155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74299432703910609577915493 13931143631983239295859155)
  ·
    refine ⟨20896715447974858943788733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13931143631983239295859155 20896715447974858943788733)
    ·
      refine ⟨7836268292990572103920775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20896715447974858943788733 7836268292990572103920775)
      ·
        refine ⟨11754402439485858155881163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836268292990572103920775 11754402439485858155881163)
        ·
          refine ⟨17631603659228787233821745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754402439485858155881163 17631603659228787233821745)
          ·
            refine ⟨13223702744421590425366309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17631603659228787233821745 13223702744421590425366309)
            ·
              refine ⟨2479444264579048204756183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13223702744421590425366309 2479444264579048204756183)
              ·
                refine ⟨3719166396868572307134275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479444264579048204756183 3719166396868572307134275)
                ·
                  refine ⟨5578749595302858460701413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719166396868572307134275 5578749595302858460701413)
                  ·
                    refine ⟨1046015549119285961381515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578749595302858460701413 1046015549119285961381515)
                    ·
                      rfl

theorem cell22_3055662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3055662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055662 prefixEnd_3055662 := by exact prefixLift 3055662
  have htrace : WordTrace (prefixWord ++ tailWord_3055662) baseStart_3055662 baseEnd_3055662 := by
    simpa [prefixWord, tailWord_3055662, baseEnd_3055662] using wordTrace_append hprefix tailTrace_3055662
  have hstable : (prefixWord ++ tailWord_3055662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055662).length < 2 ^ (prefixWord ++ tailWord_3055662).sum := by decide
  have hdescent : baseEnd_3055662 < baseStart_3055662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055737 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_3055737 : Nat := 118140960795 + 3055737 * 2 ^ 59
def prefixEnd_3055737 : Nat := 4983230072969 + 3 ^ 40 * 3055737 * 2
def baseEnd_3055737 : Nat := 1046041223152010765756285

theorem tailTrace_3055737 : CollatzResearch.WordTrace tailWord_3055737 prefixEnd_3055737 1046041223152010765756285 := by
  unfold tailWord_3055737
  simp only [CollatzResearch.WordTrace]
  refine ⟨111451884530594202175853465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74301256353729468117235643 111451884530594202175853465)
  ·
    refine ⟨83588913397945651631890099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111451884530594202175853465 83588913397945651631890099)
    ·
      refine ⟨125383370096918477447835149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83588913397945651631890099 125383370096918477447835149)
      ·
        refine ⟨47018763786344429042938181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125383370096918477447835149 47018763786344429042938181)
        ·
          refine ⟨8816018209939580445550909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47018763786344429042938181 8816018209939580445550909)
          ·
            refine ⟨3306006828727342667081591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8816018209939580445550909 3306006828727342667081591)
            ·
              refine ⟨4959010243091014000622387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306006828727342667081591 4959010243091014000622387)
              ·
                refine ⟨7438515364636521000933581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959010243091014000622387 7438515364636521000933581)
                ·
                  refine ⟨2789443261738695375350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7438515364636521000933581 2789443261738695375350093)
                  ·
                    refine ⟨1046041223152010765756285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789443261738695375350093 1046041223152010765756285)
                    ·
                      rfl

theorem cell22_3055737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_3055737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055737 prefixEnd_3055737 := by exact prefixLift 3055737
  have htrace : WordTrace (prefixWord ++ tailWord_3055737) baseStart_3055737 baseEnd_3055737 := by
    simpa [prefixWord, tailWord_3055737, baseEnd_3055737] using wordTrace_append hprefix tailTrace_3055737
  have hstable : (prefixWord ++ tailWord_3055737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055737).length < 2 ^ (prefixWord ++ tailWord_3055737).sum := by decide
  have hdescent : baseEnd_3055737 < baseStart_3055737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055748 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3055748 : Nat := 118140960795 + 3055748 * 2 ^ 59
def prefixEnd_3055748 : Nat := 4983230072969 + 3 ^ 40 * 3055748 * 2
def baseEnd_3055748 : Nat := 1046044988676810403731251

theorem tailTrace_3055748 : CollatzResearch.WordTrace tailWord_3055748 prefixEnd_3055748 1046044988676810403731251 := by
  unfold tailWord_3055748
  simp only [CollatzResearch.WordTrace]
  refine ⟨55726142866777175527251949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74301523822369567369669265 55726142866777175527251949)
  ·
    refine ⟨20897303575041440822719481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55726142866777175527251949 20897303575041440822719481)
    ·
      refine ⟨15672977681281080617039611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20897303575041440822719481 15672977681281080617039611)
      ·
        refine ⟨23509466521921620925559417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15672977681281080617039611 23509466521921620925559417)
        ·
          refine ⟨17632099891441215694169563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23509466521921620925559417 17632099891441215694169563)
          ·
            refine ⟨26448149837161823541254345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17632099891441215694169563 26448149837161823541254345)
            ·
              refine ⟨19836112377871367655940759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26448149837161823541254345 19836112377871367655940759)
              ·
                refine ⟨29754168566807051483911139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19836112377871367655940759 29754168566807051483911139)
                ·
                  refine ⟨44631252850210577225866709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29754168566807051483911139 44631252850210577225866709)
                  ·
                    refine ⟨1046044988676810403731251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44631252850210577225866709 1046044988676810403731251)
                    ·
                      rfl

theorem cell22_3055748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3055748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055748 prefixEnd_3055748 := by exact prefixLift 3055748
  have htrace : WordTrace (prefixWord ++ tailWord_3055748) baseStart_3055748 baseEnd_3055748 := by
    simpa [prefixWord, tailWord_3055748, baseEnd_3055748] using wordTrace_append hprefix tailTrace_3055748
  have hstable : (prefixWord ++ tailWord_3055748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055748).length < 2 ^ (prefixWord ++ tailWord_3055748).sum := by decide
  have hdescent : baseEnd_3055748 < baseStart_3055748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055825 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_3055825 : Nat := 118140960795 + 3055825 * 2 ^ 59
def prefixEnd_3055825 : Nat := 4983230072969 + 3 ^ 40 * 3055825 * 2
def baseEnd_3055825 : Nat := 1046071347350407869556015

theorem tailTrace_3055825 : CollatzResearch.WordTrace tailWord_3055825 prefixEnd_3055825 1046071347350407869556015 := by
  unfold tailWord_3055825
  simp only [CollatzResearch.WordTrace]
  refine ⟨111455094154275393205056929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74303396102850262136704619 111455094154275393205056929)
  ·
    refine ⟨83591320615706544903792697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111455094154275393205056929 83591320615706544903792697)
    ·
      refine ⟨62693490461779908677844523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83591320615706544903792697 62693490461779908677844523)
      ·
        refine ⟨94040235692669863016766785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62693490461779908677844523 94040235692669863016766785)
        ·
          refine ⟨70530176769502397262575089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94040235692669863016766785 70530176769502397262575089)
          ·
            refine ⟨52897632577126797946931317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70530176769502397262575089 52897632577126797946931317)
            ·
              refine ⟨4959153054105637307524811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52897632577126797946931317 4959153054105637307524811)
              ·
                refine ⟨7438729581158455961287217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959153054105637307524811 7438729581158455961287217)
                ·
                  refine ⟨5579047185868841970965413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7438729581158455961287217 5579047185868841970965413)
                  ·
                    refine ⟨1046071347350407869556015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579047185868841970965413 1046071347350407869556015)
                    ·
                      rfl

theorem cell22_3055825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_3055825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055825 prefixEnd_3055825 := by exact prefixLift 3055825
  have htrace : WordTrace (prefixWord ++ tailWord_3055825) baseStart_3055825 baseEnd_3055825 := by
    simpa [prefixWord, tailWord_3055825, baseEnd_3055825] using wordTrace_append hprefix tailTrace_3055825
  have hstable : (prefixWord ++ tailWord_3055825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055825).length < 2 ^ (prefixWord ++ tailWord_3055825).sum := by decide
  have hdescent : baseEnd_3055825 < baseStart_3055825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055829 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 4]
def baseStart_3055829 : Nat := 118140960795 + 3055829 * 2 ^ 59
def prefixEnd_3055829 : Nat := 4983230072969 + 3 ^ 40 * 3055829 * 2
def baseEnd_3055829 : Nat := 348690905544051064152001

theorem tailTrace_3055829 : CollatzResearch.WordTrace tailWord_3055829 prefixEnd_3055829 348690905544051064152001 := by
  unfold tailWord_3055829
  simp only [CollatzResearch.WordTrace]
  refine ⟨111455240046260901888202541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74303493364173934592135027 111455240046260901888202541)
  ·
    refine ⟨41795715017347838208075953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111455240046260901888202541 41795715017347838208075953)
    ·
      refine ⟨31346786263010878656056965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41795715017347838208075953 31346786263010878656056965)
      ·
        refine ⟨5877522424314539748010681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31346786263010878656056965 5877522424314539748010681)
        ·
          refine ⟨4408141818235904811008011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877522424314539748010681 4408141818235904811008011)
          ·
            refine ⟨6612212727353857216512017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408141818235904811008011 6612212727353857216512017)
            ·
              refine ⟨4959159545515392912384013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6612212727353857216512017 4959159545515392912384013)
              ·
                refine ⟨1859684829568272342144005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959159545515392912384013 1859684829568272342144005)
                ·
                  refine ⟨348690905544051064152001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859684829568272342144005 348690905544051064152001)
                  ·
                    rfl

theorem cell22_3055829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_3055829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055829 prefixEnd_3055829 := by exact prefixLift 3055829
  have htrace : WordTrace (prefixWord ++ tailWord_3055829) baseStart_3055829 baseEnd_3055829 := by
    simpa [prefixWord, tailWord_3055829, baseEnd_3055829] using wordTrace_append hprefix tailTrace_3055829
  have hstable : (prefixWord ++ tailWord_3055829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055829).length < 2 ^ (prefixWord ++ tailWord_3055829).sum := by decide
  have hdescent : baseEnd_3055829 < baseStart_3055829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055874 : List Nat := [3, 4, 1, 1, 2, 3, 2, 6]
def baseStart_3055874 : Nat := 118140960795 + 3055874 * 2 ^ 59
def prefixEnd_3055874 : Nat := 4983230072969 + 3 ^ 40 * 3055874 * 2
def baseEnd_3055874 : Nat := 116232013450198675008985

theorem tailTrace_3055874 : CollatzResearch.WordTrace tailWord_3055874 prefixEnd_3055874 116232013450198675008985 := by
  unfold tailWord_3055874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27864220332774468643397669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74304587554065249715727117 27864220332774468643397669)
  ·
    refine ⟨5224541312395212870637063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27864220332774468643397669 5224541312395212870637063)
    ·
      refine ⟨7836811968592819305955595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224541312395212870637063 7836811968592819305955595)
      ·
        refine ⟨11755217952889228958933393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836811968592819305955595 11755217952889228958933393)
        ·
          refine ⟨8816413464666921719200045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11755217952889228958933393 8816413464666921719200045)
          ·
            refine ⟨3306155049250095644700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8816413464666921719200045 3306155049250095644700017)
            ·
              refine ⟨2479616286937571733525013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306155049250095644700017 2479616286937571733525013)
              ·
                refine ⟨116232013450198675008985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2479616286937571733525013 116232013450198675008985)
                ·
                  rfl

theorem cell22_3055874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_3055874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055874 prefixEnd_3055874 := by exact prefixLift 3055874
  have htrace : WordTrace (prefixWord ++ tailWord_3055874) baseStart_3055874 baseEnd_3055874 := by
    simpa [prefixWord, tailWord_3055874, baseEnd_3055874] using wordTrace_append hprefix tailTrace_3055874
  have hstable : (prefixWord ++ tailWord_3055874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055874).length < 2 ^ (prefixWord ++ tailWord_3055874).sum := by decide
  have hdescent : baseEnd_3055874 < baseStart_3055874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055889 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_3055889 : Nat := 118140960795 + 3055889 * 2 ^ 59
def prefixEnd_3055889 : Nat := 4983230072969 + 3 ^ 40 * 3055889 * 2
def baseEnd_3055889 : Nat := 1046093255858333035955819

theorem tailTrace_3055889 : CollatzResearch.WordTrace tailWord_3055889 prefixEnd_3055889 1046093255858333035955819 := by
  unfold tailWord_3055889
  simp only [CollatzResearch.WordTrace]
  refine ⟨111457428426043532135386721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74304952284029021423591147 111457428426043532135386721)
  ·
    refine ⟨83593071319532649101540041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111457428426043532135386721 83593071319532649101540041)
    ·
      refine ⟨62694803489649486826155031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83593071319532649101540041 62694803489649486826155031)
      ·
        refine ⟨94042205234474230239232547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62694803489649486826155031 94042205234474230239232547)
        ·
          refine ⟨141063307851711345358848821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94042205234474230239232547 141063307851711345358848821)
          ·
            refine ⟨13224685111097938627392077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141063307851711345358848821 13224685111097938627392077)
            ·
              refine ⟨4959256916661726985272029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13224685111097938627392077 4959256916661726985272029)
              ·
                refine ⟨1859721343748147619477011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959256916661726985272029 1859721343748147619477011)
                ·
                  refine ⟨2789582015622221429215517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859721343748147619477011 2789582015622221429215517)
                  ·
                    refine ⟨1046093255858333035955819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789582015622221429215517 1046093255858333035955819)
                    ·
                      rfl

theorem cell22_3055889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_3055889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055889 prefixEnd_3055889 := by exact prefixLift 3055889
  have htrace : WordTrace (prefixWord ++ tailWord_3055889) baseStart_3055889 baseEnd_3055889 := by
    simpa [prefixWord, tailWord_3055889, baseEnd_3055889] using wordTrace_append hprefix tailTrace_3055889
  have hstable : (prefixWord ++ tailWord_3055889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055889).length < 2 ^ (prefixWord ++ tailWord_3055889).sum := by decide
  have hdescent : baseEnd_3055889 < baseStart_3055889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055960 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_3055960 : Nat := 118140960795 + 3055960 * 2 ^ 59
def prefixEnd_3055960 : Nat := 4983230072969 + 3 ^ 40 * 3055960 * 2
def baseEnd_3055960 : Nat := 1046117560609312517430601

theorem tailTrace_3055960 : CollatzResearch.WordTrace tailWord_3055960 prefixEnd_3055960 1046117560609312517430601 := by
  unfold tailWord_3055960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730009004393155630610667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74306678672524207507480889 55730009004393155630610667)
  ·
    refine ⟨83595013506589733445916001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55730009004393155630610667 83595013506589733445916001)
    ·
      refine ⟨62696260129942300084437001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83595013506589733445916001 62696260129942300084437001)
      ·
        refine ⟨47022195097456725063327751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62696260129942300084437001 47022195097456725063327751)
        ·
          refine ⟨70533292646185087594991627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47022195097456725063327751 70533292646185087594991627)
          ·
            refine ⟨105799938969277631392487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70533292646185087594991627 105799938969277631392487441)
            ·
              refine ⟨79349954226958223544365581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105799938969277631392487441 79349954226958223544365581)
              ·
                refine ⟨29756232835109333829137093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79349954226958223544365581 29756232835109333829137093)
                ·
                  refine ⟨5579293656583000092963205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29756232835109333829137093 5579293656583000092963205)
                  ·
                    refine ⟨1046117560609312517430601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579293656583000092963205 1046117560609312517430601)
                    ·
                      rfl

theorem cell22_3055960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_3055960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3055960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3055960 prefixEnd_3055960 := by exact prefixLift 3055960
  have htrace : WordTrace (prefixWord ++ tailWord_3055960) baseStart_3055960 baseEnd_3055960 := by
    simpa [prefixWord, tailWord_3055960, baseEnd_3055960] using wordTrace_append hprefix tailTrace_3055960
  have hstable : (prefixWord ++ tailWord_3055960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055960).length < 2 ^ (prefixWord ++ tailWord_3055960).sum := by decide
  have hdescent : baseEnd_3055960 < baseStart_3055960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056007 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3056007 : Nat := 118140960795 + 3056007 * 2 ^ 59
def prefixEnd_3056007 : Nat := 4983230072969 + 3 ^ 40 * 3056007 * 2
def baseEnd_3056007 : Nat := 1046133649669820061505457

theorem tailTrace_3056007 : CollatzResearch.WordTrace tailWord_3056007 prefixEnd_3056007 1046133649669820061505457 := by
  unfold tailWord_3056007
  simp only [CollatzResearch.WordTrace]
  refine ⟨111461732239616038288182275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74307821493077358858788183 111461732239616038288182275)
  ·
    refine ⟨167192598359424057432273413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111461732239616038288182275 167192598359424057432273413)
    ·
      refine ⟨31348612192392010768551265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167192598359424057432273413 31348612192392010768551265)
      ·
        refine ⟨23511459144294008076413449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31348612192392010768551265 23511459144294008076413449)
        ·
          refine ⟨17633594358220506057310087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23511459144294008076413449 17633594358220506057310087)
          ·
            refine ⟨26450391537330759085965131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17633594358220506057310087 26450391537330759085965131)
            ·
              refine ⟨39675587305996138628947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26450391537330759085965131 39675587305996138628947697)
              ·
                refine ⟨29756690479497103971710773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39675587305996138628947697 29756690479497103971710773)
                ·
                  refine ⟨2789689732452853497347885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29756690479497103971710773 2789689732452853497347885)
                  ·
                    refine ⟨1046133649669820061505457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789689732452853497347885 1046133649669820061505457)
                    ·
                      rfl

theorem cell22_3056007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3056007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056007 prefixEnd_3056007 := by exact prefixLift 3056007
  have htrace : WordTrace (prefixWord ++ tailWord_3056007) baseStart_3056007 baseEnd_3056007 := by
    simpa [prefixWord, tailWord_3056007, baseEnd_3056007] using wordTrace_append hprefix tailTrace_3056007
  have hstable : (prefixWord ++ tailWord_3056007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056007).length < 2 ^ (prefixWord ++ tailWord_3056007).sum := by decide
  have hdescent : baseEnd_3056007 < baseStart_3056007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056024 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_3056024 : Nat := 118140960795 + 3056024 * 2 ^ 59
def prefixEnd_3056024 : Nat := 4983230072969 + 3 ^ 40 * 3056024 * 2
def baseEnd_3056024 : Nat := 1046139469117237683830405

theorem tailTrace_3056024 : CollatzResearch.WordTrace tailWord_3056024 prefixEnd_3056024 1046139469117237683830405 := by
  unfold tailWord_3056024
  simp only [CollatzResearch.WordTrace]
  refine ⟨55731176140277225095775563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74308234853702966794367417 55731176140277225095775563)
  ·
    refine ⟨83596764210415837643663345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55731176140277225095775563 83596764210415837643663345)
    ·
      refine ⟨62697573157811878232747509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83596764210415837643663345 62697573157811878232747509)
      ·
        refine ⟨5877897483544863584320079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62697573157811878232747509 5877897483544863584320079)
        ·
          refine ⟨8816846225317295376480119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877897483544863584320079 8816846225317295376480119)
          ·
            refine ⟨13225269337975943064720179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816846225317295376480119 13225269337975943064720179)
            ·
              refine ⟨19837904006963914597080269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13225269337975943064720179 19837904006963914597080269)
              ·
                refine ⟨7439214002611467973905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19837904006963914597080269 7439214002611467973905101)
                ·
                  refine ⟨2789705250979300490214413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7439214002611467973905101 2789705250979300490214413)
                  ·
                    refine ⟨1046139469117237683830405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789705250979300490214413 1046139469117237683830405)
                    ·
                      rfl

theorem cell22_3056024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_3056024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056024 prefixEnd_3056024 := by exact prefixLift 3056024
  have htrace : WordTrace (prefixWord ++ tailWord_3056024) baseStart_3056024 baseEnd_3056024 := by
    simpa [prefixWord, tailWord_3056024, baseEnd_3056024] using wordTrace_append hprefix tailTrace_3056024
  have hstable : (prefixWord ++ tailWord_3056024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056024).length < 2 ^ (prefixWord ++ tailWord_3056024).sum := by decide
  have hdescent : baseEnd_3056024 < baseStart_3056024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056080 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_3056080 : Nat := 118140960795 + 3056080 * 2 ^ 59
def prefixEnd_3056080 : Nat := 4983230072969 + 3 ^ 40 * 3056080 * 2
def baseEnd_3056080 : Nat := 1046158639061672204430233

theorem tailTrace_3056080 : CollatzResearch.WordTrace tailWord_3056080 prefixEnd_3056080 1046158639061672204430233 := by
  unfold tailWord_3056080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55732197384175785877794847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74309596512234381170393129 55732197384175785877794847)
  ·
    refine ⟨83598296076263678816692271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55732197384175785877794847 83598296076263678816692271)
    ·
      refine ⟨125397444114395518225038407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83598296076263678816692271 125397444114395518225038407)
      ·
        refine ⟨188096166171593277337557611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125397444114395518225038407 188096166171593277337557611)
        ·
          refine ⟨282144249257389916006336417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188096166171593277337557611 282144249257389916006336417)
          ·
            refine ⟨211608186943042437004752313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282144249257389916006336417 211608186943042437004752313)
            ·
              refine ⟨158706140207281827753564235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211608186943042437004752313 158706140207281827753564235)
              ·
                refine ⟨238059210310922741630346353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158706140207281827753564235 238059210310922741630346353)
                ·
                  refine ⟨178544407733192056222759765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238059210310922741630346353 178544407733192056222759765)
                  ·
                    refine ⟨1046158639061672204430233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178544407733192056222759765 1046158639061672204430233)
                    ·
                      rfl

theorem cell22_3056080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_3056080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056080 prefixEnd_3056080 := by exact prefixLift 3056080
  have htrace : WordTrace (prefixWord ++ tailWord_3056080) baseStart_3056080 baseEnd_3056080 := by
    simpa [prefixWord, tailWord_3056080, baseEnd_3056080] using wordTrace_append hprefix tailTrace_3056080
  have hstable : (prefixWord ++ tailWord_3056080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056080).length < 2 ^ (prefixWord ++ tailWord_3056080).sum := by decide
  have hdescent : baseEnd_3056080 < baseStart_3056080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056097 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3056097 : Nat := 118140960795 + 3056097 * 2 ^ 59
def prefixEnd_3056097 : Nat := 4983230072969 + 3 ^ 40 * 3056097 * 2
def baseEnd_3056097 : Nat := 1046164458509089826755181

theorem tailTrace_3056097 : CollatzResearch.WordTrace tailWord_3056097 prefixEnd_3056097 1046164458509089826755181 := by
  unfold tailWord_3056097
  simp only [CollatzResearch.WordTrace]
  refine ⟨111465014809289983658958545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74310009872859989105972363 111465014809289983658958545)
  ·
    refine ⟨83598761106967487744218909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111465014809289983658958545 83598761106967487744218909)
    ·
      refine ⟨31349535415112807904082091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83598761106967487744218909 31349535415112807904082091)
      ·
        refine ⟨47024303122669211856123137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31349535415112807904082091 47024303122669211856123137)
        ·
          refine ⟨35268227342001908892092353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47024303122669211856123137 35268227342001908892092353)
          ·
            refine ⟨26451170506501431669069265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35268227342001908892092353 26451170506501431669069265)
            ·
              refine ⟨19838377879876073751801949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26451170506501431669069265 19838377879876073751801949)
              ·
                refine ⟨7439391704953527656925731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19838377879876073751801949 7439391704953527656925731)
                ·
                  refine ⟨11159087557430291485388597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439391704953527656925731 11159087557430291485388597)
                  ·
                    refine ⟨1046164458509089826755181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11159087557430291485388597 1046164458509089826755181)
                    ·
                      rfl

theorem cell22_3056097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3056097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056097 prefixEnd_3056097 := by exact prefixLift 3056097
  have htrace : WordTrace (prefixWord ++ tailWord_3056097) baseStart_3056097 baseEnd_3056097 := by
    simpa [prefixWord, tailWord_3056097, baseEnd_3056097] using wordTrace_append hprefix tailTrace_3056097
  have hstable : (prefixWord ++ tailWord_3056097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056097).length < 2 ^ (prefixWord ++ tailWord_3056097).sum := by decide
  have hdescent : baseEnd_3056097 < baseStart_3056097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056129 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3056129 : Nat := 118140960795 + 3056129 * 2 ^ 59
def prefixEnd_3056129 : Nat := 4983230072969 + 3 ^ 40 * 3056129 * 2
def baseEnd_3056129 : Nat := 1046175412763052409955083

theorem tailTrace_3056129 : CollatzResearch.WordTrace tailWord_3056129 prefixEnd_3056129 1046175412763052409955083 := by
  unfold tailWord_3056129
  simp only [CollatzResearch.WordTrace]
  refine ⟨111466181945174053124123441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74310787963449368749415627 111466181945174053124123441)
  ·
    refine ⟨83599636458880539843092581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111466181945174053124123441 83599636458880539843092581)
    ·
      refine ⟨15674931836040101220579859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83599636458880539843092581 15674931836040101220579859)
      ·
        refine ⟨23512397754060151830869789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15674931836040101220579859 23512397754060151830869789)
        ·
          refine ⟨8817149157772556936576171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23512397754060151830869789 8817149157772556936576171)
          ·
            refine ⟨13225723736658835404864257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817149157772556936576171 13225723736658835404864257)
            ·
              refine ⟨9919292802494126553648193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13225723736658835404864257 9919292802494126553648193)
              ·
                refine ⟨7439469601870594915236145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919292802494126553648193 7439469601870594915236145)
                ·
                  refine ⟨5579602201402946186427109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439469601870594915236145 5579602201402946186427109)
                  ·
                    refine ⟨1046175412763052409955083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579602201402946186427109 1046175412763052409955083)
                    ·
                      rfl

theorem cell22_3056129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3056129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056129 prefixEnd_3056129 := by exact prefixLift 3056129
  have htrace : WordTrace (prefixWord ++ tailWord_3056129) baseStart_3056129 baseEnd_3056129 := by
    simpa [prefixWord, tailWord_3056129, baseEnd_3056129] using wordTrace_append hprefix tailTrace_3056129
  have hstable : (prefixWord ++ tailWord_3056129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056129).length < 2 ^ (prefixWord ++ tailWord_3056129).sum := by decide
  have hdescent : baseEnd_3056129 < baseStart_3056129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056148 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3056148 : Nat := 118140960795 + 3056148 * 2 ^ 59
def prefixEnd_3056148 : Nat := 4983230072969 + 3 ^ 40 * 3056148 * 2
def baseEnd_3056148 : Nat := 1046181916851342693730025

theorem tailTrace_3056148 : CollatzResearch.WordTrace tailWord_3056148 prefixEnd_3056148 1046181916851342693730025 := by
  unfold tailWord_3056148
  simp only [CollatzResearch.WordTrace]
  refine ⟨55733437466052609684532549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74311249954736812912710065 55733437466052609684532549)
  ·
    refine ⟨10450019524884864315849853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55733437466052609684532549 10450019524884864315849853)
    ·
      refine ⟨3918757321831824118443695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10450019524884864315849853 3918757321831824118443695)
      ·
        refine ⟨5878135982747736177665543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918757321831824118443695 5878135982747736177665543)
        ·
          refine ⟨8817203974121604266498315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878135982747736177665543 8817203974121604266498315)
          ·
            refine ⟨13225805961182406399747473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817203974121604266498315 13225805961182406399747473)
            ·
              refine ⟨9919354470886804799810605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13225805961182406399747473 9919354470886804799810605)
              ·
                refine ⟨3719757926582551799928977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9919354470886804799810605 3719757926582551799928977)
                ·
                  refine ⟨2789818444936913849946733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719757926582551799928977 2789818444936913849946733)
                  ·
                    refine ⟨1046181916851342693730025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789818444936913849946733 1046181916851342693730025)
                    ·
                      rfl

theorem cell22_3056148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3056148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056148 prefixEnd_3056148 := by exact prefixLift 3056148
  have htrace : WordTrace (prefixWord ++ tailWord_3056148) baseStart_3056148 baseEnd_3056148 := by
    simpa [prefixWord, tailWord_3056148, baseEnd_3056148] using wordTrace_append hprefix tailTrace_3056148
  have hstable : (prefixWord ++ tailWord_3056148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056148).length < 2 ^ (prefixWord ++ tailWord_3056148).sum := by decide
  have hdescent : baseEnd_3056148 < baseStart_3056148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056176 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_3056176 : Nat := 118140960795 + 3056176 * 2 ^ 59
def prefixEnd_3056176 : Nat := 4983230072969 + 3 ^ 40 * 3056176 * 2
def baseEnd_3056176 : Nat := 1046191501823559954029939

theorem tailTrace_3056176 : CollatzResearch.WordTrace tailWord_3056176 prefixEnd_3056176 1046191501823559954029939 := by
  unfold tailWord_3056176
  simp only [CollatzResearch.WordTrace]
  refine ⟨55733948088001890075542191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74311930784002520100722921 55733948088001890075542191)
  ·
    refine ⟨83600922132002835113313287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55733948088001890075542191 83600922132002835113313287)
    ·
      refine ⟨125401383198004252669969931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83600922132002835113313287 125401383198004252669969931)
      ·
        refine ⟨188102074797006379004954897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125401383198004252669969931 188102074797006379004954897)
        ·
          refine ⟨141076556097754784253716173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188102074797006379004954897 141076556097754784253716173)
          ·
            refine ⟨52903708536658044095143565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141076556097754784253716173 52903708536658044095143565)
            ·
              refine ⟨19838890701246766535678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52903708536658044095143565 19838890701246766535678837)
              ·
                refine ⟨1859896003241884362719891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19838890701246766535678837 1859896003241884362719891)
                ·
                  refine ⟨2789844004862826544079837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859896003241884362719891 2789844004862826544079837)
                  ·
                    refine ⟨1046191501823559954029939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789844004862826544079837 1046191501823559954029939)
                    ·
                      rfl

theorem cell22_3056176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_3056176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056176 prefixEnd_3056176 := by exact prefixLift 3056176
  have htrace : WordTrace (prefixWord ++ tailWord_3056176) baseStart_3056176 baseEnd_3056176 := by
    simpa [prefixWord, tailWord_3056176, baseEnd_3056176] using wordTrace_append hprefix tailTrace_3056176
  have hstable : (prefixWord ++ tailWord_3056176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056176).length < 2 ^ (prefixWord ++ tailWord_3056176).sum := by decide
  have hdescent : baseEnd_3056176 < baseStart_3056176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056189 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 7]
def baseStart_3056189 : Nat := 118140960795 + 3056189 * 2 ^ 59
def prefixEnd_3056189 : Nat := 4983230072969 + 3 ^ 40 * 3056189 * 2
def baseEnd_3056189 : Nat := 348731983996410751151633

theorem tailTrace_3056189 : CollatzResearch.WordTrace tailWord_3056189 prefixEnd_3056189 348731983996410751151633 := by
  unfold tailWord_3056189
  simp only [CollatzResearch.WordTrace]
  refine ⟨111468370324956683371307621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74312246883304455580871747 111468370324956683371307621)
  ·
    refine ⟨20900319435929378132120179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111468370324956683371307621 20900319435929378132120179)
    ·
      refine ⟨31350479153894067198180269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20900319435929378132120179 31350479153894067198180269)
      ·
        refine ⟨11756429682710275199317601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31350479153894067198180269 11756429682710275199317601)
        ·
          refine ⟨8817322262032706399488201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11756429682710275199317601 8817322262032706399488201)
          ·
            refine ⟨6612991696524529799616151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817322262032706399488201 6612991696524529799616151)
            ·
              refine ⟨9919487544786794699424227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612991696524529799616151 9919487544786794699424227)
              ·
                refine ⟨14879231317180192049136341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9919487544786794699424227 14879231317180192049136341)
                ·
                  refine ⟨348731983996410751151633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14879231317180192049136341 348731983996410751151633)
                  ·
                    rfl

theorem cell22_3056189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_3056189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056189 prefixEnd_3056189 := by exact prefixLift 3056189
  have htrace : WordTrace (prefixWord ++ tailWord_3056189) baseStart_3056189 baseEnd_3056189 := by
    simpa [prefixWord, tailWord_3056189, baseEnd_3056189] using wordTrace_append hprefix tailTrace_3056189
  have hstable : (prefixWord ++ tailWord_3056189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056189).length < 2 ^ (prefixWord ++ tailWord_3056189).sum := by decide
  have hdescent : baseEnd_3056189 < baseStart_3056189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056193 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3056193 : Nat := 118140960795 + 3056193 * 2 ^ 59
def prefixEnd_3056193 : Nat := 4983230072969 + 3 ^ 40 * 3056193 * 2
def baseEnd_3056193 : Nat := 1046197321270977576354887

theorem tailTrace_3056193 : CollatzResearch.WordTrace tailWord_3056193 prefixEnd_3056193 1046197321270977576354887 := by
  unfold tailWord_3056193
  simp only [CollatzResearch.WordTrace]
  refine ⟨111468516216942192054453233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74312344144628128036302155 111468516216942192054453233)
  ·
    refine ⟨83601387162706644040839925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111468516216942192054453233 83601387162706644040839925)
    ·
      refine ⟨7837630046503747878828743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83601387162706644040839925 7837630046503747878828743)
      ·
        refine ⟨11756445069755621818243115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7837630046503747878828743 11756445069755621818243115)
        ·
          refine ⟨17634667604633432727364673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11756445069755621818243115 17634667604633432727364673)
          ·
            refine ⟨13226000703475074545523505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17634667604633432727364673 13226000703475074545523505)
            ·
              refine ⟨9919500527606305909142629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226000703475074545523505 9919500527606305909142629)
              ·
                refine ⟨1859906348926182357964243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9919500527606305909142629 1859906348926182357964243)
                ·
                  refine ⟨2789859523389273536946365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859906348926182357964243 2789859523389273536946365)
                  ·
                    refine ⟨1046197321270977576354887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789859523389273536946365 1046197321270977576354887)
                    ·
                      rfl

theorem cell22_3056193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3056193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056193 prefixEnd_3056193 := by exact prefixLift 3056193
  have htrace : WordTrace (prefixWord ++ tailWord_3056193) baseStart_3056193 baseEnd_3056193 := by
    simpa [prefixWord, tailWord_3056193, baseEnd_3056193] using wordTrace_append hprefix tailTrace_3056193
  have hstable : (prefixWord ++ tailWord_3056193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056193).length < 2 ^ (prefixWord ++ tailWord_3056193).sum := by decide
  have hdescent : baseEnd_3056193 < baseStart_3056193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056302 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3056302 : Nat := 118140960795 + 3056302 * 2 ^ 59
def prefixEnd_3056302 : Nat := 4983230072969 + 3 ^ 40 * 3056302 * 2
def baseEnd_3056302 : Nat := 348744878066179208459851

theorem tailTrace_3056302 : CollatzResearch.WordTrace tailWord_3056302 prefixEnd_3056302 348744878066179208459851 := by
  unfold tailWord_3056302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934061471693412958771395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74314994515698202446780773 13934061471693412958771395)
  ·
    refine ⟨20901092207540119438157093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13934061471693412958771395 20901092207540119438157093)
    ·
      refine ⟨3918954788913772394654455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20901092207540119438157093 3918954788913772394654455)
      ·
        refine ⟨5878432183370658591981683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918954788913772394654455 5878432183370658591981683)
        ·
          refine ⟨8817648275055987887972525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878432183370658591981683 8817648275055987887972525)
          ·
            refine ⟨3306618103145995457989697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8817648275055987887972525 3306618103145995457989697)
            ·
              refine ⟨2479963577359496593492273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306618103145995457989697 2479963577359496593492273)
              ·
                refine ⟨1859972683019622445119205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479963577359496593492273 1859972683019622445119205)
                ·
                  refine ⟨348744878066179208459851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859972683019622445119205 348744878066179208459851)
                  ·
                    rfl

theorem cell22_3056302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3056302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056302 prefixEnd_3056302 := by exact prefixLift 3056302
  have htrace : WordTrace (prefixWord ++ tailWord_3056302) baseStart_3056302 baseEnd_3056302 := by
    simpa [prefixWord, tailWord_3056302, baseEnd_3056302] using wordTrace_append hprefix tailTrace_3056302
  have hstable : (prefixWord ++ tailWord_3056302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056302).length < 2 ^ (prefixWord ++ tailWord_3056302).sum := by decide
  have hdescent : baseEnd_3056302 < baseStart_3056302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056388 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_3056388 : Nat := 118140960795 + 3056388 * 2 ^ 59
def prefixEnd_3056388 : Nat := 4983230072969 + 3 ^ 40 * 3056388 * 2
def baseEnd_3056388 : Nat := 1046264073756062067729289

theorem tailTrace_3056388 : CollatzResearch.WordTrace tailWord_3056388 prefixEnd_3056388 1046264073756062067729289 := by
  unfold tailWord_3056388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55737814225617870178900909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74317085634157160238534545 55737814225617870178900909)
  ·
    refine ⟨20901680334606701317087841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55737814225617870178900909 20901680334606701317087841)
    ·
      refine ⟨15676260250955025987815881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20901680334606701317087841 15676260250955025987815881)
      ·
        refine ⟨11757195188216269490861911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15676260250955025987815881 11757195188216269490861911)
        ·
          refine ⟨17635792782324404236292867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757195188216269490861911 17635792782324404236292867)
          ·
            refine ⟨26453689173486606354439301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17635792782324404236292867 26453689173486606354439301)
            ·
              refine ⟨4960066720028738691457369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26453689173486606354439301 4960066720028738691457369)
              ·
                refine ⟨3720050040021554018593027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4960066720028738691457369 3720050040021554018593027)
                ·
                  refine ⟨5580075060032331027889541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720050040021554018593027 5580075060032331027889541)
                  ·
                    refine ⟨1046264073756062067729289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5580075060032331027889541 1046264073756062067729289)
                    ·
                      rfl

theorem cell22_3056388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_3056388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056388 prefixEnd_3056388 := by exact prefixLift 3056388
  have htrace : WordTrace (prefixWord ++ tailWord_3056388) baseStart_3056388 baseEnd_3056388 := by
    simpa [prefixWord, tailWord_3056388, baseEnd_3056388] using wordTrace_append hprefix tailTrace_3056388
  have hstable : (prefixWord ++ tailWord_3056388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056388).length < 2 ^ (prefixWord ++ tailWord_3056388).sum := by decide
  have hdescent : baseEnd_3056388 < baseStart_3056388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056399 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3056399 : Nat := 118140960795 + 3056399 * 2 ^ 59
def prefixEnd_3056399 : Nat := 4983230072969 + 3 ^ 40 * 3056399 * 2
def baseEnd_3056399 : Nat := 1046267839280861705704255

theorem tailTrace_3056399 : CollatzResearch.WordTrace tailWord_3056399 prefixEnd_3056399 1046267839280861705704255 := by
  unfold tailWord_3056399
  simp only [CollatzResearch.WordTrace]
  refine ⟨111476029654195889236452251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74317353102797259490968167 111476029654195889236452251)
  ·
    refine ⟨167214044481293833854678377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111476029654195889236452251 167214044481293833854678377)
    ·
      refine ⟨125410533360970375391008783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167214044481293833854678377 125410533360970375391008783)
      ·
        refine ⟨188115800041455563086513175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125410533360970375391008783 188115800041455563086513175)
        ·
          refine ⟨282173700062183344629769763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188115800041455563086513175 282173700062183344629769763)
          ·
            refine ⟨423260550093275016944654645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282173700062183344629769763 423260550093275016944654645)
            ·
              refine ⟨39680676571244532838561373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 423260550093275016944654645 39680676571244532838561373)
              ·
                refine ⟨14880253714216699814460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39680676571244532838561373 14880253714216699814460515)
                ·
                  refine ⟨22320380571325049721690773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14880253714216699814460515 22320380571325049721690773)
                  ·
                    refine ⟨1046267839280861705704255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22320380571325049721690773 1046267839280861705704255)
                    ·
                      rfl

theorem cell22_3056399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3056399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056399 prefixEnd_3056399 := by exact prefixLift 3056399
  have htrace : WordTrace (prefixWord ++ tailWord_3056399) baseStart_3056399 baseEnd_3056399 := by
    simpa [prefixWord, tailWord_3056399, baseEnd_3056399] using wordTrace_append hprefix tailTrace_3056399
  have hstable : (prefixWord ++ tailWord_3056399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056399).length < 2 ^ (prefixWord ++ tailWord_3056399).sum := by decide
  have hdescent : baseEnd_3056399 < baseStart_3056399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056401 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_3056401 : Nat := 118140960795 + 3056401 * 2 ^ 59
def prefixEnd_3056401 : Nat := 4983230072969 + 3 ^ 40 * 3056401 * 2
def baseEnd_3056401 : Nat := 1046268523921734367154249

theorem tailTrace_3056401 : CollatzResearch.WordTrace tailWord_3056401 prefixEnd_3056401 1046268523921734367154249 := by
  unfold tailWord_3056401
  simp only [CollatzResearch.WordTrace]
  refine ⟨111476102600188643578025057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74317401733459095718683371 111476102600188643578025057)
  ·
    refine ⟨83607076950141482683518793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111476102600188643578025057 83607076950141482683518793)
    ·
      refine ⟨62705307712606112012639095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83607076950141482683518793 62705307712606112012639095)
      ·
        refine ⟨94057961568909168018958643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62705307712606112012639095 94057961568909168018958643)
        ·
          refine ⟨141086942353363752028437965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94057961568909168018958643 141086942353363752028437965)
          ·
            refine ⟨52907603382511407010664237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141086942353363752028437965 52907603382511407010664237)
            ·
              refine ⟨19840351268441777628999089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52907603382511407010664237 19840351268441777628999089)
              ·
                refine ⟨14880263451331333221749317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19840351268441777628999089 14880263451331333221749317)
                ·
                  refine ⟨2790049397124624979077997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14880263451331333221749317 2790049397124624979077997)
                  ·
                    refine ⟨1046268523921734367154249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790049397124624979077997 1046268523921734367154249)
                    ·
                      rfl

theorem cell22_3056401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_3056401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056401 prefixEnd_3056401 := by exact prefixLift 3056401
  have htrace : WordTrace (prefixWord ++ tailWord_3056401) baseStart_3056401 baseEnd_3056401 := by
    simpa [prefixWord, tailWord_3056401, baseEnd_3056401] using wordTrace_append hprefix tailTrace_3056401
  have hstable : (prefixWord ++ tailWord_3056401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056401).length < 2 ^ (prefixWord ++ tailWord_3056401).sum := by decide
  have hdescent : baseEnd_3056401 < baseStart_3056401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056416 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_3056416 : Nat := 118140960795 + 3056416 * 2 ^ 59
def prefixEnd_3056416 : Nat := 4983230072969 + 3 ^ 40 * 3056416 * 2
def baseEnd_3056416 : Nat := 1046273658728279328029203

theorem tailTrace_3056416 : CollatzResearch.WordTrace tailWord_3056416 prefixEnd_3056416 1046273658728279328029203 := by
  unfold tailWord_3056416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55738324847567150569910551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74317766463422867426547401 55738324847567150569910551)
  ·
    refine ⟨83607487271350725854865827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55738324847567150569910551 83607487271350725854865827)
    ·
      refine ⟨125411230907026088782298741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83607487271350725854865827 125411230907026088782298741)
      ·
        refine ⟨11757302897533695823340507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125411230907026088782298741 11757302897533695823340507)
        ·
          refine ⟨17635954346300543735010761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757302897533695823340507 17635954346300543735010761)
          ·
            refine ⟨13226965759725407801258071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17635954346300543735010761 13226965759725407801258071)
            ·
              refine ⟨19840448639588111701887107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226965759725407801258071 19840448639588111701887107)
              ·
                refine ⟨29760672959382167552830661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19840448639588111701887107 29760672959382167552830661)
                ·
                  refine ⟨5580126179884156416155749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29760672959382167552830661 5580126179884156416155749)
                  ·
                    refine ⟨1046273658728279328029203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5580126179884156416155749 1046273658728279328029203)
                    ·
                      rfl

theorem cell22_3056416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_3056416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056416 prefixEnd_3056416 := by exact prefixLift 3056416
  have htrace : WordTrace (prefixWord ++ tailWord_3056416) baseStart_3056416 baseEnd_3056416 := by
    simpa [prefixWord, tailWord_3056416, baseEnd_3056416] using wordTrace_append hprefix tailTrace_3056416
  have hstable : (prefixWord ++ tailWord_3056416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056416).length < 2 ^ (prefixWord ++ tailWord_3056416).sum := by decide
  have hdescent : baseEnd_3056416 < baseStart_3056416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056418 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3056418 : Nat := 118140960795 + 3056418 * 2 ^ 59
def prefixEnd_3056418 : Nat := 4983230072969 + 3 ^ 40 * 3056418 * 2
def baseEnd_3056418 : Nat := 1046274343369151989479197

theorem tailTrace_3056418 : CollatzResearch.WordTrace tailWord_3056418 prefixEnd_3056418 1046274343369151989479197 := by
  unfold tailWord_3056418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869180660281763870348477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74317815094084703654262605 27869180660281763870348477)
  ·
    refine ⟨10450942747605661451380679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27869180660281763870348477 10450942747605661451380679)
    ·
      refine ⟨15676414121408492177071019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10450942747605661451380679 15676414121408492177071019)
      ·
        refine ⟨23514621182112738265606529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676414121408492177071019 23514621182112738265606529)
        ·
          refine ⟨17635965886584553699204897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23514621182112738265606529 17635965886584553699204897)
          ·
            refine ⟨13226974414938415274403673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17635965886584553699204897 13226974414938415274403673)
            ·
              refine ⟨9920230811203811455802755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226974414938415274403673 9920230811203811455802755)
              ·
                refine ⟨14880346216805717183704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9920230811203811455802755 14880346216805717183704133)
                ·
                  refine ⟨2790064915651071971944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14880346216805717183704133 2790064915651071971944525)
                  ·
                    refine ⟨1046274343369151989479197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790064915651071971944525 1046274343369151989479197)
                    ·
                      rfl

theorem cell22_3056418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3056418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056418 prefixEnd_3056418 := by exact prefixLift 3056418
  have htrace : WordTrace (prefixWord ++ tailWord_3056418) baseStart_3056418 baseEnd_3056418 := by
    simpa [prefixWord, tailWord_3056418, baseEnd_3056418] using wordTrace_append hprefix tailTrace_3056418
  have hstable : (prefixWord ++ tailWord_3056418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056418).length < 2 ^ (prefixWord ++ tailWord_3056418).sum := by decide
  have hdescent : baseEnd_3056418 < baseStart_3056418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056420 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_3056420 : Nat := 118140960795 + 3056420 * 2 ^ 59
def prefixEnd_3056420 : Nat := 4983230072969 + 3 ^ 40 * 3056420 * 2
def baseEnd_3056420 : Nat := 348758342670008216976397

theorem tailTrace_3056420 : CollatzResearch.WordTrace tailWord_3056420 prefixEnd_3056420 348758342670008216976397 := by
  unfold tailWord_3056420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55738397793559904911483357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74317863724746539881977809 55738397793559904911483357)
  ·
    refine ⟨20901899172584964341806259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55738397793559904911483357 20901899172584964341806259)
    ·
      refine ⟨31352848758877446512709389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20901899172584964341806259 31352848758877446512709389)
      ·
        refine ⟨11757318284579042442266021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31352848758877446512709389 11757318284579042442266021)
        ·
          refine ⟨2204497178358570457924879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11757318284579042442266021 2204497178358570457924879)
          ·
            refine ⟨3306745767537855686887319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204497178358570457924879 3306745767537855686887319)
            ·
              refine ⟨4960118651306783530330979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306745767537855686887319 4960118651306783530330979)
              ·
                refine ⟨7440177976960175295496469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960118651306783530330979 7440177976960175295496469)
                ·
                  refine ⟨348758342670008216976397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7440177976960175295496469 348758342670008216976397)
                  ·
                    rfl

theorem cell22_3056420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_3056420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056420 prefixEnd_3056420 := by exact prefixLift 3056420
  have htrace : WordTrace (prefixWord ++ tailWord_3056420) baseStart_3056420 baseEnd_3056420 := by
    simpa [prefixWord, tailWord_3056420, baseEnd_3056420] using wordTrace_append hprefix tailTrace_3056420
  have hstable : (prefixWord ++ tailWord_3056420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056420).length < 2 ^ (prefixWord ++ tailWord_3056420).sum := by decide
  have hdescent : baseEnd_3056420 < baseStart_3056420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056435 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 2, 3]
def baseStart_3056435 : Nat := 118140960795 + 3056435 * 2 ^ 59
def prefixEnd_3056435 : Nat := 4983230072969 + 3 ^ 40 * 3056435 * 2
def baseEnd_3056435 : Nat := 1046280162816569611804145

theorem tailTrace_3056435 : CollatzResearch.WordTrace tailWord_3056435 prefixEnd_3056435 1046280162816569611804145 := by
  unfold tailWord_3056435
  simp only [CollatzResearch.WordTrace]
  refine ⟨111477342682065467384762759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74318228454710311589841839 111477342682065467384762759)
  ·
    refine ⟨167216014023098201077144139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111477342682065467384762759 167216014023098201077144139)
    ·
      refine ⟨250824021034647301615716209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167216014023098201077144139 250824021034647301615716209)
      ·
        refine ⟨188118015775985476211787157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250824021034647301615716209 188118015775985476211787157)
        ·
          refine ⟨8818031989499319197427523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188118015775985476211787157 8818031989499319197427523)
          ·
            refine ⟨13227047984248978796141285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818031989499319197427523 13227047984248978796141285)
            ·
              refine ⟨2480071497046683524276491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13227047984248978796141285 2480071497046683524276491)
              ·
                refine ⟨3720107245570025286414737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480071497046683524276491 3720107245570025286414737)
                ·
                  refine ⟨2790080434177518964811053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720107245570025286414737 2790080434177518964811053)
                  ·
                    refine ⟨1046280162816569611804145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790080434177518964811053 1046280162816569611804145)
                    ·
                      rfl

theorem cell22_3056435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 3].length) (baseStart_3056435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056435 prefixEnd_3056435 := by exact prefixLift 3056435
  have htrace : WordTrace (prefixWord ++ tailWord_3056435) baseStart_3056435 baseEnd_3056435 := by
    simpa [prefixWord, tailWord_3056435, baseEnd_3056435] using wordTrace_append hprefix tailTrace_3056435
  have hstable : (prefixWord ++ tailWord_3056435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056435).length < 2 ^ (prefixWord ++ tailWord_3056435).sum := by decide
  have hdescent : baseEnd_3056435 < baseStart_3056435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056480 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_3056480 : Nat := 118140960795 + 3056480 * 2 ^ 59
def prefixEnd_3056480 : Nat := 4983230072969 + 3 ^ 40 * 3056480 * 2
def baseEnd_3056480 : Nat := 1046295567236204494429007

theorem tailTrace_3056480 : CollatzResearch.WordTrace tailWord_3056480 prefixEnd_3056480 1046295567236204494429007 := by
  unfold tailWord_3056480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55739491983451220035075447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74319322644601626713433929 55739491983451220035075447)
  ·
    refine ⟨83609237975176830052613171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55739491983451220035075447 83609237975176830052613171)
    ·
      refine ⟨125413856962765245078919757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83609237975176830052613171 125413856962765245078919757)
      ·
        refine ⟨47030196361036966904594909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125413856962765245078919757 47030196361036966904594909)
        ·
          refine ⟨17636323635388862589223091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47030196361036966904594909 17636323635388862589223091)
          ·
            refine ⟨26454485453083293883834637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17636323635388862589223091 26454485453083293883834637)
            ·
              refine ⟨9920432044906235206437989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26454485453083293883834637 9920432044906235206437989)
              ·
                refine ⟨1860081008419919101207123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9920432044906235206437989 1860081008419919101207123)
                ·
                  refine ⟨2790121512629878651810685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860081008419919101207123 2790121512629878651810685)
                  ·
                    refine ⟨1046295567236204494429007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790121512629878651810685 1046295567236204494429007)
                    ·
                      rfl

theorem cell22_3056480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_3056480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056480 prefixEnd_3056480 := by exact prefixLift 3056480
  have htrace : WordTrace (prefixWord ++ tailWord_3056480) baseStart_3056480 baseEnd_3056480 := by
    simpa [prefixWord, tailWord_3056480, baseEnd_3056480] using wordTrace_append hprefix tailTrace_3056480
  have hstable : (prefixWord ++ tailWord_3056480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056480).length < 2 ^ (prefixWord ++ tailWord_3056480).sum := by decide
  have hdescent : baseEnd_3056480 < baseStart_3056480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056673 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 8]
def baseStart_3056673 : Nat := 118140960795 + 3056673 * 2 ^ 59
def prefixEnd_3056673 : Nat := 4983230072969 + 3 ^ 40 * 3056673 * 2
def baseEnd_3056673 : Nat := 348787211693472108117805

theorem tailTrace_3056673 : CollatzResearch.WordTrace tailWord_3056673 prefixEnd_3056673 348787211693472108117805 := by
  unfold tailWord_3056673
  simp only [CollatzResearch.WordTrace]
  refine ⟨111486023255203234031926673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74324015503468822687951115 111486023255203234031926673)
  ·
    refine ⟨83614517441402425523945005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111486023255203234031926673 83614517441402425523945005)
    ·
      refine ⟨31355444040525909571479377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83614517441402425523945005 31355444040525909571479377)
      ·
        refine ⟨23516583030394432178609533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31355444040525909571479377 23516583030394432178609533)
        ·
          refine ⟨8818718636397912066978575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23516583030394432178609533 8818718636397912066978575)
          ·
            refine ⟨13228077954596868100467863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818718636397912066978575 13228077954596868100467863)
            ·
              refine ⟨19842116931895302150701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228077954596868100467863 19842116931895302150701795)
              ·
                refine ⟨29763175397842953226052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19842116931895302150701795 29763175397842953226052693)
                ·
                  refine ⟨348787211693472108117805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29763175397842953226052693 348787211693472108117805)
                  ·
                    rfl

theorem cell22_3056673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_3056673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056673 prefixEnd_3056673 := by exact prefixLift 3056673
  have htrace : WordTrace (prefixWord ++ tailWord_3056673) baseStart_3056673 baseEnd_3056673 := by
    simpa [prefixWord, tailWord_3056673, baseEnd_3056673] using wordTrace_append hprefix tailTrace_3056673
  have hstable : (prefixWord ++ tailWord_3056673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056673).length < 2 ^ (prefixWord ++ tailWord_3056673).sum := by decide
  have hdescent : baseEnd_3056673 < baseStart_3056673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056688 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_3056688 : Nat := 118140960795 + 3056688 * 2 ^ 59
def prefixEnd_3056688 : Nat := 4983230072969 + 3 ^ 40 * 3056688 * 2
def baseEnd_3056688 : Nat := 1046366769886961285228369

theorem tailTrace_3056688 : CollatzResearch.WordTrace tailWord_3056688 prefixEnd_3056688 1046366769886961285228369 := by
  unfold tailWord_3056688
  simp only [CollatzResearch.WordTrace]
  refine ⟨55743285175074445796861359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74324380233432594395815145 55743285175074445796861359)
  ·
    refine ⟨83614927762611668695292039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55743285175074445796861359 83614927762611668695292039)
    ·
      refine ⟨125422391643917503042938059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83614927762611668695292039 125422391643917503042938059)
      ·
        refine ⟨188133587465876254564407089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125422391643917503042938059 188133587465876254564407089)
        ·
          refine ⟨141100190599407190923305317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188133587465876254564407089 141100190599407190923305317)
          ·
            refine ⟨26456285737388848298119747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141100190599407190923305317 26456285737388848298119747)
            ·
              refine ⟨39684428606083272447179621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26456285737388848298119747 39684428606083272447179621)
              ·
                refine ⟨7440830363640613583846179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39684428606083272447179621 7440830363640613583846179)
                ·
                  refine ⟨11161245545460920375769269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440830363640613583846179 11161245545460920375769269)
                  ·
                    refine ⟨1046366769886961285228369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11161245545460920375769269 1046366769886961285228369)
                    ·
                      rfl

theorem cell22_3056688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_3056688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056688 prefixEnd_3056688 := by exact prefixLift 3056688
  have htrace : WordTrace (prefixWord ++ tailWord_3056688) baseStart_3056688 baseEnd_3056688 := by
    simpa [prefixWord, tailWord_3056688, baseEnd_3056688] using wordTrace_append hprefix tailTrace_3056688
  have hstable : (prefixWord ++ tailWord_3056688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056688).length < 2 ^ (prefixWord ++ tailWord_3056688).sum := by decide
  have hdescent : baseEnd_3056688 < baseStart_3056688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056703 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_3056703 : Nat := 118140960795 + 3056703 * 2 ^ 59
def prefixEnd_3056703 : Nat := 4983230072969 + 3 ^ 40 * 3056703 * 2
def baseEnd_3056703 : Nat := 1046371904693506246103323

theorem tailTrace_3056703 : CollatzResearch.WordTrace tailWord_3056703 prefixEnd_3056703 1046371904693506246103323 := by
  unfold tailWord_3056703
  simp only [CollatzResearch.WordTrace]
  refine ⟨111487117445094549155518763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74324744963396366103679175 111487117445094549155518763)
  ·
    refine ⟨167230676167641823733278145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111487117445094549155518763 167230676167641823733278145)
    ·
      refine ⟨125423007125731367799958609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167230676167641823733278145 125423007125731367799958609)
      ·
        refine ⟨94067255344298525849968957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125423007125731367799958609 94067255344298525849968957)
        ·
          refine ⟨35275220754111947193738359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94067255344298525849968957 35275220754111947193738359)
          ·
            refine ⟨52912831131167920790607539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35275220754111947193738359 52912831131167920790607539)
            ·
              refine ⟨79369246696751881185911309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52912831131167920790607539 79369246696751881185911309)
              ·
                refine ⟨29763467511281955444716741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79369246696751881185911309 29763467511281955444716741)
                ·
                  refine ⟨5580650158365366645884389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29763467511281955444716741 5580650158365366645884389)
                  ·
                    refine ⟨1046371904693506246103323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5580650158365366645884389 1046371904693506246103323)
                    ·
                      rfl

theorem cell22_3056703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_3056703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056703 prefixEnd_3056703 := by exact prefixLift 3056703
  have htrace : WordTrace (prefixWord ++ tailWord_3056703) baseStart_3056703 baseEnd_3056703 := by
    simpa [prefixWord, tailWord_3056703, baseEnd_3056703] using wordTrace_append hprefix tailTrace_3056703
  have hstable : (prefixWord ++ tailWord_3056703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056703).length < 2 ^ (prefixWord ++ tailWord_3056703).sum := by decide
  have hdescent : baseEnd_3056703 < baseStart_3056703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056718 : List Nat := [4, 1, 1, 1, 1, 3, 2, 9]
def baseStart_3056718 : Nat := 118140960795 + 3056718 * 2 ^ 59
def prefixEnd_3056718 : Nat := 4983230072969 + 3 ^ 40 * 3056718 * 2
def baseEnd_3056718 : Nat := 116264115500005689664253

theorem tailTrace_3056718 : CollatzResearch.WordTrace tailWord_3056718 prefixEnd_3056718 116264115500005689664253 := by
  unfold tailWord_3056718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935958067505025839664351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74325109693360137811543205 13935958067505025839664351)
  ·
    refine ⟨20903937101257538759496527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935958067505025839664351 20903937101257538759496527)
    ·
      refine ⟨31355905651886308139244791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20903937101257538759496527 31355905651886308139244791)
      ·
        refine ⟨47033858477829462208867187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31355905651886308139244791 47033858477829462208867187)
        ·
          refine ⟨70550787716744193313300781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47033858477829462208867187 70550787716744193313300781)
          ·
            refine ⟨26456545393779072492487793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70550787716744193313300781 26456545393779072492487793)
            ·
              refine ⟨19842409045334304369365845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26456545393779072492487793 19842409045334304369365845)
              ·
                refine ⟨116264115500005689664253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19842409045334304369365845 116264115500005689664253)
                ·
                  rfl

theorem cell22_3056718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_3056718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056718 prefixEnd_3056718 := by exact prefixLift 3056718
  have htrace : WordTrace (prefixWord ++ tailWord_3056718) baseStart_3056718 baseEnd_3056718 := by
    simpa [prefixWord, tailWord_3056718, baseEnd_3056718] using wordTrace_append hprefix tailTrace_3056718
  have hstable : (prefixWord ++ tailWord_3056718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056718).length < 2 ^ (prefixWord ++ tailWord_3056718).sum := by decide
  have hdescent : baseEnd_3056718 < baseStart_3056718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056722 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3056722 : Nat := 118140960795 + 3056722 * 2 ^ 59
def prefixEnd_3056722 : Nat := 4983230072969 + 3 ^ 40 * 3056722 * 2
def baseEnd_3056722 : Nat := 1046378408781796529878265

theorem tailTrace_3056722 : CollatzResearch.WordTrace tailWord_3056722 prefixEnd_3056722 1046378408781796529878265 := by
  unfold tailWord_3056722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27871952608006428850115105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74325206954683810266973613 27871952608006428850115105)
  ·
    refine ⟨20903964456004821637586329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27871952608006428850115105 20903964456004821637586329)
    ·
      refine ⟨15677973342003616228189747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20903964456004821637586329 15677973342003616228189747)
      ·
        refine ⟨23516960013005424342284621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15677973342003616228189747 23516960013005424342284621)
        ·
          refine ⟨8818860004877034128356733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23516960013005424342284621 8818860004877034128356733)
          ·
            refine ⟨3307072501828887798133775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8818860004877034128356733 3307072501828887798133775)
            ·
              refine ⟨4960608752743331697200663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307072501828887798133775 4960608752743331697200663)
              ·
                refine ⟨7440913129114997545800995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960608752743331697200663 7440913129114997545800995)
                ·
                  refine ⟨11161369693672496318701493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440913129114997545800995 11161369693672496318701493)
                  ·
                    refine ⟨1046378408781796529878265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11161369693672496318701493 1046378408781796529878265)
                    ·
                      rfl

theorem cell22_3056722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3056722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056722 prefixEnd_3056722 := by exact prefixLift 3056722
  have htrace : WordTrace (prefixWord ++ tailWord_3056722) baseStart_3056722 baseEnd_3056722 := by
    simpa [prefixWord, tailWord_3056722, baseEnd_3056722] using wordTrace_append hprefix tailTrace_3056722
  have hstable : (prefixWord ++ tailWord_3056722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056722).length < 2 ^ (prefixWord ++ tailWord_3056722).sum := by decide
  have hdescent : baseEnd_3056722 < baseStart_3056722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056726 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3056726 : Nat := 118140960795 + 3056726 * 2 ^ 59
def prefixEnd_3056726 : Nat := 4983230072969 + 3 ^ 40 * 3056726 * 2
def baseEnd_3056726 : Nat := 1046379778063541852778253

theorem tailTrace_3056726 : CollatzResearch.WordTrace tailWord_3056726 prefixEnd_3056726 1046379778063541852778253 := by
  unfold tailWord_3056726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967997270250701505225377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74325304216007482722404021 6967997270250701505225377)
  ·
    refine ⟨5225997952688026128919033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6967997270250701505225377 5225997952688026128919033)
    ·
      refine ⟨3919498464516019596689275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5225997952688026128919033 3919498464516019596689275)
      ·
        refine ⟨5879247696774029395033913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919498464516019596689275 5879247696774029395033913)
        ·
          refine ⟨4409435772580522046275435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5879247696774029395033913 4409435772580522046275435)
          ·
            refine ⟨6614153658870783069413153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409435772580522046275435 6614153658870783069413153)
            ·
              refine ⟨4960615244153087302059865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6614153658870783069413153 4960615244153087302059865)
              ·
                refine ⟨3720461433114815476544899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4960615244153087302059865 3720461433114815476544899)
                ·
                  refine ⟨5580692149672223214817349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720461433114815476544899 5580692149672223214817349)
                  ·
                    refine ⟨1046379778063541852778253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5580692149672223214817349 1046379778063541852778253)
                    ·
                      rfl

theorem cell22_3056726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3056726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056726 prefixEnd_3056726 := by exact prefixLift 3056726
  have htrace : WordTrace (prefixWord ++ tailWord_3056726) baseStart_3056726 baseEnd_3056726 := by
    simpa [prefixWord, tailWord_3056726, baseEnd_3056726] using wordTrace_append hprefix tailTrace_3056726
  have hstable : (prefixWord ++ tailWord_3056726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056726).length < 2 ^ (prefixWord ++ tailWord_3056726).sum := by decide
  have hdescent : baseEnd_3056726 < baseStart_3056726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056840 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3056840 : Nat := 118140960795 + 3056840 * 2 ^ 59
def prefixEnd_3056840 : Nat := 4983230072969 + 3 ^ 40 * 3056840 * 2
def baseEnd_3056840 : Nat := 1046418802593283555427903

theorem tailTrace_3056840 : CollatzResearch.WordTrace tailWord_3056840 prefixEnd_3056840 1046418802593283555427903 := by
  unfold tailWord_3056840
  simp only [CollatzResearch.WordTrace]
  refine ⟨55746057122799110776627987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74328076163732147702170649 55746057122799110776627987)
  ·
    refine ⟨83619085684198666164941981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55746057122799110776627987 83619085684198666164941981)
    ·
      refine ⟨31357157131574499811853243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83619085684198666164941981 31357157131574499811853243)
      ·
        refine ⟨47035735697361749717779865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31357157131574499811853243 47035735697361749717779865)
        ·
          refine ⟨35276801773021312288334899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47035735697361749717779865 35276801773021312288334899)
          ·
            refine ⟨52915202659531968432502349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35276801773021312288334899 52915202659531968432502349)
            ·
              refine ⟨19843200997324488162188381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52915202659531968432502349 19843200997324488162188381)
              ·
                refine ⟨7441200373996683060820643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19843200997324488162188381 7441200373996683060820643)
                ·
                  refine ⟨11161800560995024591230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441200373996683060820643 11161800560995024591230965)
                  ·
                    refine ⟨1046418802593283555427903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11161800560995024591230965 1046418802593283555427903)
                    ·
                      rfl

theorem cell22_3056840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3056840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056840 prefixEnd_3056840 := by exact prefixLift 3056840
  have htrace : WordTrace (prefixWord ++ tailWord_3056840) baseStart_3056840 baseEnd_3056840 := by
    simpa [prefixWord, tailWord_3056840, baseEnd_3056840] using wordTrace_append hprefix tailTrace_3056840
  have hstable : (prefixWord ++ tailWord_3056840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056840).length < 2 ^ (prefixWord ++ tailWord_3056840).sum := by decide
  have hdescent : baseEnd_3056840 < baseStart_3056840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056874 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3056874 : Nat := 118140960795 + 3056874 * 2 ^ 59
def prefixEnd_3056874 : Nat := 4983230072969 + 3 ^ 40 * 3056874 * 2
def baseEnd_3056874 : Nat := 1046430441488118800077799

theorem tailTrace_3056874 : CollatzResearch.WordTrace tailWord_3056874 prefixEnd_3056874 1046430441488118800077799 := by
  unfold tailWord_3056874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873338581868761339998419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74328902884983363573329117 27873338581868761339998419)
  ·
    refine ⟨41810007872803142009997629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27873338581868761339998419 41810007872803142009997629)
    ·
      refine ⟨15678752952301178253749111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41810007872803142009997629 15678752952301178253749111)
      ·
        refine ⟨23518129428451767380623667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15678752952301178253749111 23518129428451767380623667)
        ·
          refine ⟨35277194142677651070935501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23518129428451767380623667 35277194142677651070935501)
          ·
            refine ⟨13228947803504119151600813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35277194142677651070935501 13228947803504119151600813)
            ·
              refine ⟨4960855426314044681850305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13228947803504119151600813 4960855426314044681850305)
              ·
                refine ⟨3720641569735533511387729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4960855426314044681850305 3720641569735533511387729)
                ·
                  refine ⟨2790481177301650133540797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720641569735533511387729 2790481177301650133540797)
                  ·
                    refine ⟨1046430441488118800077799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790481177301650133540797 1046430441488118800077799)
                    ·
                      rfl

theorem cell22_3056874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3056874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056874 prefixEnd_3056874 := by exact prefixLift 3056874
  have htrace : WordTrace (prefixWord ++ tailWord_3056874) baseStart_3056874 baseEnd_3056874 := by
    simpa [prefixWord, tailWord_3056874, baseEnd_3056874] using wordTrace_append hprefix tailTrace_3056874
  have hstable : (prefixWord ++ tailWord_3056874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056874).length < 2 ^ (prefixWord ++ tailWord_3056874).sum := by decide
  have hdescent : baseEnd_3056874 < baseStart_3056874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056904 : List Nat := [2, 1, 3, 2, 4, 2, 2, 6]
def baseStart_3056904 : Nat := 118140960795 + 3056904 * 2 ^ 59
def prefixEnd_3056904 : Nat := 4983230072969 + 3 ^ 40 * 3056904 * 2
def baseEnd_3056904 : Nat := 116271190122356524647523

theorem tailTrace_3056904 : CollatzResearch.WordTrace tailWord_3056904 prefixEnd_3056904 116271190122356524647523 := by
  unfold tailWord_3056904
  simp only [CollatzResearch.WordTrace]
  refine ⟨55747224258683180241792883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74329632344910906989057177 55747224258683180241792883)
  ·
    refine ⟨83620836388024770362689325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55747224258683180241792883 83620836388024770362689325)
    ·
      refine ⟨31357813645509288886008497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83620836388024770362689325 31357813645509288886008497)
      ·
        refine ⟨23518360234131966664506373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31357813645509288886008497 23518360234131966664506373)
        ·
          refine ⟨4409692543899743749594945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23518360234131966664506373 4409692543899743749594945)
          ·
            refine ⟨3307269407924807812196209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4409692543899743749594945 3307269407924807812196209)
            ·
              refine ⟨2480452055943605859147157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307269407924807812196209 2480452055943605859147157)
              ·
                refine ⟨116271190122356524647523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2480452055943605859147157 116271190122356524647523)
                ·
                  rfl

theorem cell22_3056904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_3056904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056904 prefixEnd_3056904 := by exact prefixLift 3056904
  have htrace : WordTrace (prefixWord ++ tailWord_3056904) baseStart_3056904 baseEnd_3056904 := by
    simpa [prefixWord, tailWord_3056904, baseEnd_3056904] using wordTrace_append hprefix tailTrace_3056904
  have hstable : (prefixWord ++ tailWord_3056904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056904).length < 2 ^ (prefixWord ++ tailWord_3056904).sum := by decide
  have hdescent : baseEnd_3056904 < baseStart_3056904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056932 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3056932 : Nat := 118140960795 + 3056932 * 2 ^ 59
def prefixEnd_3056932 : Nat := 4983230072969 + 3 ^ 40 * 3056932 * 2
def baseEnd_3056932 : Nat := 348816765357808660709207

theorem tailTrace_3056932 : CollatzResearch.WordTrace tailWord_3056932 prefixEnd_3056932 348816765357808660709207 := by
  unfold tailWord_3056932
  simp only [CollatzResearch.WordTrace]
  refine ⟨55747734880632460632802525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74330313174176614177070033 55747734880632460632802525)
  ·
    refine ⟨20905400580237172737300947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55747734880632460632802525 20905400580237172737300947)
    ·
      refine ⟨31358100870355759105951421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20905400580237172737300947 31358100870355759105951421)
      ·
        refine ⟨11759287826383409664731783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31358100870355759105951421 11759287826383409664731783)
        ·
          refine ⟨17638931739575114497097675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11759287826383409664731783 17638931739575114497097675)
          ·
            refine ⟨26458397609362671745646513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17638931739575114497097675 26458397609362671745646513)
            ·
              refine ⟨19843798207022003809234885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26458397609362671745646513 19843798207022003809234885)
              ·
                refine ⟨3720712163816625714231541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19843798207022003809234885 3720712163816625714231541)
                ·
                  refine ⟨348816765357808660709207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3720712163816625714231541 348816765357808660709207)
                  ·
                    rfl

theorem cell22_3056932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3056932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056932 prefixEnd_3056932 := by exact prefixLift 3056932
  have htrace : WordTrace (prefixWord ++ tailWord_3056932) baseStart_3056932 baseEnd_3056932 := by
    simpa [prefixWord, tailWord_3056932, baseEnd_3056932] using wordTrace_append hprefix tailTrace_3056932
  have hstable : (prefixWord ++ tailWord_3056932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056932).length < 2 ^ (prefixWord ++ tailWord_3056932).sum := by decide
  have hdescent : baseEnd_3056932 < baseStart_3056932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056936 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3056936 : Nat := 118140960795 + 3056936 * 2 ^ 59
def prefixEnd_3056936 : Nat := 4983230072969 + 3 ^ 40 * 3056936 * 2
def baseEnd_3056936 : Nat := 1046451665355171305027609

theorem tailTrace_3056936 : CollatzResearch.WordTrace tailWord_3056936 prefixEnd_3056936 1046451665355171305027609 := by
  unfold tailWord_3056936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55747807826625214974375331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74330410435500286632500441 55747807826625214974375331)
  ·
    refine ⟨83621711739937822461562997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55747807826625214974375331 83621711739937822461562997)
    ·
      refine ⟨7839535475619170855771531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83621711739937822461562997 7839535475619170855771531)
      ·
        refine ⟨11759303213428756283657297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7839535475619170855771531 11759303213428756283657297)
        ·
          refine ⟨8819477410071567212742973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11759303213428756283657297 8819477410071567212742973)
          ·
            refine ⟨3307304028776837704778615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8819477410071567212742973 3307304028776837704778615)
            ·
              refine ⟨4960956043165256557167923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307304028776837704778615 4960956043165256557167923)
              ·
                refine ⟨7441434064747884835751885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960956043165256557167923 7441434064747884835751885)
                ·
                  refine ⟨2790537774280456813406957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7441434064747884835751885 2790537774280456813406957)
                  ·
                    refine ⟨1046451665355171305027609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790537774280456813406957 1046451665355171305027609)
                    ·
                      rfl

theorem cell22_3056936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3056936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056936 prefixEnd_3056936 := by exact prefixLift 3056936
  have htrace : WordTrace (prefixWord ++ tailWord_3056936) baseStart_3056936 baseEnd_3056936 := by
    simpa [prefixWord, tailWord_3056936, baseEnd_3056936] using wordTrace_append hprefix tailTrace_3056936
  have hstable : (prefixWord ++ tailWord_3056936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056936).length < 2 ^ (prefixWord ++ tailWord_3056936).sum := by decide
  have hdescent : baseEnd_3056936 < baseStart_3056936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056949 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 5]
def baseStart_3056949 : Nat := 118140960795 + 3056949 * 2 ^ 59
def prefixEnd_3056949 : Nat := 4983230072969 + 3 ^ 40 * 3056949 * 2
def baseEnd_3056949 : Nat := 348818705173614534817523

theorem tailTrace_3056949 : CollatzResearch.WordTrace tailWord_3056949 prefixEnd_3056949 348818705173614534817523 := by
  unfold tailWord_3056949
  simp only [CollatzResearch.WordTrace]
  refine ⟨111496089802203333168973901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74330726534802222112649267 111496089802203333168973901)
  ·
    refine ⟨41811033675826249938365213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111496089802203333168973901 41811033675826249938365213)
    ·
      refine ⟨15679137628434843726886955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41811033675826249938365213 15679137628434843726886955)
      ·
        refine ⟨23518706442652265590330433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15679137628434843726886955 23518706442652265590330433)
        ·
          refine ⟨17639029831989199192747825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23518706442652265590330433 17639029831989199192747825)
          ·
            refine ⟨13229272373991899394560869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17639029831989199192747825 13229272373991899394560869)
            ·
              refine ⟨2480488570123481136480163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13229272373991899394560869 2480488570123481136480163)
              ·
                refine ⟨3720732855185221704720245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480488570123481136480163 3720732855185221704720245)
                ·
                  refine ⟨348818705173614534817523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3720732855185221704720245 348818705173614534817523)
                  ·
                    rfl

theorem cell22_3056949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_3056949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056949 prefixEnd_3056949 := by exact prefixLift 3056949
  have htrace : WordTrace (prefixWord ++ tailWord_3056949) baseStart_3056949 baseEnd_3056949 := by
    simpa [prefixWord, tailWord_3056949, baseEnd_3056949] using wordTrace_append hprefix tailTrace_3056949
  have hstable : (prefixWord ++ tailWord_3056949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056949).length < 2 ^ (prefixWord ++ tailWord_3056949).sum := by decide
  have hdescent : baseEnd_3056949 < baseStart_3056949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056960 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_3056960 : Nat := 118140960795 + 3056960 * 2 ^ 59
def prefixEnd_3056960 : Nat := 4983230072969 + 3 ^ 40 * 3056960 * 2
def baseEnd_3056960 : Nat := 348819960348547747475845

theorem tailTrace_3056960 : CollatzResearch.WordTrace tailWord_3056960 prefixEnd_3056960 348819960348547747475845 := by
  unfold tailWord_3056960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55748245502581741023812167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74330994003442321365082889 55748245502581741023812167)
  ·
    refine ⟨83622368253872611535718251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55748245502581741023812167 83622368253872611535718251)
    ·
      refine ⟨125433552380808917303577377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83622368253872611535718251 125433552380808917303577377)
      ·
        refine ⟨94075164285606687977683033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125433552380808917303577377 94075164285606687977683033)
        ·
          refine ⟨70556373214205015983262275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94075164285606687977683033 70556373214205015983262275)
          ·
            refine ⟨105834559821307523974893413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70556373214205015983262275 105834559821307523974893413)
            ·
              refine ⟨19843979966495160745292515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105834559821307523974893413 19843979966495160745292515)
              ·
                refine ⟨29765969949742741117938773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19843979966495160745292515 29765969949742741117938773)
                ·
                  refine ⟨348819960348547747475845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29765969949742741117938773 348819960348547747475845)
                  ·
                    rfl

theorem cell22_3056960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_3056960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056960 prefixEnd_3056960 := by exact prefixLift 3056960
  have htrace : WordTrace (prefixWord ++ tailWord_3056960) baseStart_3056960 baseEnd_3056960 := by
    simpa [prefixWord, tailWord_3056960, baseEnd_3056960] using wordTrace_append hprefix tailTrace_3056960
  have hstable : (prefixWord ++ tailWord_3056960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056960).length < 2 ^ (prefixWord ++ tailWord_3056960).sum := by decide
  have hdescent : baseEnd_3056960 < baseStart_3056960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056979 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 1, 4]
def baseStart_3056979 : Nat := 118140960795 + 3056979 * 2 ^ 59
def prefixEnd_3056979 : Nat := 4983230072969 + 3 ^ 40 * 3056979 * 2
def baseEnd_3056979 : Nat := 1046466385133933526202477

theorem tailTrace_3056979 : CollatzResearch.WordTrace tailWord_3056979 prefixEnd_3056979 1046466385133933526202477 := by
  unfold tailWord_3056979
  simp only [CollatzResearch.WordTrace]
  refine ⟨111497183992094648292565991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74331455994729765528377327 111497183992094648292565991)
  ·
    refine ⟨167245775988141972438848987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111497183992094648292565991 167245775988141972438848987)
    ·
      refine ⟨250868663982212958658273481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167245775988141972438848987 250868663982212958658273481)
      ·
        refine ⟨188151497986659718993705111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250868663982212958658273481 188151497986659718993705111)
        ·
          refine ⟨282227246979989578490557667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188151497986659718993705111 282227246979989578490557667)
          ·
            refine ⟨423340870469984367735836501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282227246979989578490557667 423340870469984367735836501)
            ·
              refine ⟨2480512912910064654702167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 423340870469984367735836501 2480512912910064654702167)
              ·
                refine ⟨3720769369365096982053251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480512912910064654702167 3720769369365096982053251)
                ·
                  refine ⟨5581154054047645473079877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720769369365096982053251 5581154054047645473079877)
                  ·
                    refine ⟨1046466385133933526202477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581154054047645473079877 1046466385133933526202477)
                    ·
                      rfl

theorem cell22_3056979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 4].length) (baseStart_3056979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3056979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3056979 prefixEnd_3056979 := by exact prefixLift 3056979
  have htrace : WordTrace (prefixWord ++ tailWord_3056979) baseStart_3056979 baseEnd_3056979 := by
    simpa [prefixWord, tailWord_3056979, baseEnd_3056979] using wordTrace_append hprefix tailTrace_3056979
  have hstable : (prefixWord ++ tailWord_3056979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056979).length < 2 ^ (prefixWord ++ tailWord_3056979).sum := by decide
  have hdescent : baseEnd_3056979 < baseStart_3056979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057009 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_3057009 : Nat := 118140960795 + 3057009 * 2 ^ 59
def prefixEnd_3057009 : Nat := 4983230072969 + 3 ^ 40 * 3057009 * 2
def baseEnd_3057009 : Nat := 1046476654747023447952385

theorem tailTrace_3057009 : CollatzResearch.WordTrace tailWord_3057009 prefixEnd_3057009 1046476654747023447952385 := by
  unfold tailWord_3057009
  simp only [CollatzResearch.WordTrace]
  refine ⟨111498278181985963416158081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74332185454657308944105387 111498278181985963416158081)
  ·
    refine ⟨83623708636489472562118561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111498278181985963416158081 83623708636489472562118561)
    ·
      refine ⟨62717781477367104421588921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83623708636489472562118561 62717781477367104421588921)
      ·
        refine ⟨47038336108025328316191691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62717781477367104421588921 47038336108025328316191691)
        ·
          refine ⟨70557504162037992474287537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47038336108025328316191691 70557504162037992474287537)
          ·
            refine ⟨52918128121528494355715653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70557504162037992474287537 52918128121528494355715653)
            ·
              refine ⟨9922149022786592691696685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52918128121528494355715653 9922149022786592691696685)
              ·
                refine ⟨3720805883544972259386257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9922149022786592691696685 3720805883544972259386257)
                ·
                  refine ⟨2790604412658729194539693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720805883544972259386257 2790604412658729194539693)
                  ·
                    refine ⟨1046476654747023447952385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790604412658729194539693 1046476654747023447952385)
                    ·
                      rfl

theorem cell22_3057009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_3057009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057009 prefixEnd_3057009 := by exact prefixLift 3057009
  have htrace : WordTrace (prefixWord ++ tailWord_3057009) baseStart_3057009 baseEnd_3057009 := by
    simpa [prefixWord, tailWord_3057009, baseEnd_3057009] using wordTrace_append hprefix tailTrace_3057009
  have hstable : (prefixWord ++ tailWord_3057009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057009).length < 2 ^ (prefixWord ++ tailWord_3057009).sum := by decide
  have hdescent : baseEnd_3057009 < baseStart_3057009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057026 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3057026 : Nat := 118140960795 + 3057026 * 2 ^ 59
def prefixEnd_3057026 : Nat := 4983230072969 + 3 ^ 40 * 3057026 * 2
def baseEnd_3057026 : Nat := 1046482474194441070277333

theorem tailTrace_3057026 : CollatzResearch.WordTrace tailWord_3057026 prefixEnd_3057026 1046482474194441070277333 := by
  unfold tailWord_3057026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27874724555731093829881733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74332598815282916879684621 27874724555731093829881733)
  ·
    refine ⟨5226510854199580093102825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27874724555731093829881733 5226510854199580093102825)
    ·
      refine ⟨3919883140649685069827119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5226510854199580093102825 3919883140649685069827119)
      ·
        refine ⟨5879824710974527604740679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919883140649685069827119 5879824710974527604740679)
        ·
          refine ⟨8819737066461791407111019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879824710974527604740679 8819737066461791407111019)
          ·
            refine ⟨13229605599692687110666529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819737066461791407111019 13229605599692687110666529)
            ·
              refine ⟨9922204199769515332999897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229605599692687110666529 9922204199769515332999897)
              ·
                refine ⟨7441653149827136499749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9922204199769515332999897 7441653149827136499749923)
                ·
                  refine ⟨11162479724740704749624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441653149827136499749923 11162479724740704749624885)
                  ·
                    refine ⟨1046482474194441070277333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162479724740704749624885 1046482474194441070277333)
                    ·
                      rfl

theorem cell22_3057026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3057026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057026 prefixEnd_3057026 := by exact prefixLift 3057026
  have htrace : WordTrace (prefixWord ++ tailWord_3057026) baseStart_3057026 baseEnd_3057026 := by
    simpa [prefixWord, tailWord_3057026, baseEnd_3057026] using wordTrace_append hprefix tailTrace_3057026
  have hstable : (prefixWord ++ tailWord_3057026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057026).length < 2 ^ (prefixWord ++ tailWord_3057026).sum := by decide
  have hdescent : baseEnd_3057026 < baseStart_3057026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057090 : List Nat := [3, 5, 2, 1, 1, 2, 8]
def baseStart_3057090 : Nat := 118140960795 + 3057090 * 2 ^ 59
def prefixEnd_3057090 : Nat := 4983230072969 + 3 ^ 40 * 3057090 * 2
def baseEnd_3057090 : Nat := 38759421581569119876931

theorem tailTrace_3057090 : CollatzResearch.WordTrace tailWord_3057090 prefixEnd_3057090 38759421581569119876931 := by
  unfold tailWord_3057090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27875308123673128562464181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74334154996461676166571149 27875308123673128562464181)
  ·
    refine ⟨2613310136594355802731017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27875308123673128562464181 2613310136594355802731017)
    ·
      refine ⟨1959982602445766852048263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613310136594355802731017 1959982602445766852048263)
      ·
        refine ⟨2939973903668650278072395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959982602445766852048263 2939973903668650278072395)
        ·
          refine ⟨4409960855502975417108593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939973903668650278072395 4409960855502975417108593)
          ·
            refine ⟨3307470641627231562831445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4409960855502975417108593 3307470641627231562831445)
            ·
              refine ⟨38759421581569119876931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3307470641627231562831445 38759421581569119876931)
              ·
                rfl

theorem cell22_3057090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 8].length) (baseStart_3057090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057090 prefixEnd_3057090 := by exact prefixLift 3057090
  have htrace : WordTrace (prefixWord ++ tailWord_3057090) baseStart_3057090 baseEnd_3057090 := by
    simpa [prefixWord, tailWord_3057090, baseEnd_3057090] using wordTrace_append hprefix tailTrace_3057090
  have hstable : (prefixWord ++ tailWord_3057090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057090).length < 2 ^ (prefixWord ++ tailWord_3057090).sum := by decide
  have hdescent : baseEnd_3057090 < baseStart_3057090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_3057097 : Nat := 118140960795 + 3057097 * 2 ^ 59
def prefixEnd_3057097 : Nat := 4983230072969 + 3 ^ 40 * 3057097 * 2
def baseEnd_3057097 : Nat := 1046506778945420551752115

theorem tailTrace_3057097 : CollatzResearch.WordTrace tailWord_3057097 prefixEnd_3057097 1046506778945420551752115 := by
  unfold tailWord_3057097
  simp only [CollatzResearch.WordTrace]
  refine ⟨111501487805667154445361545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74334325203778102963574363 111501487805667154445361545)
  ·
    refine ⟨83626115854250365834021159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111501487805667154445361545 83626115854250365834021159)
    ·
      refine ⟨125439173781375548751031739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83626115854250365834021159 125439173781375548751031739)
      ·
        refine ⟨188158760672063323126547609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125439173781375548751031739 188158760672063323126547609)
        ·
          refine ⟨141119070504047492344910707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188158760672063323126547609 141119070504047492344910707)
          ·
            refine ⟨211678605756071238517366061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141119070504047492344910707 211678605756071238517366061)
            ·
              refine ⟨79379477158526714444012273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211678605756071238517366061 79379477158526714444012273)
              ·
                refine ⟨59534607868895035833009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79379477158526714444012273 59534607868895035833009205)
                ·
                  refine ⟨5581369487708909609344613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59534607868895035833009205 5581369487708909609344613)
                  ·
                    refine ⟨1046506778945420551752115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581369487708909609344613 1046506778945420551752115)
                    ·
                      rfl

theorem cell22_3057097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_3057097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057097 prefixEnd_3057097 := by exact prefixLift 3057097
  have htrace : WordTrace (prefixWord ++ tailWord_3057097) baseStart_3057097 baseEnd_3057097 := by
    simpa [prefixWord, tailWord_3057097, baseEnd_3057097] using wordTrace_append hprefix tailTrace_3057097
  have hstable : (prefixWord ++ tailWord_3057097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057097).length < 2 ^ (prefixWord ++ tailWord_3057097).sum := by decide
  have hdescent : baseEnd_3057097 < baseStart_3057097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057144 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3057144 : Nat := 118140960795 + 3057144 * 2 ^ 59
def prefixEnd_3057144 : Nat := 4983230072969 + 3 ^ 40 * 3057144 * 2
def baseEnd_3057144 : Nat := 1046522868005928095826971

theorem tailTrace_3057144 : CollatzResearch.WordTrace tailWord_3057144 prefixEnd_3057144 1046522868005928095826971 := by
  unfold tailWord_3057144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55751601018248440736161243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74335468024331254314881657 55751601018248440736161243)
  ·
    refine ⟨83627401527372661104241865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55751601018248440736161243 83627401527372661104241865)
    ·
      refine ⟨62720551145529495828181399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83627401527372661104241865 62720551145529495828181399)
      ·
        refine ⟨94080826718294243742272099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62720551145529495828181399 94080826718294243742272099)
        ·
          refine ⟨141121240077441365613408149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94080826718294243742272099 141121240077441365613408149)
          ·
            refine ⟨6615058128630064013128507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141121240077441365613408149 6615058128630064013128507)
            ·
              refine ⟨9922587192945096019692761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615058128630064013128507 9922587192945096019692761)
              ·
                refine ⟨7441940394708822014769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9922587192945096019692761 7441940394708822014769571)
                ·
                  refine ⟨11162910592063233022154357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441940394708822014769571 11162910592063233022154357)
                  ·
                    refine ⟨1046522868005928095826971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162910592063233022154357 1046522868005928095826971)
                    ·
                      rfl

theorem cell22_3057144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3057144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057144 prefixEnd_3057144 := by exact prefixLift 3057144
  have htrace : WordTrace (prefixWord ++ tailWord_3057144) baseStart_3057144 baseEnd_3057144 := by
    simpa [prefixWord, tailWord_3057144, baseEnd_3057144] using wordTrace_append hprefix tailTrace_3057144
  have hstable : (prefixWord ++ tailWord_3057144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057144).length < 2 ^ (prefixWord ++ tailWord_3057144).sum := by decide
  have hdescent : baseEnd_3057144 < baseStart_3057144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057161 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_3057161 : Nat := 118140960795 + 3057161 * 2 ^ 59
def prefixEnd_3057161 : Nat := 4983230072969 + 3 ^ 40 * 3057161 * 2
def baseEnd_3057161 : Nat := 1046528687453345718151919

theorem tailTrace_3057161 : CollatzResearch.WordTrace tailWord_3057161 prefixEnd_3057161 1046528687453345718151919 := by
  unfold tailWord_3057161
  simp only [CollatzResearch.WordTrace]
  refine ⟨111503822077435293375691337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74335881384956862250460891 111503822077435293375691337)
  ·
    refine ⟨83627866558076470031768503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111503822077435293375691337 83627866558076470031768503)
    ·
      refine ⟨125441799837114705047652755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83627866558076470031768503 125441799837114705047652755)
      ·
        refine ⟨188162699755672057571479133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125441799837114705047652755 188162699755672057571479133)
        ·
          refine ⟨70561012408377021589304675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188162699755672057571479133 70561012408377021589304675)
          ·
            refine ⟨105841518612565532383957013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70561012408377021589304675 105841518612565532383957013)
            ·
              refine ⟨4961321184964009330497985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105841518612565532383957013 4961321184964009330497985)
              ·
                refine ⟨3720990888723006997873489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961321184964009330497985 3720990888723006997873489)
                ·
                  refine ⟨2790743166542255248405117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720990888723006997873489 2790743166542255248405117)
                  ·
                    refine ⟨1046528687453345718151919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790743166542255248405117 1046528687453345718151919)
                    ·
                      rfl

theorem cell22_3057161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_3057161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057161 prefixEnd_3057161 := by exact prefixLift 3057161
  have htrace : WordTrace (prefixWord ++ tailWord_3057161) baseStart_3057161 baseEnd_3057161 := by
    simpa [prefixWord, tailWord_3057161, baseEnd_3057161] using wordTrace_append hprefix tailTrace_3057161
  have hstable : (prefixWord ++ tailWord_3057161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057161).length < 2 ^ (prefixWord ++ tailWord_3057161).sum := by decide
  have hdescent : baseEnd_3057161 < baseStart_3057161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057223 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3057223 : Nat := 118140960795 + 3057223 * 2 ^ 59
def prefixEnd_3057223 : Nat := 4983230072969 + 3 ^ 40 * 3057223 * 2
def baseEnd_3057223 : Nat := 1046549911320398223101729

theorem tailTrace_3057223 : CollatzResearch.WordTrace tailWord_3057223 prefixEnd_3057223 1046549911320398223101729 := by
  unfold tailWord_3057223
  simp only [CollatzResearch.WordTrace]
  refine ⟨111506083403210677964448323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74337388935473785309632215 111506083403210677964448323)
  ·
    refine ⟨167259125104816016946672485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111506083403210677964448323 167259125104816016946672485)
    ·
      refine ⟨31361085957153003177501091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167259125104816016946672485 31361085957153003177501091)
      ·
        refine ⟨47041628935729504766251637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31361085957153003177501091 47041628935729504766251637)
        ·
          refine ⟨4410152712724641071836091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47041628935729504766251637 4410152712724641071836091)
          ·
            refine ⟨6615229069086961607754137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410152712724641071836091 6615229069086961607754137)
            ·
              refine ⟨4961421801815221205815603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615229069086961607754137 4961421801815221205815603)
              ·
                refine ⟨7442132702722831808723405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961421801815221205815603 7442132702722831808723405)
                ·
                  refine ⟨2790799763521061928271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7442132702722831808723405 2790799763521061928271277)
                  ·
                    refine ⟨1046549911320398223101729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790799763521061928271277 1046549911320398223101729)
                    ·
                      rfl

theorem cell22_3057223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3057223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057223 prefixEnd_3057223 := by exact prefixLift 3057223
  have htrace : WordTrace (prefixWord ++ tailWord_3057223) baseStart_3057223 baseEnd_3057223 := by
    simpa [prefixWord, tailWord_3057223, baseEnd_3057223] using wordTrace_append hprefix tailTrace_3057223
  have hstable : (prefixWord ++ tailWord_3057223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057223).length < 2 ^ (prefixWord ++ tailWord_3057223).sum := by decide
  have hdescent : baseEnd_3057223 < baseStart_3057223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057281 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 6]
def baseStart_3057281 : Nat := 118140960795 + 3057281 * 2 ^ 59
def prefixEnd_3057281 : Nat := 4983230072969 + 3 ^ 40 * 3057281 * 2
def baseEnd_3057281 : Nat := 348856588635235135050517

theorem tailTrace_3057281 : CollatzResearch.WordTrace tailWord_3057281 prefixEnd_3057281 348856588635235135050517 := by
  unfold tailWord_3057281
  simp only [CollatzResearch.WordTrace]
  refine ⟨111508198837000553870059697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74338799224667035913373131 111508198837000553870059697)
  ·
    refine ⟨83631149127750415402544773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111508198837000553870059697 83631149127750415402544773)
    ·
      refine ⟨15680840461453202887977145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83631149127750415402544773 15680840461453202887977145)
      ·
        refine ⟨11760630346089902165982859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15680840461453202887977145 11760630346089902165982859)
        ·
          refine ⟨17640945519134853248974289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11760630346089902165982859 17640945519134853248974289)
          ·
            refine ⟨13230709139351139936730717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17640945519134853248974289 13230709139351139936730717)
            ·
              refine ⟨4961515927256677476274019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13230709139351139936730717 4961515927256677476274019)
              ·
                refine ⟨7442273890885016214411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961515927256677476274019 7442273890885016214411029)
                ·
                  refine ⟨348856588635235135050517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7442273890885016214411029 348856588635235135050517)
                  ·
                    rfl

theorem cell22_3057281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_3057281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057281 prefixEnd_3057281 := by exact prefixLift 3057281
  have htrace : WordTrace (prefixWord ++ tailWord_3057281) baseStart_3057281 baseEnd_3057281 := by
    simpa [prefixWord, tailWord_3057281, baseEnd_3057281] using wordTrace_append hprefix tailTrace_3057281
  have hstable : (prefixWord ++ tailWord_3057281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057281).length < 2 ^ (prefixWord ++ tailWord_3057281).sum := by decide
  have hdescent : baseEnd_3057281 < baseStart_3057281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057326 : List Nat := [4, 1, 4, 1, 12]
def baseStart_3057326 : Nat := 118140960795 + 3057326 * 2 ^ 59
def prefixEnd_3057326 : Nat := 4983230072969 + 3 ^ 40 * 3057326 * 2
def baseEnd_3057326 : Nat := 4306934857305927110191

theorem tailTrace_3057326 : CollatzResearch.WordTrace tailWord_3057326 prefixEnd_3057326 4306934857305927110191 := by
  unfold tailWord_3057326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938730015229690819430979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74339893414558351036965221 13938730015229690819430979)
  ·
    refine ⟨20908095022844536229146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938730015229690819430979 20908095022844536229146469)
    ·
      refine ⟨3920267816783350542964963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20908095022844536229146469 3920267816783350542964963)
      ·
        refine ⟨5880401725175025814447445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920267816783350542964963 5880401725175025814447445)
        ·
          refine ⟨4306934857305927110191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5880401725175025814447445 4306934857305927110191)
          ·
            rfl

theorem cell22_3057326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 12].length) (baseStart_3057326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057326 prefixEnd_3057326 := by exact prefixLift 3057326
  have htrace : WordTrace (prefixWord ++ tailWord_3057326) baseStart_3057326 baseEnd_3057326 := by
    simpa [prefixWord, tailWord_3057326, baseEnd_3057326] using wordTrace_append hprefix tailTrace_3057326
  have hstable : (prefixWord ++ tailWord_3057326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057326).length < 2 ^ (prefixWord ++ tailWord_3057326).sum := by decide
  have hdescent : baseEnd_3057326 < baseStart_3057326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057358 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3057358 : Nat := 118140960795 + 3057358 * 2 ^ 59
def prefixEnd_3057358 : Nat := 4983230072969 + 3 ^ 40 * 3057358 * 2
def baseEnd_3057358 : Nat := 1046596124579302870976315

theorem tailTrace_3057358 : CollatzResearch.WordTrace tailWord_3057358 prefixEnd_3057358 1046596124579302870976315 := by
  unfold tailWord_3057358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938875907215199502576591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74340671505147730680408485 13938875907215199502576591)
  ·
    refine ⟨20908313860822799253864887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938875907215199502576591 20908313860822799253864887)
    ·
      refine ⟨31362470791234198880797331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20908313860822799253864887 31362470791234198880797331)
      ·
        refine ⟨47043706186851298321195997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31362470791234198880797331 47043706186851298321195997)
        ·
          refine ⟨17641389820069236870448499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47043706186851298321195997 17641389820069236870448499)
          ·
            refine ⟨26462084730103855305672749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17641389820069236870448499 26462084730103855305672749)
            ·
              refine ⟨9923281773788945739627281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26462084730103855305672749 9923281773788945739627281)
              ·
                refine ⟨7442461330341709304720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9923281773788945739627281 7442461330341709304720461)
                ·
                  refine ⟨2790922998878140989270173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7442461330341709304720461 2790922998878140989270173)
                  ·
                    refine ⟨1046596124579302870976315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790922998878140989270173 1046596124579302870976315)
                    ·
                      rfl

theorem cell22_3057358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3057358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057358 prefixEnd_3057358 := by exact prefixLift 3057358
  have htrace : WordTrace (prefixWord ++ tailWord_3057358) baseStart_3057358 baseEnd_3057358 := by
    simpa [prefixWord, tailWord_3057358, baseEnd_3057358] using wordTrace_append hprefix tailTrace_3057358
  have hstable : (prefixWord ++ tailWord_3057358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057358).length < 2 ^ (prefixWord ++ tailWord_3057358).sum := by decide
  have hdescent : baseEnd_3057358 < baseStart_3057358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057375 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 1, 3]
def baseStart_3057375 : Nat := 118140960795 + 3057375 * 2 ^ 59
def prefixEnd_3057375 : Nat := 4983230072969 + 3 ^ 40 * 3057375 * 2
def baseEnd_3057375 : Nat := 1046601944026720493301263

theorem tailTrace_3057375 : CollatzResearch.WordTrace tailWord_3057375 prefixEnd_3057375 1046601944026720493301263 := by
  unfold tailWord_3057375
  simp only [CollatzResearch.WordTrace]
  refine ⟨111511627298660007923981579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74341084865773338615987719 111511627298660007923981579)
  ·
    refine ⟨167267440947990011885972369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111511627298660007923981579 167267440947990011885972369)
    ·
      refine ⟨125450580710992508914479277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167267440947990011885972369 125450580710992508914479277)
      ·
        refine ⟨47043967766622190842929729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125450580710992508914479277 47043967766622190842929729)
        ·
          refine ⟨35282975824966643132197297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47043967766622190842929729 35282975824966643132197297)
          ·
            refine ⟨26462231868724982349147973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35282975824966643132197297 26462231868724982349147973)
            ·
              refine ⟨4961668475385934190465245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26462231868724982349147973 4961668475385934190465245)
              ·
                refine ⟨1860625678269725321424467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4961668475385934190465245 1860625678269725321424467)
                ·
                  refine ⟨2790938517404587982136701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860625678269725321424467 2790938517404587982136701)
                  ·
                    refine ⟨1046601944026720493301263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790938517404587982136701 1046601944026720493301263)
                    ·
                      rfl

theorem cell22_3057375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_3057375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057375 prefixEnd_3057375 := by exact prefixLift 3057375
  have htrace : WordTrace (prefixWord ++ tailWord_3057375) baseStart_3057375 baseEnd_3057375 := by
    simpa [prefixWord, tailWord_3057375, baseEnd_3057375] using wordTrace_append hprefix tailTrace_3057375
  have hstable : (prefixWord ++ tailWord_3057375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057375).length < 2 ^ (prefixWord ++ tailWord_3057375).sum := by decide
  have hdescent : baseEnd_3057375 < baseStart_3057375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057386 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3057386 : Nat := 118140960795 + 3057386 * 2 ^ 59
def prefixEnd_3057386 : Nat := 4983230072969 + 3 ^ 40 * 3057386 * 2
def baseEnd_3057386 : Nat := 1046605709551520131276229

theorem tailTrace_3057386 : CollatzResearch.WordTrace tailWord_3057386 prefixEnd_3057386 1046605709551520131276229 := by
  unfold tailWord_3057386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27878007125405039200658003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74341352334413437868421341 27878007125405039200658003)
  ·
    refine ⟨41817010688107558800987005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27878007125405039200658003 41817010688107558800987005)
    ·
      refine ⟨15681379008040334550370127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41817010688107558800987005 15681379008040334550370127)
      ·
        refine ⟨23522068512060501825555191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15681379008040334550370127 23522068512060501825555191)
        ·
          refine ⟨35283102768090752738332787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23522068512060501825555191 35283102768090752738332787)
          ·
            refine ⟨52924654152136129107499181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35283102768090752738332787 52924654152136129107499181)
            ·
              refine ⟨19846745307051048415312193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52924654152136129107499181 19846745307051048415312193)
              ·
                refine ⟨14885058980288286311484145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19846745307051048415312193 14885058980288286311484145)
                ·
                  refine ⟨11163794235216214733613109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14885058980288286311484145 11163794235216214733613109)
                  ·
                    refine ⟨1046605709551520131276229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11163794235216214733613109 1046605709551520131276229)
                    ·
                      rfl

theorem cell22_3057386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3057386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057386 prefixEnd_3057386 := by exact prefixLift 3057386
  have htrace : WordTrace (prefixWord ++ tailWord_3057386) baseStart_3057386 baseEnd_3057386 := by
    simpa [prefixWord, tailWord_3057386, baseEnd_3057386] using wordTrace_append hprefix tailTrace_3057386
  have hstable : (prefixWord ++ tailWord_3057386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057386).length < 2 ^ (prefixWord ++ tailWord_3057386).sum := by decide
  have hdescent : baseEnd_3057386 < baseStart_3057386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057416 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_3057416 : Nat := 118140960795 + 3057416 * 2 ^ 59
def prefixEnd_3057416 : Nat := 4983230072969 + 3 ^ 40 * 3057416 * 2
def baseEnd_3057416 : Nat := 348871993054870017675379

theorem tailTrace_3057416 : CollatzResearch.WordTrace tailWord_3057416 prefixEnd_3057416 348871993054870017675379 := by
  unfold tailWord_3057416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55756561345755735963112051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74342081794340981284149401 55756561345755735963112051)
  ·
    refine ⟨83634842018633603944668077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55756561345755735963112051 83634842018633603944668077)
    ·
      refine ⟨31363065756987601479250529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83634842018633603944668077 31363065756987601479250529)
      ·
        refine ⟨23522299317740701109437897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31363065756987601479250529 23522299317740701109437897)
        ·
          refine ⟨17641724488305525832078423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23522299317740701109437897 17641724488305525832078423)
          ·
            refine ⟨26462586732458288748117635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17641724488305525832078423 26462586732458288748117635)
            ·
              refine ⟨39693880098687433122176453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26462586732458288748117635 39693880098687433122176453)
              ·
                refine ⟨7442602518503893710408085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39693880098687433122176453 7442602518503893710408085)
                ·
                  refine ⟨348871993054870017675379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7442602518503893710408085 348871993054870017675379)
                  ·
                    rfl

theorem cell22_3057416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_3057416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057416 prefixEnd_3057416 := by exact prefixLift 3057416
  have htrace : WordTrace (prefixWord ++ tailWord_3057416) baseStart_3057416 baseEnd_3057416 := by
    simpa [prefixWord, tailWord_3057416, baseEnd_3057416] using wordTrace_append hprefix tailTrace_3057416
  have hstable : (prefixWord ++ tailWord_3057416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057416).length < 2 ^ (prefixWord ++ tailWord_3057416).sum := by decide
  have hdescent : baseEnd_3057416 < baseStart_3057416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057418 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_3057418 : Nat := 118140960795 + 3057418 * 2 ^ 59
def prefixEnd_3057418 : Nat := 4983230072969 + 3 ^ 40 * 3057418 * 2
def baseEnd_3057418 : Nat := 1046616663805482714476131

theorem tailTrace_3057418 : CollatzResearch.WordTrace tailWord_3057418 prefixEnd_3057418 1046616663805482714476131 := by
  unfold tailWord_3057418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27878298909376056566949227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74342130425002817511864605 27878298909376056566949227)
  ·
    refine ⟨41817448364064084850423841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27878298909376056566949227 41817448364064084850423841)
    ·
      refine ⟨31363086273048063637817881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41817448364064084850423841 31363086273048063637817881)
      ·
        refine ⟨23522314704786047728363411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31363086273048063637817881 23522314704786047728363411)
        ·
          refine ⟨35283472057179071592545117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23522314704786047728363411 35283472057179071592545117)
          ·
            refine ⟨13231302021442151847204419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35283472057179071592545117 13231302021442151847204419)
            ·
              refine ⟨19846953032163227770806629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231302021442151847204419 19846953032163227770806629)
              ·
                refine ⟨3721303693530605207026243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19846953032163227770806629 3721303693530605207026243)
                ·
                  refine ⟨5581955540295907810539365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721303693530605207026243 5581955540295907810539365)
                  ·
                    refine ⟨1046616663805482714476131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581955540295907810539365 1046616663805482714476131)
                    ·
                      rfl

theorem cell22_3057418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_3057418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057418 prefixEnd_3057418 := by exact prefixLift 3057418
  have htrace : WordTrace (prefixWord ++ tailWord_3057418) baseStart_3057418 baseEnd_3057418 := by
    simpa [prefixWord, tailWord_3057418, baseEnd_3057418] using wordTrace_append hprefix tailTrace_3057418
  have hstable : (prefixWord ++ tailWord_3057418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057418).length < 2 ^ (prefixWord ++ tailWord_3057418).sum := by decide
  have hdescent : baseEnd_3057418 < baseStart_3057418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057544 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3057544 : Nat := 118140960795 + 3057544 * 2 ^ 59
def prefixEnd_3057544 : Nat := 4983230072969 + 3 ^ 40 * 3057544 * 2
def baseEnd_3057544 : Nat := 1046659796180460385825745

theorem tailTrace_3057544 : CollatzResearch.WordTrace tailWord_3057544 prefixEnd_3057544 1046659796180460385825745 := by
  unfold tailWord_3057544
  simp only [CollatzResearch.WordTrace]
  refine ⟨55758895617523874893441843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74345194156698499857922457 55758895617523874893441843)
  ·
    refine ⟨83638343426285812340162765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55758895617523874893441843 83638343426285812340162765)
    ·
      refine ⟨31364378784857179627561037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83638343426285812340162765 31364378784857179627561037)
      ·
        refine ⟨11761642044321442360335389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31364378784857179627561037 11761642044321442360335389)
        ·
          refine ⟨4410615766620540885125771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11761642044321442360335389 4410615766620540885125771)
          ·
            refine ⟨6615923649930811327688657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410615766620540885125771 6615923649930811327688657)
            ·
              refine ⟨4961942737448108495766493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615923649930811327688657 4961942737448108495766493)
              ·
                refine ⟨1860728526543040685912435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4961942737448108495766493 1860728526543040685912435)
                ·
                  refine ⟨2791092789814561028868653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860728526543040685912435 2791092789814561028868653)
                  ·
                    refine ⟨1046659796180460385825745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2791092789814561028868653 1046659796180460385825745)
                    ·
                      rfl

theorem cell22_3057544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3057544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057544 prefixEnd_3057544 := by exact prefixLift 3057544
  have htrace : WordTrace (prefixWord ++ tailWord_3057544) baseStart_3057544 baseEnd_3057544 := by
    simpa [prefixWord, tailWord_3057544, baseEnd_3057544] using wordTrace_append hprefix tailTrace_3057544
  have hstable : (prefixWord ++ tailWord_3057544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057544).length < 2 ^ (prefixWord ++ tailWord_3057544).sum := by decide
  have hdescent : baseEnd_3057544 < baseStart_3057544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057675 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 5]
def baseStart_3057675 : Nat := 118140960795 + 3057675 * 2 ^ 59
def prefixEnd_3057675 : Nat := 4983230072969 + 3 ^ 40 * 3057675 * 2
def baseEnd_3057675 : Nat := 348901546719206570266781

theorem tailTrace_3057675 : CollatzResearch.WordTrace tailWord_3057675 prefixEnd_3057675 348901546719206570266781 := by
  unfold tailWord_3057675
  simp only [CollatzResearch.WordTrace]
  refine ⟨111522569197573159159902479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74348379465048772773268319 111522569197573159159902479)
  ·
    refine ⟨167283853796359738739853719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111522569197573159159902479 167283853796359738739853719)
    ·
      refine ⟨250925780694539608109780579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167283853796359738739853719 250925780694539608109780579)
      ·
        refine ⟨376388671041809412164670869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250925780694539608109780579 376388671041809412164670869)
        ·
          refine ⟨17643218955084816195218947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 376388671041809412164670869 17643218955084816195218947)
          ·
            refine ⟨26464828432627224292828421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643218955084816195218947 26464828432627224292828421)
            ·
              refine ⟨4962155331117604554905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26464828432627224292828421 4962155331117604554905329)
              ·
                refine ⟨3721616498338203416178997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962155331117604554905329 3721616498338203416178997)
                ·
                  refine ⟨348901546719206570266781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3721616498338203416178997 348901546719206570266781)
                  ·
                    rfl

theorem cell22_3057675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 5].length) (baseStart_3057675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057675 prefixEnd_3057675 := by exact prefixLift 3057675
  have htrace : WordTrace (prefixWord ++ tailWord_3057675) baseStart_3057675 baseEnd_3057675 := by
    simpa [prefixWord, tailWord_3057675, baseEnd_3057675] using wordTrace_append hprefix tailTrace_3057675
  have hstable : (prefixWord ++ tailWord_3057675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057675).length < 2 ^ (prefixWord ++ tailWord_3057675).sum := by decide
  have hdescent : baseEnd_3057675 < baseStart_3057675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057690 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_3057690 : Nat := 118140960795 + 3057690 * 2 ^ 59
def prefixEnd_3057690 : Nat := 4983230072969 + 3 ^ 40 * 3057690 * 2
def baseEnd_3057690 : Nat := 1046709774964164671675297

theorem tailTrace_3057690 : CollatzResearch.WordTrace tailWord_3057690 prefixEnd_3057690 1046709774964164671675297 := by
  unfold tailWord_3057690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27880779073129704180424631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74348744195012544481132349 27880779073129704180424631)
  ·
    refine ⟨41821168609694556270636947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27880779073129704180424631 41821168609694556270636947)
    ·
      refine ⟨62731752914541834405955421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41821168609694556270636947 62731752914541834405955421)
      ·
        refine ⟨23524407342953187902233283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62731752914541834405955421 23524407342953187902233283)
        ·
          refine ⟨35286611014429781853349925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23524407342953187902233283 35286611014429781853349925)
          ·
            refine ⟨6616239565205584097503111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35286611014429781853349925 6616239565205584097503111)
            ·
              refine ⟨9924359347808376146254667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616239565205584097503111 9924359347808376146254667)
              ·
                refine ⟨14886539021712564219382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9924359347808376146254667 14886539021712564219382001)
                ·
                  refine ⟨11164904266284423164536501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14886539021712564219382001 11164904266284423164536501)
                  ·
                    refine ⟨1046709774964164671675297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11164904266284423164536501 1046709774964164671675297)
                    ·
                      rfl

theorem cell22_3057690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_3057690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057690 prefixEnd_3057690 := by exact prefixLift 3057690
  have htrace : WordTrace (prefixWord ++ tailWord_3057690) baseStart_3057690 baseEnd_3057690 := by
    simpa [prefixWord, tailWord_3057690, baseEnd_3057690] using wordTrace_append hprefix tailTrace_3057690
  have hstable : (prefixWord ++ tailWord_3057690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057690).length < 2 ^ (prefixWord ++ tailWord_3057690).sum := by decide
  have hdescent : baseEnd_3057690 < baseStart_3057690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057726 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_3057726 : Nat := 118140960795 + 3057726 * 2 ^ 59
def prefixEnd_3057726 : Nat := 4983230072969 + 3 ^ 40 * 3057726 * 2
def baseEnd_3057726 : Nat := 348907366166624192591729

theorem tailTrace_3057726 : CollatzResearch.WordTrace tailWord_3057726 prefixEnd_3057726 348907366166624192591729 := by
  unfold tailWord_3057726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940553665048549358751129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74349619546925596580006021 13940553665048549358751129)
  ·
    refine ⟨10455415248786412019063347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13940553665048549358751129 10455415248786412019063347)
    ·
      refine ⟨15683122873179618028595021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10455415248786412019063347 15683122873179618028595021)
      ·
        refine ⟨5881171077442356760723133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15683122873179618028595021 5881171077442356760723133)
        ·
          refine ⟨2205439154040883785271175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5881171077442356760723133 2205439154040883785271175)
          ·
            refine ⟨3308158731061325677906763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205439154040883785271175 3308158731061325677906763)
            ·
              refine ⟨4962238096591988516860145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308158731061325677906763 4962238096591988516860145)
              ·
                refine ⟨3721678572443991387645109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962238096591988516860145 3721678572443991387645109)
                ·
                  refine ⟨348907366166624192591729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3721678572443991387645109 348907366166624192591729)
                  ·
                    rfl

theorem cell22_3057726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_3057726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057726 prefixEnd_3057726 := by exact prefixLift 3057726
  have htrace : WordTrace (prefixWord ++ tailWord_3057726) baseStart_3057726 baseEnd_3057726 := by
    simpa [prefixWord, tailWord_3057726, baseEnd_3057726] using wordTrace_append hprefix tailTrace_3057726
  have hstable : (prefixWord ++ tailWord_3057726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057726).length < 2 ^ (prefixWord ++ tailWord_3057726).sum := by decide
  have hdescent : baseEnd_3057726 < baseStart_3057726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057752 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_3057752 : Nat := 118140960795 + 3057752 * 2 ^ 59
def prefixEnd_3057752 : Nat := 4983230072969 + 3 ^ 40 * 3057752 * 2
def baseEnd_3057752 : Nat := 1046730998831217176625107

theorem tailTrace_3057752 : CollatzResearch.WordTrace tailWord_3057752 prefixEnd_3057752 1046730998831217176625107 := by
  unfold tailWord_3057752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55762688809147100655227755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74350251745529467540303673 55762688809147100655227755)
  ·
    refine ⟨83644033213720650982841633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55762688809147100655227755 83644033213720650982841633)
    ·
      refine ⟨62733024910290488237131225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83644033213720650982841633 62733024910290488237131225)
      ·
        refine ⟨47049768682717866177848419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62733024910290488237131225 47049768682717866177848419)
        ·
          refine ⟨70574653024076799266772629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47049768682717866177848419 70574653024076799266772629)
          ·
            refine ⟨3308186860503599965629967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70574653024076799266772629 3308186860503599965629967)
            ·
              refine ⟨4962280290755399948444951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308186860503599965629967 4962280290755399948444951)
              ·
                refine ⟨7443420436133099922667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962280290755399948444951 7443420436133099922667427)
                ·
                  refine ⟨11165130654199649884001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443420436133099922667427 11165130654199649884001141)
                  ·
                    refine ⟨1046730998831217176625107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11165130654199649884001141 1046730998831217176625107)
                    ·
                      rfl

theorem cell22_3057752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_3057752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057752 prefixEnd_3057752 := by exact prefixLift 3057752
  have htrace : WordTrace (prefixWord ++ tailWord_3057752) baseStart_3057752 baseEnd_3057752 := by
    simpa [prefixWord, tailWord_3057752, baseEnd_3057752] using wordTrace_append hprefix tailTrace_3057752
  have hstable : (prefixWord ++ tailWord_3057752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057752).length < 2 ^ (prefixWord ++ tailWord_3057752).sum := by decide
  have hdescent : baseEnd_3057752 < baseStart_3057752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057765 : List Nat := [1, 3, 1, 3, 2, 3, 1, 8]
def baseStart_3057765 : Nat := 118140960795 + 3057765 * 2 ^ 59
def prefixEnd_3057765 : Nat := 4983230072969 + 3 ^ 40 * 3057765 * 2
def baseEnd_3057765 : Nat := 116303938777432164005563

theorem tailTrace_3057765 : CollatzResearch.WordTrace tailWord_3057765 prefixEnd_3057765 116303938777432164005563 := by
  unfold tailWord_3057765
  simp only [CollatzResearch.WordTrace]
  refine ⟨111525851767247104530678749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74350567844831403020452499 111525851767247104530678749)
  ·
    refine ⟨41822194412717664199004531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111525851767247104530678749 41822194412717664199004531)
    ·
      refine ⟨62733291619076496298506797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41822194412717664199004531 62733291619076496298506797)
      ·
        refine ⟨23524984357153686111940049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62733291619076496298506797 23524984357153686111940049)
        ·
          refine ⟨17643738267865264583955037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23524984357153686111940049 17643738267865264583955037)
          ·
            refine ⟨6616401850449474218983139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17643738267865264583955037 6616401850449474218983139)
            ·
              refine ⟨9924602775674211328474709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616401850449474218983139 9924602775674211328474709)
              ·
                refine ⟨116303938777432164005563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9924602775674211328474709 116303938777432164005563)
                ·
                  rfl

theorem cell22_3057765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 8].length) (baseStart_3057765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057765 prefixEnd_3057765 := by exact prefixLift 3057765
  have htrace : WordTrace (prefixWord ++ tailWord_3057765) baseStart_3057765 baseEnd_3057765 := by
    simpa [prefixWord, tailWord_3057765, baseEnd_3057765] using wordTrace_append hprefix tailTrace_3057765
  have hstable : (prefixWord ++ tailWord_3057765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057765).length < 2 ^ (prefixWord ++ tailWord_3057765).sum := by decide
  have hdescent : baseEnd_3057765 < baseStart_3057765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057782 : List Nat := [5, 1, 1, 2, 1, 4, 8]
def baseStart_3057782 : Nat := 118140960795 + 3057782 * 2 ^ 59
def prefixEnd_3057782 : Nat := 4983230072969 + 3 ^ 40 * 3057782 * 2
def baseEnd_3057782 : Nat := 38768195127566929569445

theorem tailTrace_3057782 : CollatzResearch.WordTrace tailWord_3057782 prefixEnd_3057782 38768195127566929569445 := by
  unfold tailWord_3057782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970404488011594777127975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74350981205457010956031733 6970404488011594777127975)
  ·
    refine ⟨10455606732017392165691963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970404488011594777127975 10455606732017392165691963)
    ·
      refine ⟨15683410098026088248537945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10455606732017392165691963 15683410098026088248537945)
      ·
        refine ⟨11762557573519566186403459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15683410098026088248537945 11762557573519566186403459)
        ·
          refine ⟨17643836360279349279605189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762557573519566186403459 17643836360279349279605189)
          ·
            refine ⟨3308219317552377989925973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17643836360279349279605189 3308219317552377989925973)
            ·
              refine ⟨38768195127566929569445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3308219317552377989925973 38768195127566929569445)
              ·
                rfl

theorem cell22_3057782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 8].length) (baseStart_3057782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057782 prefixEnd_3057782 := by exact prefixLift 3057782
  have htrace : WordTrace (prefixWord ++ tailWord_3057782) baseStart_3057782 baseEnd_3057782 := by
    simpa [prefixWord, tailWord_3057782, baseEnd_3057782] using wordTrace_append hprefix tailTrace_3057782
  have hstable : (prefixWord ++ tailWord_3057782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057782).length < 2 ^ (prefixWord ++ tailWord_3057782).sum := by decide
  have hdescent : baseEnd_3057782 < baseStart_3057782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_3057840 : Nat := 118140960795 + 3057840 * 2 ^ 59
def prefixEnd_3057840 : Nat := 4983230072969 + 3 ^ 40 * 3057840 * 2
def baseEnd_3057840 : Nat := 1046761123029614280424837

theorem tailTrace_3057840 : CollatzResearch.WordTrace tailWord_3057840 prefixEnd_3057840 1046761123029614280424837 := by
  unfold tailWord_3057840
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764293620987696169829487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74352391494650261559772649 55764293620987696169829487)
  ·
    refine ⟨83646440431481544254744231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55764293620987696169829487 83646440431481544254744231)
    ·
      refine ⟨125469660647222316382116347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83646440431481544254744231 125469660647222316382116347)
      ·
        refine ⟨188204490970833474573174521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125469660647222316382116347 188204490970833474573174521)
        ·
          refine ⟨141153368228125105929880891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188204490970833474573174521 141153368228125105929880891)
          ·
            refine ⟨211730052342187658894821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141153368228125105929880891 211730052342187658894821337)
            ·
              refine ⟨158797539256640744171116003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211730052342187658894821337 158797539256640744171116003)
              ·
                refine ⟨238196308884961116256674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158797539256640744171116003 238196308884961116256674005)
                ·
                  refine ⟨5582725989491276162265797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 238196308884961116256674005 5582725989491276162265797)
                  ·
                    refine ⟨1046761123029614280424837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582725989491276162265797 1046761123029614280424837)
                    ·
                      rfl

theorem cell22_3057840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_3057840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057840 prefixEnd_3057840 := by exact prefixLift 3057840
  have htrace : WordTrace (prefixWord ++ tailWord_3057840) baseStart_3057840 baseEnd_3057840 := by
    simpa [prefixWord, tailWord_3057840, baseEnd_3057840] using wordTrace_append hprefix tailTrace_3057840
  have hstable : (prefixWord ++ tailWord_3057840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057840).length < 2 ^ (prefixWord ++ tailWord_3057840).sum := by decide
  have hdescent : baseEnd_3057840 < baseStart_3057840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057855 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 6]
def baseStart_3057855 : Nat := 118140960795 + 3057855 * 2 ^ 59
def prefixEnd_3057855 : Nat := 4983230072969 + 3 ^ 40 * 3057855 * 2
def baseEnd_3057855 : Nat := 348922085945386413766597

theorem tailTrace_3057855 : CollatzResearch.WordTrace tailWord_3057855 prefixEnd_3057855 348922085945386413766597 := by
  unfold tailWord_3057855
  simp only [CollatzResearch.WordTrace]
  refine ⟨111529134336921049901455019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74352756224614033267636679 111529134336921049901455019)
  ·
    refine ⟨167293701505381574852182529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111529134336921049901455019 167293701505381574852182529)
    ·
      refine ⟨125470276129036181139136897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167293701505381574852182529 125470276129036181139136897)
      ·
        refine ⟨94102707096777135854352673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125470276129036181139136897 94102707096777135854352673)
        ·
          refine ⟨70577030322582851890764505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94102707096777135854352673 70577030322582851890764505)
          ·
            refine ⟨52932772741937138918073379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70577030322582851890764505 52932772741937138918073379)
            ·
              refine ⟨79399159112905708377110069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52932772741937138918073379 79399159112905708377110069)
              ·
                refine ⟨7443671166834910160354069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79399159112905708377110069 7443671166834910160354069)
                ·
                  refine ⟨348922085945386413766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7443671166834910160354069 348922085945386413766597)
                  ·
                    rfl

theorem cell22_3057855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_3057855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057855 prefixEnd_3057855 := by exact prefixLift 3057855
  have htrace : WordTrace (prefixWord ++ tailWord_3057855) baseStart_3057855 baseEnd_3057855 := by
    simpa [prefixWord, tailWord_3057855, baseEnd_3057855] using wordTrace_append hprefix tailTrace_3057855
  have hstable : (prefixWord ++ tailWord_3057855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057855).length < 2 ^ (prefixWord ++ tailWord_3057855).sum := by decide
  have hdescent : baseEnd_3057855 < baseStart_3057855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057887 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 4, 3]
def baseStart_3057887 : Nat := 118140960795 + 3057887 * 2 ^ 59
def prefixEnd_3057887 : Nat := 4983230072969 + 3 ^ 40 * 3057887 * 2
def baseEnd_3057887 : Nat := 1046777212090121824499693

theorem tailTrace_3057887 : CollatzResearch.WordTrace tailWord_3057887 prefixEnd_3057887 1046777212090121824499693 := by
  unfold tailWord_3057887
  simp only [CollatzResearch.WordTrace]
  refine ⟨111530301472805119366619915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74353534315203412911079943 111530301472805119366619915)
  ·
    refine ⟨167295452209207679049929873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111530301472805119366619915 167295452209207679049929873)
    ·
      refine ⟨125471589156905759287447405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167295452209207679049929873 125471589156905759287447405)
      ·
        refine ⟨47051845933839659732792777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125471589156905759287447405 47051845933839659732792777)
        ·
          refine ⟨35288884450379744799594583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47051845933839659732792777 35288884450379744799594583)
          ·
            refine ⟨52933326675569617199391875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35288884450379744799594583 52933326675569617199391875)
            ·
              refine ⟨79399990013354425799087813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52933326675569617199391875 79399990013354425799087813)
              ·
                refine ⟨14887498127503954837328965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79399990013354425799087813 14887498127503954837328965)
                ·
                  refine ⟨2791405898906991531999181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14887498127503954837328965 2791405898906991531999181)
                  ·
                    refine ⟨1046777212090121824499693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2791405898906991531999181 1046777212090121824499693)
                    ·
                      rfl

theorem cell22_3057887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_3057887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057887 prefixEnd_3057887 := by exact prefixLift 3057887
  have htrace : WordTrace (prefixWord ++ tailWord_3057887) baseStart_3057887 baseEnd_3057887 := by
    simpa [prefixWord, tailWord_3057887, baseEnd_3057887] using wordTrace_append hprefix tailTrace_3057887
  have hstable : (prefixWord ++ tailWord_3057887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057887).length < 2 ^ (prefixWord ++ tailWord_3057887).sum := by decide
  have hdescent : baseEnd_3057887 < baseStart_3057887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057889 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 4]
def baseStart_3057889 : Nat := 118140960795 + 3057889 * 2 ^ 59
def prefixEnd_3057889 : Nat := 4983230072969 + 3 ^ 40 * 3057889 * 2
def baseEnd_3057889 : Nat := 348925965576998161983229

theorem tailTrace_3057889 : CollatzResearch.WordTrace tailWord_3057889 prefixEnd_3057889 348925965576998161983229 := by
  unfold tailWord_3057889
  simp only [CollatzResearch.WordTrace]
  refine ⟨111530374418797873708192721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74353582945865249138795147 111530374418797873708192721)
  ·
    refine ⟨83647780814098405281144541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111530374418797873708192721 83647780814098405281144541)
    ·
      refine ⟨31367917805286901980429203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83647780814098405281144541 31367917805286901980429203)
      ·
        refine ⟨47051876707930352970643805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31367917805286901980429203 47051876707930352970643805)
        ·
          refine ⟨17644453765473882363991427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47051876707930352970643805 17644453765473882363991427)
          ·
            refine ⟨26466680648210823545987141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17644453765473882363991427 26466680648210823545987141)
            ·
              refine ⟨4962502621539529414872589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26466680648210823545987141 4962502621539529414872589)
              ·
                refine ⟨1860938483077323530577221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4962502621539529414872589 1860938483077323530577221)
                ·
                  refine ⟨348925965576998161983229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860938483077323530577221 348925965576998161983229)
                  ·
                    rfl

theorem cell22_3057889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_3057889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057889 prefixEnd_3057889 := by exact prefixLift 3057889
  have htrace : WordTrace (prefixWord ++ tailWord_3057889) baseStart_3057889 baseEnd_3057889 := by
    simpa [prefixWord, tailWord_3057889, baseEnd_3057889] using wordTrace_append hprefix tailTrace_3057889
  have hstable : (prefixWord ++ tailWord_3057889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057889).length < 2 ^ (prefixWord ++ tailWord_3057889).sum := by decide
  have hdescent : baseEnd_3057889 < baseStart_3057889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057891 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 1, 4]
def baseStart_3057891 : Nat := 118140960795 + 3057891 * 2 ^ 59
def prefixEnd_3057891 : Nat := 4983230072969 + 3 ^ 40 * 3057891 * 2
def baseEnd_3057891 : Nat := 1046778581371867147399681

theorem tailTrace_3057891 : CollatzResearch.WordTrace tailWord_3057891 prefixEnd_3057891 1046778581371867147399681 := by
  unfold tailWord_3057891
  simp only [CollatzResearch.WordTrace]
  refine ⟨111530447364790628049765527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74353631576527085366510351 111530447364790628049765527)
  ·
    refine ⟨167295671047185942074648291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111530447364790628049765527 167295671047185942074648291)
    ·
      refine ⟨250943506570778913111972437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167295671047185942074648291 250943506570778913111972437)
      ·
        refine ⟨2940744217626315388030927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 250943506570778913111972437 2940744217626315388030927)
        ·
          refine ⟨4411116326439473082046391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940744217626315388030927 4411116326439473082046391)
          ·
            refine ⟨6616674489659209623069587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411116326439473082046391 6616674489659209623069587)
            ·
              refine ⟨9925011734488814434604381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616674489659209623069587 9925011734488814434604381)
              ·
                refine ⟨3721879400433305412976643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9925011734488814434604381 3721879400433305412976643)
                ·
                  refine ⟨5582819100649958119464965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721879400433305412976643 5582819100649958119464965)
                  ·
                    refine ⟨1046778581371867147399681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582819100649958119464965 1046778581371867147399681)
                    ·
                      rfl

theorem cell22_3057891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].length) (baseStart_3057891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057891 prefixEnd_3057891 := by exact prefixLift 3057891
  have htrace : WordTrace (prefixWord ++ tailWord_3057891) baseStart_3057891 baseEnd_3057891 := by
    simpa [prefixWord, tailWord_3057891, baseEnd_3057891] using wordTrace_append hprefix tailTrace_3057891
  have hstable : (prefixWord ++ tailWord_3057891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057891).length < 2 ^ (prefixWord ++ tailWord_3057891).sum := by decide
  have hdescent : baseEnd_3057891 < baseStart_3057891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057900 : List Nat := [2, 2, 1, 1, 2, 3, 11]
def baseStart_3057900 : Nat := 118140960795 + 3057900 * 2 ^ 59
def prefixEnd_3057900 : Nat := 4983230072969 + 3 ^ 40 * 3057900 * 2
def baseEnd_3057900 : Nat := 38769691194659041626839

theorem tailTrace_3057900 : CollatzResearch.WordTrace tailWord_3057900 prefixEnd_3057900 38769691194659041626839 := by
  unfold tailWord_3057900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55765387810879011293421577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74353850414505348391228769 55765387810879011293421577)
  ·
    refine ⟨41824040858159258470066183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55765387810879011293421577 41824040858159258470066183)
    ·
      refine ⟨62736061287238887705099275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41824040858159258470066183 62736061287238887705099275)
      ·
        refine ⟨94104091930858331557648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62736061287238887705099275 94104091930858331557648913)
        ·
          refine ⟨70578068948143748668236685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94104091930858331557648913 70578068948143748668236685)
          ·
            refine ⟨26466775855553905750588757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70578068948143748668236685 26466775855553905750588757)
            ·
              refine ⟨38769691194659041626839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26466775855553905750588757 38769691194659041626839)
              ·
                rfl

theorem cell22_3057900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 11].length) (baseStart_3057900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057900 prefixEnd_3057900 := by exact prefixLift 3057900
  have htrace : WordTrace (prefixWord ++ tailWord_3057900) baseStart_3057900 baseEnd_3057900 := by
    simpa [prefixWord, tailWord_3057900, baseEnd_3057900] using wordTrace_append hprefix tailTrace_3057900
  have hstable : (prefixWord ++ tailWord_3057900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057900).length < 2 ^ (prefixWord ++ tailWord_3057900).sum := by decide
  have hdescent : baseEnd_3057900 < baseStart_3057900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057902 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3057902 : Nat := 118140960795 + 3057902 * 2 ^ 59
def prefixEnd_3057902 : Nat := 4983230072969 + 3 ^ 40 * 3057902 * 2
def baseEnd_3057902 : Nat := 1046782346896666785374647

theorem tailTrace_3057902 : CollatzResearch.WordTrace tailWord_3057902 prefixEnd_3057902 1046782346896666785374647 := by
  unfold tailWord_3057902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941356070968847116051995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74353899045167184618943973 13941356070968847116051995)
  ·
    refine ⟨20912034106453270674077993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941356070968847116051995 20912034106453270674077993)
    ·
      refine ⟨15684025579839953005558495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20912034106453270674077993 15684025579839953005558495)
      ·
        refine ⟨23526038369759929508337743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684025579839953005558495 23526038369759929508337743)
        ·
          refine ⟨35289057554639894262506615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526038369759929508337743 35289057554639894262506615)
          ·
            refine ⟨52933586331959841393759923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35289057554639894262506615 52933586331959841393759923)
            ·
              refine ⟨79400379497939762090639885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52933586331959841393759923 79400379497939762090639885)
              ·
                refine ⟨29775142311727410783989957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79400379497939762090639885 29775142311727410783989957)
                ·
                  refine ⟨5582839183448889521998117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29775142311727410783989957 5582839183448889521998117)
                  ·
                    refine ⟨1046782346896666785374647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582839183448889521998117 1046782346896666785374647)
                    ·
                      rfl

theorem cell22_3057902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3057902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057902 prefixEnd_3057902 := by exact prefixLift 3057902
  have htrace : WordTrace (prefixWord ++ tailWord_3057902) baseStart_3057902 baseEnd_3057902 := by
    simpa [prefixWord, tailWord_3057902, baseEnd_3057902] using wordTrace_append hprefix tailTrace_3057902
  have hstable : (prefixWord ++ tailWord_3057902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057902).length < 2 ^ (prefixWord ++ tailWord_3057902).sum := by decide
  have hdescent : baseEnd_3057902 < baseStart_3057902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057921 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3057921 : Nat := 118140960795 + 3057921 * 2 ^ 59
def prefixEnd_3057921 : Nat := 4983230072969 + 3 ^ 40 * 3057921 * 2
def baseEnd_3057921 : Nat := 1046788850984957069149589

theorem tailTrace_3057921 : CollatzResearch.WordTrace tailWord_3057921 prefixEnd_3057921 1046788850984957069149589 := by
  unfold tailWord_3057921
  simp only [CollatzResearch.WordTrace]
  refine ⟨111531541554681943173357617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74354361036454628782238411 111531541554681943173357617)
  ·
    refine ⟨83648656166011457380018213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111531541554681943173357617 83648656166011457380018213)
    ·
      refine ⟨15684123031127148258753415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83648656166011457380018213 15684123031127148258753415)
      ·
        refine ⟨23526184546690722388130123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684123031127148258753415 23526184546690722388130123)
        ·
          refine ⟨35289276820036083582195185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526184546690722388130123 35289276820036083582195185)
          ·
            refine ⟨26466957615027062686646389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35289276820036083582195185 26466957615027062686646389)
            ·
              refine ⟨2481277276408787126873099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26466957615027062686646389 2481277276408787126873099)
              ·
                refine ⟨3721915914613180690309649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481277276408787126873099 3721915914613180690309649)
                ·
                  refine ⟨2791436935959885517732237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3721915914613180690309649 2791436935959885517732237)
                  ·
                    refine ⟨1046788850984957069149589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2791436935959885517732237 1046788850984957069149589)
                    ·
                      rfl

theorem cell22_3057921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3057921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3057921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3057921 prefixEnd_3057921 := by exact prefixLift 3057921
  have htrace : WordTrace (prefixWord ++ tailWord_3057921) baseStart_3057921 baseEnd_3057921 := by
    simpa [prefixWord, tailWord_3057921, baseEnd_3057921] using wordTrace_append hprefix tailTrace_3057921
  have hstable : (prefixWord ++ tailWord_3057921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057921).length < 2 ^ (prefixWord ++ tailWord_3057921).sum := by decide
  have hdescent : baseEnd_3057921 < baseStart_3057921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058144 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_3058144 : Nat := 118140960795 + 3058144 * 2 ^ 59
def prefixEnd_3058144 : Nat := 4983230072969 + 3 ^ 40 * 3058144 * 2
def baseEnd_3058144 : Nat := 1046865188442258820823905

theorem tailTrace_3058144 : CollatzResearch.WordTrace tailWord_3058144 prefixEnd_3058144 1046865188442258820823905 := by
  unfold tailWord_3058144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55769837516437026129362743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74359783355249368172483657 55769837516437026129362743)
  ·
    refine ⟨83654756274655539194044115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55769837516437026129362743 83654756274655539194044115)
    ·
      refine ⟨125482134411983308791066173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83654756274655539194044115 125482134411983308791066173)
      ·
        refine ⟨47055800404493740796649815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125482134411983308791066173 47055800404493740796649815)
        ·
          refine ⟨70583700606740611194974723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47055800404493740796649815 70583700606740611194974723)
          ·
            refine ⟨105875550910110916792462085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70583700606740611194974723 105875550910110916792462085)
            ·
              refine ⟨19851665795645796898586641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105875550910110916792462085 19851665795645796898586641)
              ·
                refine ⟨14888749346734347673939981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19851665795645796898586641 14888749346734347673939981)
                ·
                  refine ⟨5583281005025380377727493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14888749346734347673939981 5583281005025380377727493)
                  ·
                    refine ⟨1046865188442258820823905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5583281005025380377727493 1046865188442258820823905)
                    ·
                      rfl

theorem cell22_3058144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_3058144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058144 prefixEnd_3058144 := by exact prefixLift 3058144
  have htrace : WordTrace (prefixWord ++ tailWord_3058144) baseStart_3058144 baseEnd_3058144 := by
    simpa [prefixWord, tailWord_3058144, baseEnd_3058144] using wordTrace_append hprefix tailTrace_3058144
  have hstable : (prefixWord ++ tailWord_3058144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058144).length < 2 ^ (prefixWord ++ tailWord_3058144).sum := by decide
  have hdescent : baseEnd_3058144 < baseStart_3058144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058182 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3058182 : Nat := 118140960795 + 3058182 * 2 ^ 59
def prefixEnd_3058182 : Nat := 4983230072969 + 3 ^ 40 * 3058182 * 2
def baseEnd_3058182 : Nat := 348959398872946462791263

theorem tailTrace_3058182 : CollatzResearch.WordTrace tailWord_3058182 prefixEnd_3058182 348959398872946462791263 := by
  unfold tailWord_3058182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485658156460512023394025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74360707337824256499072533 3485658156460512023394025)
  ·
    refine ⟨2614243617345384017545519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3485658156460512023394025 2614243617345384017545519)
    ·
      refine ⟨3921365426018076026318279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614243617345384017545519 3921365426018076026318279)
      ·
        refine ⟨5882048139027114039477419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921365426018076026318279 5882048139027114039477419)
        ·
          refine ⟨8823072208540671059216129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882048139027114039477419 8823072208540671059216129)
          ·
            refine ⟨6617304156405503294412097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8823072208540671059216129 6617304156405503294412097)
            ·
              refine ⟨4962978117304127470809073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6617304156405503294412097 4962978117304127470809073)
              ·
                refine ⟨3722233587978095603106805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962978117304127470809073 3722233587978095603106805)
                ·
                  refine ⟨348959398872946462791263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722233587978095603106805 348959398872946462791263)
                  ·
                    rfl

theorem cell22_3058182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3058182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058182 prefixEnd_3058182 := by exact prefixLift 3058182
  have htrace : WordTrace (prefixWord ++ tailWord_3058182) baseStart_3058182 baseEnd_3058182 := by
    simpa [prefixWord, tailWord_3058182, baseEnd_3058182] using wordTrace_append hprefix tailTrace_3058182
  have hstable : (prefixWord ++ tailWord_3058182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058182).length < 2 ^ (prefixWord ++ tailWord_3058182).sum := by decide
  have hdescent : baseEnd_3058182 < baseStart_3058182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058191 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 2, 3]
def baseStart_3058191 : Nat := 118140960795 + 3058191 * 2 ^ 59
def prefixEnd_3058191 : Nat := 4983230072969 + 3 ^ 40 * 3058191 * 2
def baseEnd_3058191 : Nat := 1046881277502766364898761

theorem tailTrace_3058191 : CollatzResearch.WordTrace tailWord_3058191 prefixEnd_3058191 1046881277502766364898761 := by
  unfold tailWord_3058191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111541389263703779285686427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74360926175802519523790951 111541389263703779285686427)
  ·
    refine ⟨167312083895555668928529641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111541389263703779285686427 167312083895555668928529641)
    ·
      refine ⟨125484062921666751696397231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167312083895555668928529641 125484062921666751696397231)
      ·
        refine ⟨188226094382500127544595847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125484062921666751696397231 188226094382500127544595847)
        ·
          refine ⟨282339141573750191316893771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188226094382500127544595847 282339141573750191316893771)
          ·
            refine ⟨423508712360625286975340657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282339141573750191316893771 423508712360625286975340657)
            ·
              refine ⟨317631534270468965231505493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423508712360625286975340657 317631534270468965231505493)
              ·
                refine ⟨3722244542232058186306705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 317631534270468965231505493 3722244542232058186306705)
                ·
                  refine ⟨2791683406674043639730029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722244542232058186306705 2791683406674043639730029)
                  ·
                    refine ⟨1046881277502766364898761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2791683406674043639730029 1046881277502766364898761)
                    ·
                      rfl

theorem cell22_3058191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_3058191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058191 prefixEnd_3058191 := by exact prefixLift 3058191
  have htrace : WordTrace (prefixWord ++ tailWord_3058191) baseStart_3058191 baseEnd_3058191 := by
    simpa [prefixWord, tailWord_3058191, baseEnd_3058191] using wordTrace_append hprefix tailTrace_3058191
  have hstable : (prefixWord ++ tailWord_3058191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058191).length < 2 ^ (prefixWord ++ tailWord_3058191).sum := by decide
  have hdescent : baseEnd_3058191 < baseStart_3058191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058208 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_3058208 : Nat := 118140960795 + 3058208 * 2 ^ 59
def prefixEnd_3058208 : Nat := 4983230072969 + 3 ^ 40 * 3058208 * 2
def baseEnd_3058208 : Nat := 1046887096950183987223709

theorem tailTrace_3058208 : CollatzResearch.WordTrace tailWord_3058208 prefixEnd_3058208 1046887096950183987223709 := by
  unfold tailWord_3058208
  simp only [CollatzResearch.WordTrace]
  refine ⟨55771004652321095594527639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74361339536428127459370185 55771004652321095594527639)
  ·
    refine ⟨83656506978481643391791459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55771004652321095594527639 83656506978481643391791459)
    ·
      refine ⟨125484760467722465087687189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83656506978481643391791459 125484760467722465087687189)
      ·
        refine ⟨5882098146924490550985337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125484760467722465087687189 5882098146924490550985337)
        ·
          refine ⟨4411573610193367913239003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5882098146924490550985337 4411573610193367913239003)
          ·
            refine ⟨6617360415290051869858505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411573610193367913239003 6617360415290051869858505)
            ·
              refine ⟨4963020311467538902393879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6617360415290051869858505 4963020311467538902393879)
              ·
                refine ⟨7444530467201308353590819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963020311467538902393879 7444530467201308353590819)
                ·
                  refine ⟨11166795700801962530386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444530467201308353590819 11166795700801962530386229)
                  ·
                    refine ⟨1046887096950183987223709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11166795700801962530386229 1046887096950183987223709)
                    ·
                      rfl

theorem cell22_3058208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_3058208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058208 prefixEnd_3058208 := by exact prefixLift 3058208
  have htrace : WordTrace (prefixWord ++ tailWord_3058208) baseStart_3058208 baseEnd_3058208 := by
    simpa [prefixWord, tailWord_3058208, baseEnd_3058208] using wordTrace_append hprefix tailTrace_3058208
  have hstable : (prefixWord ++ tailWord_3058208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058208).length < 2 ^ (prefixWord ++ tailWord_3058208).sum := by decide
  have hdescent : baseEnd_3058208 < baseStart_3058208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058238 : List Nat := [4, 2, 1, 4, 1, 1, 9]
def baseStart_3058238 : Nat := 118140960795 + 3058238 * 2 ^ 59
def prefixEnd_3058238 : Nat := 4983230072969 + 3 ^ 40 * 3058238 * 2
def baseEnd_3058238 : Nat := 38773976539380515147171

theorem tailTrace_3058238 : CollatzResearch.WordTrace tailWord_3058238 prefixEnd_3058238 38773976539380515147171 := by
  unfold tailWord_3058238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942887936816688289080921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74362068996355670875098245 13942887936816688289080921)
  ·
    refine ⟨10457165952612516216810691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13942887936816688289080921 10457165952612516216810691)
    ·
      refine ⟨15685748928918774325216037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10457165952612516216810691 15685748928918774325216037)
      ·
        refine ⟨2941077924172270185978007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15685748928918774325216037 2941077924172270185978007)
        ·
          refine ⟨4411616886258405278967011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941077924172270185978007 4411616886258405278967011)
          ·
            refine ⟨6617425329387607918450517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411616886258405278967011 6617425329387607918450517)
            ·
              refine ⟨38773976539380515147171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6617425329387607918450517 38773976539380515147171)
              ·
                rfl

theorem cell22_3058238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 9].length) (baseStart_3058238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058238 prefixEnd_3058238 := by exact prefixLift 3058238
  have htrace : WordTrace (prefixWord ++ tailWord_3058238) baseStart_3058238 baseEnd_3058238 := by
    simpa [prefixWord, tailWord_3058238, baseEnd_3058238] using wordTrace_append hprefix tailTrace_3058238
  have hstable : (prefixWord ++ tailWord_3058238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058238).length < 2 ^ (prefixWord ++ tailWord_3058238).sum := by decide
  have hdescent : baseEnd_3058238 < baseStart_3058238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058330 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_3058330 : Nat := 118140960795 + 3058330 * 2 ^ 59
def prefixEnd_3058330 : Nat := 4983230072969 + 3 ^ 40 * 3058330 * 2
def baseEnd_3058330 : Nat := 1046928860043416335673335

theorem tailTrace_3058330 : CollatzResearch.WordTrace tailWord_3058330 prefixEnd_3058330 1046928860043416335673335 := by
  unfold tailWord_3058330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27886614752550051506249111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74364306006800137349997629 27886614752550051506249111)
  ·
    refine ⟨41829922128825077259373667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27886614752550051506249111 41829922128825077259373667)
    ·
      refine ⟨62744883193237615889060501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41829922128825077259373667 62744883193237615889060501)
      ·
        refine ⟨2941166399683013244799711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62744883193237615889060501 2941166399683013244799711)
        ·
          refine ⟨4411749599524519867199567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941166399683013244799711 4411749599524519867199567)
          ·
            refine ⟨6617624399286779800799351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411749599524519867199567 6617624399286779800799351)
            ·
              refine ⟨9926436598930169701199027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617624399286779800799351 9926436598930169701199027)
              ·
                refine ⟨14889654898395254551798541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9926436598930169701199027 14889654898395254551798541)
                ·
                  refine ⟨5583620586898220456924453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14889654898395254551798541 5583620586898220456924453)
                  ·
                    refine ⟨1046928860043416335673335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5583620586898220456924453 1046928860043416335673335)
                    ·
                      rfl

theorem cell22_3058330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_3058330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058330 prefixEnd_3058330 := by exact prefixLift 3058330
  have htrace : WordTrace (prefixWord ++ tailWord_3058330) baseStart_3058330 baseEnd_3058330 := by
    simpa [prefixWord, tailWord_3058330, baseEnd_3058330] using wordTrace_append hprefix tailTrace_3058330
  have hstable : (prefixWord ++ tailWord_3058330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058330).length < 2 ^ (prefixWord ++ tailWord_3058330).sum := by decide
  have hdescent : baseEnd_3058330 < baseStart_3058330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058416 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_3058416 : Nat := 118140960795 + 3058416 * 2 ^ 59
def prefixEnd_3058416 : Nat := 4983230072969 + 3 ^ 40 * 3058416 * 2
def baseEnd_3058416 : Nat := 1046958299600940778023071

theorem tailTrace_3058416 : CollatzResearch.WordTrace tailWord_3058416 prefixEnd_3058416 1046958299600940778023071 := by
  unfold tailWord_3058416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55774797843944321356313551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74366397125259095141751401 55774797843944321356313551)
  ·
    refine ⟨83662196765916482034470327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55774797843944321356313551 83662196765916482034470327)
    ·
      refine ⟨125493295148874723051705491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83662196765916482034470327 125493295148874723051705491)
      ·
        refine ⟨188239942723312084577558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125493295148874723051705491 188239942723312084577558237)
        ·
          refine ⟨70589978521242031716584339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188239942723312084577558237 70589978521242031716584339)
          ·
            refine ⟨105884967781863047574876509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70589978521242031716584339 105884967781863047574876509)
            ·
              refine ⟨39706862918198642840578691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105884967781863047574876509 39706862918198642840578691)
              ·
                refine ⟨59560294377297964260868037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39706862918198642840578691 59560294377297964260868037)
                ·
                  refine ⟨11167555195743368298912757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59560294377297964260868037 11167555195743368298912757)
                  ·
                    refine ⟨1046958299600940778023071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11167555195743368298912757 1046958299600940778023071)
                    ·
                      rfl

theorem cell22_3058416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_3058416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058416 prefixEnd_3058416 := by exact prefixLift 3058416
  have htrace : WordTrace (prefixWord ++ tailWord_3058416) baseStart_3058416 baseEnd_3058416 := by
    simpa [prefixWord, tailWord_3058416, baseEnd_3058416] using wordTrace_append hprefix tailTrace_3058416
  have hstable : (prefixWord ++ tailWord_3058416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058416).length < 2 ^ (prefixWord ++ tailWord_3058416).sum := by decide
  have hdescent : baseEnd_3058416 < baseStart_3058416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058418 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_3058418 : Nat := 118140960795 + 3058418 * 2 ^ 59
def prefixEnd_3058418 : Nat := 4983230072969 + 3 ^ 40 * 3058418 * 2
def baseEnd_3058418 : Nat := 348986328080604479824355

theorem tailTrace_3058418 : CollatzResearch.WordTrace tailWord_3058418 prefixEnd_3058418 348986328080604479824355 := by
  unfold tailWord_3058418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887417158470349263549977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74366445755920931369466605 27887417158470349263549977)
  ·
    refine ⟨20915562868852761947662483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27887417158470349263549977 20915562868852761947662483)
    ·
      refine ⟨31373344303279142921493725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20915562868852761947662483 31373344303279142921493725)
      ·
        refine ⟨11765004113729678595560147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31373344303279142921493725 11765004113729678595560147)
        ·
          refine ⟨17647506170594517893340221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765004113729678595560147 17647506170594517893340221)
          ·
            refine ⟨6617814813972944210002583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17647506170594517893340221 6617814813972944210002583)
            ·
              refine ⟨9926722220959416315003875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617814813972944210002583 9926722220959416315003875)
              ·
                refine ⟨14890083331439124472505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9926722220959416315003875 14890083331439124472505813)
                ·
                  refine ⟨348986328080604479824355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14890083331439124472505813 348986328080604479824355)
                  ·
                    rfl

theorem cell22_3058418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_3058418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058418 prefixEnd_3058418 := by exact prefixLift 3058418
  have htrace : WordTrace (prefixWord ++ tailWord_3058418) baseStart_3058418 baseEnd_3058418 := by
    simpa [prefixWord, tailWord_3058418, baseEnd_3058418] using wordTrace_append hprefix tailTrace_3058418
  have hstable : (prefixWord ++ tailWord_3058418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058418).length < 2 ^ (prefixWord ++ tailWord_3058418).sum := by decide
  have hdescent : baseEnd_3058418 < baseStart_3058418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058422 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3058422 : Nat := 118140960795 + 3058422 * 2 ^ 59
def prefixEnd_3058422 : Nat := 4983230072969 + 3 ^ 40 * 3058422 * 2
def baseEnd_3058422 : Nat := 1046960353523558762373053

theorem tailTrace_3058422 : CollatzResearch.WordTrace tailWord_3058422 prefixEnd_3058422 1046960353523558762373053 := by
  unfold tailWord_3058422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971863407866681608584095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74366543017244603824897013 6971863407866681608584095)
  ·
    refine ⟨10457795111800022412876143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6971863407866681608584095 10457795111800022412876143)
    ·
      refine ⟨15686692667700033619314215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10457795111800022412876143 15686692667700033619314215)
      ·
        refine ⟨23530039001550050428971323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15686692667700033619314215 23530039001550050428971323)
        ·
          refine ⟨35295058502325075643456985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23530039001550050428971323 35295058502325075643456985)
          ·
            refine ⟨26471293876743806732592739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35295058502325075643456985 26471293876743806732592739)
            ·
              refine ⟨39706940815115710098889109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26471293876743806732592739 39706940815115710098889109)
              ·
                refine ⟨1861262850708548910885427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39706940815115710098889109 1861262850708548910885427)
                ·
                  refine ⟨2791894276062823366328141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861262850708548910885427 2791894276062823366328141)
                  ·
                    refine ⟨1046960353523558762373053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2791894276062823366328141 1046960353523558762373053)
                    ·
                      rfl

theorem cell22_3058422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3058422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058422 prefixEnd_3058422 := by exact prefixLift 3058422
  have htrace : WordTrace (prefixWord ++ tailWord_3058422) baseStart_3058422 baseEnd_3058422 := by
    simpa [prefixWord, tailWord_3058422, baseEnd_3058422] using wordTrace_append hprefix tailTrace_3058422
  have hstable : (prefixWord ++ tailWord_3058422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058422).length < 2 ^ (prefixWord ++ tailWord_3058422).sum := by decide
  have hdescent : baseEnd_3058422 < baseStart_3058422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058486 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3058486 : Nat := 118140960795 + 3058486 * 2 ^ 59
def prefixEnd_3058486 : Nat := 4983230072969 + 3 ^ 40 * 3058486 * 2
def baseEnd_3058486 : Nat := 348994087343827976257619

theorem tailTrace_3058486 : CollatzResearch.WordTrace tailWord_3058486 prefixEnd_3058486 348994087343827976257619 := by
  unfold tailWord_3058486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972009299852190291729707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74368099198423363111783541 6972009299852190291729707)
  ·
    refine ⟨10458013949778285437594561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6972009299852190291729707 10458013949778285437594561)
    ·
      refine ⟨7843510462333714078195921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10458013949778285437594561 7843510462333714078195921)
      ·
        refine ⟨5882632846750285558646941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7843510462333714078195921 5882632846750285558646941)
        ·
          refine ⟨2205987317531357084492603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5882632846750285558646941 2205987317531357084492603)
          ·
            refine ⟨3308980976297035626738905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205987317531357084492603 3308980976297035626738905)
            ·
              refine ⟨2481735732222776720054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3308980976297035626738905 2481735732222776720054179)
              ·
                refine ⟨3722603598334165080081269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481735732222776720054179 3722603598334165080081269)
                ·
                  refine ⟨348994087343827976257619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722603598334165080081269 348994087343827976257619)
                  ·
                    rfl

theorem cell22_3058486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3058486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058486 prefixEnd_3058486 := by exact prefixLift 3058486
  have htrace : WordTrace (prefixWord ++ tailWord_3058486) baseStart_3058486 baseEnd_3058486 := by
    simpa [prefixWord, tailWord_3058486, baseEnd_3058486] using wordTrace_append hprefix tailTrace_3058486
  have hstable : (prefixWord ++ tailWord_3058486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058486).length < 2 ^ (prefixWord ++ tailWord_3058486).sum := by decide
  have hdescent : baseEnd_3058486 < baseStart_3058486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058508 : List Nat := [2, 2, 1, 3, 3, 1, 2, 8]
def baseStart_3058508 : Nat := 118140960795 + 3058508 * 2 ^ 59
def prefixEnd_3058508 : Nat := 4983230072969 + 3 ^ 40 * 3058508 * 2
def baseEnd_3058508 : Nat := 116332199231231467191421

theorem tailTrace_3058508 : CollatzResearch.WordTrace tailWord_3058508 prefixEnd_3058508 116332199231231467191421 := by
  unfold tailWord_3058508
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776475601777671212488089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74368634135703561616650785 55776475601777671212488089)
  ·
    refine ⟨41832356701333253409366067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55776475601777671212488089 41832356701333253409366067)
    ·
      refine ⟨62748535051999880114049101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41832356701333253409366067 62748535051999880114049101)
      ·
        refine ⟨23530700644499955042768413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62748535051999880114049101 23530700644499955042768413)
        ·
          refine ⟨8824012741687483141038155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23530700644499955042768413 8824012741687483141038155)
          ·
            refine ⟨13236019112531224711557233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824012741687483141038155 13236019112531224711557233)
            ·
              refine ⟨9927014334398418533667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236019112531224711557233 9927014334398418533667925)
              ·
                refine ⟨116332199231231467191421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9927014334398418533667925 116332199231231467191421)
                ·
                  rfl

theorem cell22_3058508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_3058508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058508 prefixEnd_3058508 := by exact prefixLift 3058508
  have htrace : WordTrace (prefixWord ++ tailWord_3058508) baseStart_3058508 baseEnd_3058508 := by
    simpa [prefixWord, tailWord_3058508, baseEnd_3058508] using wordTrace_append hprefix tailTrace_3058508
  have hstable : (prefixWord ++ tailWord_3058508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058508).length < 2 ^ (prefixWord ++ tailWord_3058508).sum := by decide
  have hdescent : baseEnd_3058508 < baseStart_3058508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058540 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_3058540 : Nat := 118140960795 + 3058540 * 2 ^ 59
def prefixEnd_3058540 : Nat := 4983230072969 + 3 ^ 40 * 3058540 * 2
def baseEnd_3058540 : Nat := 1047000747335045787922691

theorem tailTrace_3058540 : CollatzResearch.WordTrace tailWord_3058540 prefixEnd_3058540 1047000747335045787922691 := by
  unfold tailWord_3058540
  simp only [CollatzResearch.WordTrace]
  refine ⟨55777059169719705945070537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74369412226292941260094049 55777059169719705945070537)
  ·
    refine ⟨41832794377289779458802903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55777059169719705945070537 41832794377289779458802903)
    ·
      refine ⟨62749191565934669188204355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41832794377289779458802903 62749191565934669188204355)
      ·
        refine ⟨94123787348902003782306533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62749191565934669188204355 94123787348902003782306533)
        ·
          refine ⟨17648210127919125709182475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94123787348902003782306533 17648210127919125709182475)
          ·
            refine ⟨26472315191878688563773713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648210127919125709182475 26472315191878688563773713)
            ·
              refine ⟨19854236393909016422830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26472315191878688563773713 19854236393909016422830285)
              ·
                refine ⟨7445338647715881158561357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19854236393909016422830285 7445338647715881158561357)
                ·
                  refine ⟨2792001992893455434460509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7445338647715881158561357 2792001992893455434460509)
                  ·
                    refine ⟨1047000747335045787922691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792001992893455434460509 1047000747335045787922691)
                    ·
                      rfl

theorem cell22_3058540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_3058540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058540 prefixEnd_3058540 := by exact prefixLift 3058540
  have htrace : WordTrace (prefixWord ++ tailWord_3058540) baseStart_3058540 baseEnd_3058540 := by
    simpa [prefixWord, tailWord_3058540, baseEnd_3058540] using wordTrace_append hprefix tailTrace_3058540
  have hstable : (prefixWord ++ tailWord_3058540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058540).length < 2 ^ (prefixWord ++ tailWord_3058540).sum := by decide
  have hdescent : baseEnd_3058540 < baseStart_3058540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058542 : List Nat := [4, 1, 2, 3, 2, 2, 1, 7]
def baseStart_3058542 : Nat := 118140960795 + 3058542 * 2 ^ 59
def prefixEnd_3058542 : Nat := 4983230072969 + 3 ^ 40 * 3058542 * 2
def baseEnd_3058542 : Nat := 116333492441768716596965

theorem tailTrace_3058542 : CollatzResearch.WordTrace tailWord_3058542 prefixEnd_3058542 116333492441768716596965 := by
  unfold tailWord_3058542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944273910679020778964235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74369460856954777487809253 13944273910679020778964235)
  ·
    refine ⟨20916410866018531168446353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944273910679020778964235 20916410866018531168446353)
    ·
      refine ⟨15687308149513898376334765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20916410866018531168446353 15687308149513898376334765)
      ·
        refine ⟨5882740556067711891125537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15687308149513898376334765 5882740556067711891125537)
        ·
          refine ⟨4412055417050783918344153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5882740556067711891125537 4412055417050783918344153)
          ·
            refine ⟨3309041562788087938758115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412055417050783918344153 3309041562788087938758115)
            ·
              refine ⟨4963562344182131908137173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309041562788087938758115 4963562344182131908137173)
              ·
                refine ⟨116333492441768716596965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4963562344182131908137173 116333492441768716596965)
                ·
                  rfl

theorem cell22_3058542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_3058542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058542 prefixEnd_3058542 := by exact prefixLift 3058542
  have htrace : WordTrace (prefixWord ++ tailWord_3058542) baseStart_3058542 baseEnd_3058542 := by
    simpa [prefixWord, tailWord_3058542, baseEnd_3058542] using wordTrace_append hprefix tailTrace_3058542
  have hstable : (prefixWord ++ tailWord_3058542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058542).length < 2 ^ (prefixWord ++ tailWord_3058542).sum := by decide
  have hdescent : baseEnd_3058542 < baseStart_3058542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058617 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_3058617 : Nat := 118140960795 + 3058617 * 2 ^ 59
def prefixEnd_3058617 : Nat := 4983230072969 + 3 ^ 40 * 3058617 * 2
def baseEnd_3058617 : Nat := 1047027106008643253747455

theorem tailTrace_3058617 : CollatzResearch.WordTrace tailWord_3058617 prefixEnd_3058617 1047027106008643253747455 := by
  unfold tailWord_3058617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111556926760160454040694105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74371284506773636027129403 111556926760160454040694105)
  ·
    refine ⟨83667695070120340530520579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111556926760160454040694105 83667695070120340530520579)
    ·
      refine ⟨125501542605180510795780869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83667695070120340530520579 125501542605180510795780869)
      ·
        refine ⟨23531539238471345774208913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125501542605180510795780869 23531539238471345774208913)
        ·
          refine ⟨17648654428853509330656685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23531539238471345774208913 17648654428853509330656685)
          ·
            refine ⟨6618245410820065998996257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17648654428853509330656685 6618245410820065998996257)
            ·
              refine ⟨4963684058115049499247193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618245410820065998996257 4963684058115049499247193)
              ·
                refine ⟨3722763043586287124435395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963684058115049499247193 3722763043586287124435395)
                ·
                  refine ⟨5584144565379430686653093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722763043586287124435395 5584144565379430686653093)
                  ·
                    refine ⟨1047027106008643253747455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584144565379430686653093 1047027106008643253747455)
                    ·
                      rfl

theorem cell22_3058617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_3058617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058617 prefixEnd_3058617 := by exact prefixLift 3058617
  have htrace : WordTrace (prefixWord ++ tailWord_3058617) baseStart_3058617 baseEnd_3058617 := by
    simpa [prefixWord, tailWord_3058617, baseEnd_3058617] using wordTrace_append hprefix tailTrace_3058617
  have hstable : (prefixWord ++ tailWord_3058617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058617).length < 2 ^ (prefixWord ++ tailWord_3058617).sum := by decide
  have hdescent : baseEnd_3058617 < baseStart_3058617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058649 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 4]
def baseStart_3058649 : Nat := 118140960795 + 3058649 * 2 ^ 59
def prefixEnd_3058649 : Nat := 4983230072969 + 3 ^ 40 * 3058649 * 2
def baseEnd_3058649 : Nat := 349012686754201945649119

theorem tailTrace_3058649 : CollatzResearch.WordTrace tailWord_3058649 prefixEnd_3058649 349012686754201945649119 := by
  unfold tailWord_3058649
  simp only [CollatzResearch.WordTrace]
  refine ⟨111558093896044523505859001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74372062597363015670572667 111558093896044523505859001)
  ·
    refine ⟨83668570422033392629394251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111558093896044523505859001 83668570422033392629394251)
    ·
      refine ⟨125502855633050088944091377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83668570422033392629394251 125502855633050088944091377)
      ·
        refine ⟨94127141724787566708068533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125502855633050088944091377 94127141724787566708068533)
        ·
          refine ⟨8824419536698834378881425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94127141724787566708068533 8824419536698834378881425)
          ·
            refine ⟨6618314652524125784161069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824419536698834378881425 6618314652524125784161069)
            ·
              refine ⟨2481867994696547169060401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6618314652524125784161069 2481867994696547169060401)
              ·
                refine ⟨1861400996022410376795301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481867994696547169060401 1861400996022410376795301)
                ·
                  refine ⟨349012686754201945649119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1861400996022410376795301 349012686754201945649119)
                  ·
                    rfl

theorem cell22_3058649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_3058649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058649 prefixEnd_3058649 := by exact prefixLift 3058649
  have htrace : WordTrace (prefixWord ++ tailWord_3058649) baseStart_3058649 baseEnd_3058649 := by
    simpa [prefixWord, tailWord_3058649, baseEnd_3058649] using wordTrace_append hprefix tailTrace_3058649
  have hstable : (prefixWord ++ tailWord_3058649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058649).length < 2 ^ (prefixWord ++ tailWord_3058649).sum := by decide
  have hdescent : baseEnd_3058649 < baseStart_3058649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058664 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3058664 : Nat := 118140960795 + 3058664 * 2 ^ 59
def prefixEnd_3058664 : Nat := 4983230072969 + 3 ^ 40 * 3058664 * 2
def baseEnd_3058664 : Nat := 1047043195069150797822311

theorem tailTrace_3058664 : CollatzResearch.WordTrace tailWord_3058664 prefixEnd_3058664 1047043195069150797822311 := by
  unfold tailWord_3058664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55779320495495090533827523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74372427327326787378436697 55779320495495090533827523)
  ·
    refine ⟨83668980743242635800741285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55779320495495090533827523 83668980743242635800741285)
    ·
      refine ⟨15687933889357994212638991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83668980743242635800741285 15687933889357994212638991)
      ·
        refine ⟨23531900834036991318958487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15687933889357994212638991 23531900834036991318958487)
        ·
          refine ⟨35297851251055486978437731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23531900834036991318958487 35297851251055486978437731)
          ·
            refine ⟨52946776876583230467656597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35297851251055486978437731 52946776876583230467656597)
            ·
              refine ⟨2481880166089838928171403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52946776876583230467656597 2481880166089838928171403)
              ·
                refine ⟨3722820249134758392257105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481880166089838928171403 3722820249134758392257105)
                ·
                  refine ⟨2792115186851068794192829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722820249134758392257105 2792115186851068794192829)
                  ·
                    refine ⟨1047043195069150797822311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792115186851068794192829 1047043195069150797822311)
                    ·
                      rfl

theorem cell22_3058664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3058664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058664 prefixEnd_3058664 := by exact prefixLift 3058664
  have htrace : WordTrace (prefixWord ++ tailWord_3058664) baseStart_3058664 baseEnd_3058664 := by
    simpa [prefixWord, tailWord_3058664, baseEnd_3058664] using wordTrace_append hprefix tailTrace_3058664
  have hstable : (prefixWord ++ tailWord_3058664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058664).length < 2 ^ (prefixWord ++ tailWord_3058664).sum := by decide
  have hdescent : baseEnd_3058664 < baseStart_3058664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058722 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3058722 : Nat := 118140960795 + 3058722 * 2 ^ 59
def prefixEnd_3058722 : Nat := 4983230072969 + 3 ^ 40 * 3058722 * 2
def baseEnd_3058722 : Nat := 349021016551485993290711

theorem tailTrace_3058722 : CollatzResearch.WordTrace tailWord_3058722 prefixEnd_3058722 349021016551485993290711 := by
  unfold tailWord_3058722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27890189106195014243316605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74373837616520037982177613 27890189106195014243316605)
  ·
    refine ⟨10458820914823130341243727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27890189106195014243316605 10458820914823130341243727)
    ·
      refine ⟨15688231372234695511865591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10458820914823130341243727 15688231372234695511865591)
      ·
        refine ⟨23532347058352043267798387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15688231372234695511865591 23532347058352043267798387)
        ·
          refine ⟨35298520587528064901697581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23532347058352043267798387 35298520587528064901697581)
          ·
            refine ⟨13236945220323024338136593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35298520587528064901697581 13236945220323024338136593)
            ·
              refine ⟨9927708915242268253602445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236945220323024338136593 9927708915242268253602445)
              ·
                refine ⟨3722890843215850595100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9927708915242268253602445 3722890843215850595100917)
                ·
                  refine ⟨349021016551485993290711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722890843215850595100917 349021016551485993290711)
                  ·
                    rfl

theorem cell22_3058722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3058722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058722 prefixEnd_3058722 := by exact prefixLift 3058722
  have htrace : WordTrace (prefixWord ++ tailWord_3058722) baseStart_3058722 baseEnd_3058722 := by
    simpa [prefixWord, tailWord_3058722, baseEnd_3058722] using wordTrace_append hprefix tailTrace_3058722
  have hstable : (prefixWord ++ tailWord_3058722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058722).length < 2 ^ (prefixWord ++ tailWord_3058722).sum := by decide
  have hdescent : baseEnd_3058722 < baseStart_3058722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058752 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_3058752 : Nat := 118140960795 + 3058752 * 2 ^ 59
def prefixEnd_3058752 : Nat := 4983230072969 + 3 ^ 40 * 3058752 * 2
def baseEnd_3058752 : Nat := 1047073319267547901622041

theorem tailTrace_3058752 : CollatzResearch.WordTrace tailWord_3058752 prefixEnd_3058752 1047073319267547901622041 := by
  unfold tailWord_3058752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55780925307335686048429255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74374567076447581397905673 55780925307335686048429255)
  ·
    refine ⟨83671387961003529072643883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55780925307335686048429255 83671387961003529072643883)
    ·
      refine ⟨125507081941505293608965825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83671387961003529072643883 125507081941505293608965825)
      ·
        refine ⟨94130311456128970206724369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125507081941505293608965825 94130311456128970206724369)
        ·
          refine ⟨70597733592096727655043277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94130311456128970206724369 70597733592096727655043277)
          ·
            refine ⟨26474150097036272870641229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70597733592096727655043277 26474150097036272870641229)
            ·
              refine ⟨9927806286388602326490461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26474150097036272870641229 9927806286388602326490461)
              ·
                refine ⟨3722927357395725872433923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9927806286388602326490461 3722927357395725872433923)
                ·
                  refine ⟨5584391036093588808650885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722927357395725872433923 5584391036093588808650885)
                  ·
                    refine ⟨1047073319267547901622041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584391036093588808650885 1047073319267547901622041)
                    ·
                      rfl

theorem cell22_3058752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_3058752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058752 prefixEnd_3058752 := by exact prefixLift 3058752
  have htrace : WordTrace (prefixWord ++ tailWord_3058752) baseStart_3058752 baseEnd_3058752 := by
    simpa [prefixWord, tailWord_3058752, baseEnd_3058752] using wordTrace_append hprefix tailTrace_3058752
  have hstable : (prefixWord ++ tailWord_3058752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058752).length < 2 ^ (prefixWord ++ tailWord_3058752).sum := by decide
  have hdescent : baseEnd_3058752 < baseStart_3058752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058786 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3058786 : Nat := 118140960795 + 3058786 * 2 ^ 59
def prefixEnd_3058786 : Nat := 4983230072969 + 3 ^ 40 * 3058786 * 2
def baseEnd_3058786 : Nat := 1047084958162383146271937

theorem tailTrace_3058786 : CollatzResearch.WordTrace tailWord_3058786 prefixEnd_3058786 1047084958162383146271937 := by
  unfold tailWord_3058786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27890772674137048975899053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74375393797698797269064141 27890772674137048975899053)
  ·
    refine ⟨10459039752801393365962145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27890772674137048975899053 10459039752801393365962145)
    ·
      refine ⟨7844279814601045024471609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10459039752801393365962145 7844279814601045024471609)
      ·
        refine ⟨5883209860950783768353707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7844279814601045024471609 5883209860950783768353707)
        ·
          refine ⟨8824814791426175652530561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883209860950783768353707 8824814791426175652530561)
          ·
            refine ⟨6618611093569631739397921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824814791426175652530561 6618611093569631739397921)
            ·
              refine ⟨4963958320177223804548441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618611093569631739397921 4963958320177223804548441)
              ·
                refine ⟨3722968740132917853411331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963958320177223804548441 3722968740132917853411331)
                ·
                  refine ⟨5584453110199376780116997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722968740132917853411331 5584453110199376780116997)
                  ·
                    refine ⟨1047084958162383146271937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584453110199376780116997 1047084958162383146271937)
                    ·
                      rfl

theorem cell22_3058786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3058786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058786 prefixEnd_3058786 := by exact prefixLift 3058786
  have htrace : WordTrace (prefixWord ++ tailWord_3058786) baseStart_3058786 baseEnd_3058786 := by
    simpa [prefixWord, tailWord_3058786, baseEnd_3058786] using wordTrace_append hprefix tailTrace_3058786
  have hstable : (prefixWord ++ tailWord_3058786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058786).length < 2 ^ (prefixWord ++ tailWord_3058786).sum := by decide
  have hdescent : baseEnd_3058786 < baseStart_3058786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058797 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3058797 : Nat := 118140960795 + 3058797 * 2 ^ 59
def prefixEnd_3058797 : Nat := 4983230072969 + 3 ^ 40 * 3058797 * 2
def baseEnd_3058797 : Nat := 1047088723687182784246903

theorem tailTrace_3058797 : CollatzResearch.WordTrace tailWord_3058797 prefixEnd_3058797 1047088723687182784246903 := by
  unfold tailWord_3058797
  simp only [CollatzResearch.WordTrace]
  refine ⟨111563491899508344782246645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74375661266338896521497763 111563491899508344782246645)
  ·
    refine ⟨10459077365578907323335623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111563491899508344782246645 10459077365578907323335623)
    ·
      refine ⟨15688616048368360985003435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459077365578907323335623 15688616048368360985003435)
      ·
        refine ⟨23532924072552541477505153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15688616048368360985003435 23532924072552541477505153)
        ·
          refine ⟨17649693054414406108128865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23532924072552541477505153 17649693054414406108128865)
          ·
            refine ⟨13237269790810804581096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17649693054414406108128865 13237269790810804581096649)
            ·
              refine ⟨9927952343108103435822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13237269790810804581096649 9927952343108103435822487)
              ·
                refine ⟨14891928514662155153733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927952343108103435822487 14891928514662155153733731)
                ·
                  refine ⟨22337892771993232730600597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14891928514662155153733731 22337892771993232730600597)
                  ·
                    refine ⟨1047088723687182784246903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22337892771993232730600597 1047088723687182784246903)
                    ·
                      rfl

theorem cell22_3058797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3058797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058797 prefixEnd_3058797 := by exact prefixLift 3058797
  have htrace : WordTrace (prefixWord ++ tailWord_3058797) baseStart_3058797 baseEnd_3058797 := by
    simpa [prefixWord, tailWord_3058797, baseEnd_3058797] using wordTrace_append hprefix tailTrace_3058797
  have hstable : (prefixWord ++ tailWord_3058797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058797).length < 2 ^ (prefixWord ++ tailWord_3058797).sum := by decide
  have hdescent : baseEnd_3058797 < baseStart_3058797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058878 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_3058878 : Nat := 118140960795 + 3058878 * 2 ^ 59
def prefixEnd_3058878 : Nat := 4983230072969 + 3 ^ 40 * 3058878 * 2
def baseEnd_3058878 : Nat := 1047116451642525572971655

theorem tailTrace_3058878 : CollatzResearch.WordTrace tailWord_3058878 prefixEnd_3058878 1047116451642525572971655 := by
  unfold tailWord_3058878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945805776526861951993161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74377630808143263743963525 13945805776526861951993161)
  ·
    refine ⟨10459354332395146463994871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13945805776526861951993161 10459354332395146463994871)
    ·
      refine ⟨15689031498592719695992307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459354332395146463994871 15689031498592719695992307)
      ·
        refine ⟨23533547247889079543988461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689031498592719695992307 23533547247889079543988461)
        ·
          refine ⟨8825080217958404828995673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23533547247889079543988461 8825080217958404828995673)
          ·
            refine ⟨6618810163468803621746755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8825080217958404828995673 6618810163468803621746755)
            ·
              refine ⟨9928215245203205432620133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618810163468803621746755 9928215245203205432620133)
              ·
                refine ⟨1861540358475601018616275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9928215245203205432620133 1861540358475601018616275)
                ·
                  refine ⟨2792310537713401527924413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861540358475601018616275 2792310537713401527924413)
                  ·
                    refine ⟨1047116451642525572971655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792310537713401527924413 1047116451642525572971655)
                    ·
                      rfl

theorem cell22_3058878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_3058878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058878 prefixEnd_3058878 := by exact prefixLift 3058878
  have htrace : WordTrace (prefixWord ++ tailWord_3058878) baseStart_3058878 baseEnd_3058878 := by
    simpa [prefixWord, tailWord_3058878, baseEnd_3058878] using wordTrace_append hprefix tailTrace_3058878
  have hstable : (prefixWord ++ tailWord_3058878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058878).length < 2 ^ (prefixWord ++ tailWord_3058878).sum := by decide
  have hdescent : baseEnd_3058878 < baseStart_3058878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058977 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3058977 : Nat := 118140960795 + 3058977 * 2 ^ 59
def prefixEnd_3058977 : Nat := 4983230072969 + 3 ^ 40 * 3058977 * 2
def baseEnd_3058977 : Nat := 1047150341365722314746351

theorem tailTrace_3058977 : CollatzResearch.WordTrace tailWord_3058977 prefixEnd_3058977 1047150341365722314746351 := by
  unfold tailWord_3058977
  simp only [CollatzResearch.WordTrace]
  refine ⟨111570057038856235523799185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74380038025904157015866123 111570057038856235523799185)
  ·
    refine ⟨83677542779142176642849389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111570057038856235523799185 83677542779142176642849389)
    ·
      refine ⟨31379078542178316241068521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83677542779142176642849389 31379078542178316241068521)
      ·
        refine ⟨23534308906633737180801391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31379078542178316241068521 23534308906633737180801391)
        ·
          refine ⟨35301463359950605771202087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23534308906633737180801391 35301463359950605771202087)
          ·
            refine ⟨52952195039925908656803131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35301463359950605771202087 52952195039925908656803131)
            ·
              refine ⟨79428292559888862985204697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52952195039925908656803131 79428292559888862985204697)
              ·
                refine ⟨59571219419916647238903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79428292559888862985204697 59571219419916647238903523)
                ·
                  refine ⟨89356829129874970858355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59571219419916647238903523 89356829129874970858355285)
                  ·
                    refine ⟨1047150341365722314746351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89356829129874970858355285 1047150341365722314746351)
                    ·
                      rfl

theorem cell22_3058977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3058977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058977 prefixEnd_3058977 := by exact prefixLift 3058977
  have htrace : WordTrace (prefixWord ++ tailWord_3058977) baseStart_3058977 baseEnd_3058977 := by
    simpa [prefixWord, tailWord_3058977, baseEnd_3058977] using wordTrace_append hprefix tailTrace_3058977
  have hstable : (prefixWord ++ tailWord_3058977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058977).length < 2 ^ (prefixWord ++ tailWord_3058977).sum := by decide
  have hdescent : baseEnd_3058977 < baseStart_3058977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058992 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_3058992 : Nat := 118140960795 + 3058992 * 2 ^ 59
def prefixEnd_3058992 : Nat := 4983230072969 + 3 ^ 40 * 3058992 * 2
def baseEnd_3058992 : Nat := 349051825390755758540435

theorem tailTrace_3058992 : CollatzResearch.WordTrace tailWord_3058992 prefixEnd_3058992 349051825390755758540435 := by
  unfold tailWord_3058992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55785302066900946542797615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74380402755867928723730153 55785302066900946542797615)
  ·
    refine ⟨83677953100351419814196423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55785302066900946542797615 83677953100351419814196423)
    ·
      refine ⟨125516929650527129721294635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83677953100351419814196423 125516929650527129721294635)
      ·
        refine ⟨188275394475790694581941953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125516929650527129721294635 188275394475790694581941953)
        ·
          refine ⟨141206545856843020936456465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188275394475790694581941953 141206545856843020936456465)
          ·
            refine ⟨105904909392632265702342349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141206545856843020936456465 105904909392632265702342349)
            ·
              refine ⟨39714341022237099638378381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105904909392632265702342349 39714341022237099638378381)
              ·
                refine ⟨14892877883338912364391893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39714341022237099638378381 14892877883338912364391893)
                ·
                  refine ⟨349051825390755758540435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14892877883338912364391893 349051825390755758540435)
                  ·
                    rfl

theorem cell22_3058992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_3058992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058992 prefixEnd_3058992 := by exact prefixLift 3058992
  have htrace : WordTrace (prefixWord ++ tailWord_3058992) baseStart_3058992 baseEnd_3058992 := by
    simpa [prefixWord, tailWord_3058992, baseEnd_3058992] using wordTrace_append hprefix tailTrace_3058992
  have hstable : (prefixWord ++ tailWord_3058992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058992).length < 2 ^ (prefixWord ++ tailWord_3058992).sum := by decide
  have hdescent : baseEnd_3058992 < baseStart_3058992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058998 : List Nat := [5, 1, 2, 3, 1, 1, 2, 7]
def baseStart_3058998 : Nat := 118140960795 + 3058998 * 2 ^ 59
def prefixEnd_3058998 : Nat := 4983230072969 + 3 ^ 40 * 3058998 * 2
def baseEnd_3058998 : Nat := 116350836677209473330143

theorem tailTrace_3058998 : CollatzResearch.WordTrace tailWord_3058998 prefixEnd_3058998 116350836677209473330143 := by
  unfold tailWord_3058998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973176435736259756894603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74380548647853437406875765 6973176435736259756894603)
  ·
    refine ⟨10459764653604389635341905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6973176435736259756894603 10459764653604389635341905)
    ·
      refine ⟨7844823490203292226506429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10459764653604389635341905 7844823490203292226506429)
      ·
        refine ⟨2941808808826234584939911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7844823490203292226506429 2941808808826234584939911)
        ·
          refine ⟨4412713213239351877409867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941808808826234584939911 4412713213239351877409867)
          ·
            refine ⟨6619069819859027816114801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412713213239351877409867 6619069819859027816114801)
            ·
              refine ⟨4964302364894270862086101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6619069819859027816114801 4964302364894270862086101)
              ·
                refine ⟨116350836677209473330143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4964302364894270862086101 116350836677209473330143)
                ·
                  rfl

theorem cell22_3058998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_3058998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3058998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3058998 prefixEnd_3058998 := by exact prefixLift 3058998
  have htrace : WordTrace (prefixWord ++ tailWord_3058998) baseStart_3058998 baseEnd_3058998 := by
    simpa [prefixWord, tailWord_3058998, baseEnd_3058998] using wordTrace_append hprefix tailTrace_3058998
  have hstable : (prefixWord ++ tailWord_3058998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058998).length < 2 ^ (prefixWord ++ tailWord_3058998).sum := by decide
  have hdescent : baseEnd_3058998 < baseStart_3058998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059047 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3059047 : Nat := 118140960795 + 3059047 * 2 ^ 59
def prefixEnd_3059047 : Nat := 4983230072969 + 3 ^ 40 * 3059047 * 2
def baseEnd_3059047 : Nat := 1047174303796265465496137

theorem tailTrace_3059047 : CollatzResearch.WordTrace tailWord_3059047 prefixEnd_3059047 1047174303796265465496137 := by
  unfold tailWord_3059047
  simp only [CollatzResearch.WordTrace]
  refine ⟨111572610148602637478847395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74381740099068424985898263 111572610148602637478847395)
  ·
    refine ⟨167358915222903956218271093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111572610148602637478847395 167358915222903956218271093)
    ·
      refine ⟨15689898302147245895462915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167358915222903956218271093 15689898302147245895462915)
      ·
        refine ⟨23534847453220868843194373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689898302147245895462915 23534847453220868843194373)
        ·
          refine ⟨4412783897478912908098945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23534847453220868843194373 4412783897478912908098945)
          ·
            refine ⟨3309587923109184681074209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412783897478912908098945 3309587923109184681074209)
            ·
              refine ⟨2482190942331888510805657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309587923109184681074209 2482190942331888510805657)
              ·
                refine ⟨1861643206748916383104243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482190942331888510805657 1861643206748916383104243)
                ·
                  refine ⟨2792464810123374574656365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861643206748916383104243 2792464810123374574656365)
                  ·
                    refine ⟨1047174303796265465496137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792464810123374574656365 1047174303796265465496137)
                    ·
                      rfl

theorem cell22_3059047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3059047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059047 prefixEnd_3059047 := by exact prefixLift 3059047
  have htrace : WordTrace (prefixWord ++ tailWord_3059047) baseStart_3059047 baseEnd_3059047 := by
    simpa [prefixWord, tailWord_3059047, baseEnd_3059047] using wordTrace_append hprefix tailTrace_3059047
  have hstable : (prefixWord ++ tailWord_3059047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059047).length < 2 ^ (prefixWord ++ tailWord_3059047).sum := by decide
  have hdescent : baseEnd_3059047 < baseStart_3059047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059084 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_3059084 : Nat := 118140960795 + 3059084 * 2 ^ 59
def prefixEnd_3059084 : Nat := 4983230072969 + 3 ^ 40 * 3059084 * 2
def baseEnd_3059084 : Nat := 1047186969652409702321023

theorem tailTrace_3059084 : CollatzResearch.WordTrace tailWord_3059084 prefixEnd_3059084 1047186969652409702321023 := by
  unfold tailWord_3059084
  simp only [CollatzResearch.WordTrace]
  refine ⟨55786979824734296398972153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74382639766312395198629537 55786979824734296398972153)
  ·
    refine ⟨41840234868550722299229115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55786979824734296398972153 41840234868550722299229115)
    ·
      refine ⟨62760352302826083448843673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41840234868550722299229115 62760352302826083448843673)
      ·
        refine ⟨47070264227119562586632755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62760352302826083448843673 47070264227119562586632755)
        ·
          refine ⟨70605396340679343879949133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47070264227119562586632755 70605396340679343879949133)
          ·
            refine ⟨26477023627754753954980925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70605396340679343879949133 26477023627754753954980925)
            ·
              refine ⟨9928883860408032733117847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26477023627754753954980925 9928883860408032733117847)
              ·
                refine ⟨14893325790612049099676771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928883860408032733117847 14893325790612049099676771)
                ·
                  refine ⟨22339988685918073649515157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14893325790612049099676771 22339988685918073649515157)
                  ·
                    refine ⟨1047186969652409702321023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22339988685918073649515157 1047186969652409702321023)
                    ·
                      rfl

theorem cell22_3059084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_3059084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059084 prefixEnd_3059084 := by exact prefixLift 3059084
  have htrace : WordTrace (prefixWord ++ tailWord_3059084) baseStart_3059084 baseEnd_3059084 := by
    simpa [prefixWord, tailWord_3059084, baseEnd_3059084] using wordTrace_append hprefix tailTrace_3059084
  have hstable : (prefixWord ++ tailWord_3059084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059084).length < 2 ^ (prefixWord ++ tailWord_3059084).sum := by decide
  have hdescent : baseEnd_3059084 < baseStart_3059084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059090 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3059090 : Nat := 118140960795 + 3059090 * 2 ^ 59
def prefixEnd_3059090 : Nat := 4983230072969 + 3 ^ 40 * 3059090 * 2
def baseEnd_3059090 : Nat := 1047189023575027686671005

theorem tailTrace_3059090 : CollatzResearch.WordTrace tailWord_3059090 prefixEnd_3059090 1047189023575027686671005 := by
  unfold tailWord_3059090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27893544621861713955665681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74382785658297903881775149 27893544621861713955665681)
  ·
    refine ⟨20920158466396285466749261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27893544621861713955665681 20920158466396285466749261)
    ·
      refine ⟨7845059424898607050030973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20920158466396285466749261 7845059424898607050030973)
      ·
        refine ⟨2941897284336977643761615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7845059424898607050030973 2941897284336977643761615)
        ·
          refine ⟨4412845926505466465642423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941897284336977643761615 4412845926505466465642423)
          ·
            refine ⟨6619268889758199698463635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412845926505466465642423 6619268889758199698463635)
            ·
              refine ⟨9928903334637299547695453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619268889758199698463635 9928903334637299547695453)
              ·
                refine ⟨3723338750488987330385795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9928903334637299547695453 3723338750488987330385795)
                ·
                  refine ⟨5585008125733480995578693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723338750488987330385795 5585008125733480995578693)
                  ·
                    refine ⟨1047189023575027686671005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585008125733480995578693 1047189023575027686671005)
                    ·
                      rfl

theorem cell22_3059090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3059090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059090 prefixEnd_3059090 := by exact prefixLift 3059090
  have htrace : WordTrace (prefixWord ++ tailWord_3059090) baseStart_3059090 baseEnd_3059090 := by
    simpa [prefixWord, tailWord_3059090, baseEnd_3059090] using wordTrace_append hprefix tailTrace_3059090
  have hstable : (prefixWord ++ tailWord_3059090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059090).length < 2 ^ (prefixWord ++ tailWord_3059090).sum := by decide
  have hdescent : baseEnd_3059090 < baseStart_3059090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059103 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 2, 3]
def baseStart_3059103 : Nat := 118140960795 + 3059103 * 2 ^ 59
def prefixEnd_3059103 : Nat := 4983230072969 + 3 ^ 40 * 3059103 * 2
def baseEnd_3059103 : Nat := 1047193473740699986095965

theorem tailTrace_3059103 : CollatzResearch.WordTrace tailWord_3059103 prefixEnd_3059103 1047193473740699986095965 := by
  unfold tailWord_3059103
  simp only [CollatzResearch.WordTrace]
  refine ⟨111574652636399759042885963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74383101757599839361923975 111574652636399759042885963)
  ·
    refine ⟨167361978954599638564328945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111574652636399759042885963 167361978954599638564328945)
    ·
      refine ⟨125521484215949728923246709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167361978954599638564328945 125521484215949728923246709)
      ·
        refine ⟨11767639145245287086554379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125521484215949728923246709 11767639145245287086554379)
        ·
          refine ⟨17651458717867930629831569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11767639145245287086554379 17651458717867930629831569)
          ·
            refine ⟨13238594038400947972373677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17651458717867930629831569 13238594038400947972373677)
            ·
              refine ⟨4964472764400355489640129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13238594038400947972373677 4964472764400355489640129)
              ·
                refine ⟨3723354573300266617230097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964472764400355489640129 3723354573300266617230097)
                ·
                  refine ⟨2792515929975199962922573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723354573300266617230097 2792515929975199962922573)
                  ·
                    refine ⟨1047193473740699986095965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792515929975199962922573 1047193473740699986095965)
                    ·
                      rfl

theorem cell22_3059103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_3059103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059103 prefixEnd_3059103 := by exact prefixLift 3059103
  have htrace : WordTrace (prefixWord ++ tailWord_3059103) baseStart_3059103 baseEnd_3059103 := by
    simpa [prefixWord, tailWord_3059103, baseEnd_3059103] using wordTrace_append hprefix tailTrace_3059103
  have hstable : (prefixWord ++ tailWord_3059103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059103).length < 2 ^ (prefixWord ++ tailWord_3059103).sum := by decide
  have hdescent : baseEnd_3059103 < baseStart_3059103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059144 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_3059144 : Nat := 118140960795 + 3059144 * 2 ^ 59
def prefixEnd_3059144 : Nat := 4983230072969 + 3 ^ 40 * 3059144 * 2
def baseEnd_3059144 : Nat := 349069169626196515273613

theorem tailTrace_3059144 : CollatzResearch.WordTrace tailWord_3059144 prefixEnd_3059144 349069169626196515273613 := by
  unfold tailWord_3059144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55788074014625611522564243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74384098686167482030085657 55788074014625611522564243)
  ·
    refine ⟨83682111021938417283846365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55788074014625611522564243 83682111021938417283846365)
    ·
      refine ⟨31380791633226906481442387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83682111021938417283846365 31380791633226906481442387)
      ·
        refine ⟨47071187449840359722163581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31380791633226906481442387 47071187449840359722163581)
        ·
          refine ⟨17651695293690134895811343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47071187449840359722163581 17651695293690134895811343)
          ·
            refine ⟨26477542940535202343717015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17651695293690134895811343 26477542940535202343717015)
            ·
              refine ⟨39716314410802803515575523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26477542940535202343717015 39716314410802803515575523)
              ·
                refine ⟨59574471616204205273363285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39716314410802803515575523 59574471616204205273363285)
                ·
                  refine ⟨349069169626196515273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59574471616204205273363285 349069169626196515273613)
                  ·
                    rfl

theorem cell22_3059144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_3059144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059144 prefixEnd_3059144 := by exact prefixLift 3059144
  have htrace : WordTrace (prefixWord ++ tailWord_3059144) baseStart_3059144 baseEnd_3059144 := by
    simpa [prefixWord, tailWord_3059144, baseEnd_3059144] using wordTrace_append hprefix tailTrace_3059144
  have hstable : (prefixWord ++ tailWord_3059144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059144).length < 2 ^ (prefixWord ++ tailWord_3059144).sum := by decide
  have hdescent : baseEnd_3059144 < baseStart_3059144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059159 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3059159 : Nat := 118140960795 + 3059159 * 2 ^ 59
def prefixEnd_3059159 : Nat := 4983230072969 + 3 ^ 40 * 3059159 * 2
def baseEnd_3059159 : Nat := 1047212643685134506695793

theorem tailTrace_3059159 : CollatzResearch.WordTrace tailWord_3059159 prefixEnd_3059159 1047212643685134506695793 := by
  unfold tailWord_3059159
  simp only [CollatzResearch.WordTrace]
  refine ⟨111576695124196880606924531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74384463416131253737949687 111576695124196880606924531)
  ·
    refine ⟨167365042686295320910386797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111576695124196880606924531 167365042686295320910386797)
    ·
      refine ⟨62761891007360745341395049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167365042686295320910386797 62761891007360745341395049)
      ·
        refine ⟨47071418255520559006046287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62761891007360745341395049 47071418255520559006046287)
        ·
          refine ⟨70607127383280838509069431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47071418255520559006046287 70607127383280838509069431)
          ·
            refine ⟨105910691074921257763604147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70607127383280838509069431 105910691074921257763604147)
            ·
              refine ⟨158866036612381886645406221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105910691074921257763604147 158866036612381886645406221)
              ·
                refine ⟨59574763729643207492027333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158866036612381886645406221 59574763729643207492027333)
                ·
                  refine ⟨11170268199308101404755125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59574763729643207492027333 11170268199308101404755125)
                  ·
                    refine ⟨1047212643685134506695793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11170268199308101404755125 1047212643685134506695793)
                    ·
                      rfl

theorem cell22_3059159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3059159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059159 prefixEnd_3059159 := by exact prefixLift 3059159
  have htrace : WordTrace (prefixWord ++ tailWord_3059159) baseStart_3059159 baseEnd_3059159 := by
    simpa [prefixWord, tailWord_3059159, baseEnd_3059159] using wordTrace_append hprefix tailTrace_3059159
  have hstable : (prefixWord ++ tailWord_3059159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059159).length < 2 ^ (prefixWord ++ tailWord_3059159).sum := by decide
  have hdescent : baseEnd_3059159 < baseStart_3059159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059165 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3059165 : Nat := 118140960795 + 3059165 * 2 ^ 59
def prefixEnd_3059165 : Nat := 4983230072969 + 3 ^ 40 * 3059165 * 2
def baseEnd_3059165 : Nat := 1047214697607752491045775

theorem tailTrace_3059165 : CollatzResearch.WordTrace tailWord_3059165 prefixEnd_3059165 1047214697607752491045775 := by
  unfold tailWord_3059165
  simp only [CollatzResearch.WordTrace]
  refine ⟨111576913962175143631642949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74384609308116762421095299 111576913962175143631642949)
  ·
    refine ⟨20920671367907839430933053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111576913962175143631642949 20920671367907839430933053)
    ·
      refine ⟨7845251762965439786599895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20920671367907839430933053 7845251762965439786599895)
      ·
        refine ⟨11767877644448159679899843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7845251762965439786599895 11767877644448159679899843)
        ·
          refine ⟨17651816466672239519849765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11767877644448159679899843 17651816466672239519849765)
          ·
            refine ⟨3309715587501044909971831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17651816466672239519849765 3309715587501044909971831)
            ·
              refine ⟨4964573381251567364957747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309715587501044909971831 4964573381251567364957747)
              ·
                refine ⟨7446860071877351047436621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964573381251567364957747 7446860071877351047436621)
                ·
                  refine ⟨2792572526954006642788733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7446860071877351047436621 2792572526954006642788733)
                  ·
                    refine ⟨1047214697607752491045775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792572526954006642788733 1047214697607752491045775)
                    ·
                      rfl

theorem cell22_3059165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3059165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059165 prefixEnd_3059165 := by exact prefixLift 3059165
  have htrace : WordTrace (prefixWord ++ tailWord_3059165) baseStart_3059165 baseEnd_3059165 := by
    simpa [prefixWord, tailWord_3059165, baseEnd_3059165] using wordTrace_append hprefix tailTrace_3059165
  have hstable : (prefixWord ++ tailWord_3059165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059165).length < 2 ^ (prefixWord ++ tailWord_3059165).sum := by decide
  have hdescent : baseEnd_3059165 < baseStart_3059165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059178 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_3059178 : Nat := 118140960795 + 3059178 * 2 ^ 59
def prefixEnd_3059178 : Nat := 4983230072969 + 3 ^ 40 * 3059178 * 2
def baseEnd_3059178 : Nat := 349073049257808263490245

theorem tailTrace_3059178 : CollatzResearch.WordTrace tailWord_3059178 prefixEnd_3059178 349073049257808263490245 := by
  unfold tailWord_3059178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894347027782011712966547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74384925407418697901244125 27894347027782011712966547)
  ·
    refine ⟨41841520541673017569449821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27894347027782011712966547 41841520541673017569449821)
    ·
      refine ⟨15690570203127381588543683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41841520541673017569449821 15690570203127381588543683)
      ·
        refine ⟨23535855304691072382815525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15690570203127381588543683 23535855304691072382815525)
        ·
          refine ⟨4412972869629576071777911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23535855304691072382815525 4412972869629576071777911)
          ·
            refine ⟨6619459304444364107666867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412972869629576071777911 6619459304444364107666867)
            ·
              refine ⟨9929188956666546161500301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619459304444364107666867 9929188956666546161500301)
              ·
                refine ⟨3723445858749954810562613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929188956666546161500301 3723445858749954810562613)
                ·
                  refine ⟨349073049257808263490245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3723445858749954810562613 349073049257808263490245)
                  ·
                    rfl

theorem cell22_3059178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_3059178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059178 prefixEnd_3059178 := by exact prefixLift 3059178
  have htrace : WordTrace (prefixWord ++ tailWord_3059178) baseStart_3059178 baseEnd_3059178 := by
    simpa [prefixWord, tailWord_3059178, baseEnd_3059178] using wordTrace_append hprefix tailTrace_3059178
  have hstable : (prefixWord ++ tailWord_3059178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059178).length < 2 ^ (prefixWord ++ tailWord_3059178).sum := by decide
  have hdescent : baseEnd_3059178 < baseStart_3059178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059191 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3059191 : Nat := 118140960795 + 3059191 * 2 ^ 59
def prefixEnd_3059191 : Nat := 4983230072969 + 3 ^ 40 * 3059191 * 2
def baseEnd_3059191 : Nat := 1047223597939097089895695

theorem tailTrace_3059191 : CollatzResearch.WordTrace tailWord_3059191 prefixEnd_3059191 1047223597939097089895695 := by
  unfold tailWord_3059191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111577862260080950072089427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74385241506720633381392951 111577862260080950072089427)
  ·
    refine ⟨167366793390121425108134141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111577862260080950072089427 167366793390121425108134141)
    ·
      refine ⟨62762547521295534415550303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167366793390121425108134141 62762547521295534415550303)
      ·
        refine ⟨94143821281943301623325455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62762547521295534415550303 94143821281943301623325455)
        ·
          refine ⟨141215731922914952434988183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94143821281943301623325455 141215731922914952434988183)
          ·
            refine ⟨211823597884372428652482275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141215731922914952434988183 211823597884372428652482275)
            ·
              refine ⟨317735396826558642978723413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211823597884372428652482275 317735396826558642978723413)
              ·
                refine ⟨3723461681561234097406915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 317735396826558642978723413 3723461681561234097406915)
                ·
                  refine ⟨5585192522341851146110373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723461681561234097406915 5585192522341851146110373)
                  ·
                    refine ⟨1047223597939097089895695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585192522341851146110373 1047223597939097089895695)
                    ·
                      rfl

theorem cell22_3059191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3059191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059191 prefixEnd_3059191 := by exact prefixLift 3059191
  have htrace : WordTrace (prefixWord ++ tailWord_3059191) baseStart_3059191 baseEnd_3059191 := by
    simpa [prefixWord, tailWord_3059191, baseEnd_3059191] using wordTrace_append hprefix tailTrace_3059191
  have hstable : (prefixWord ++ tailWord_3059191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059191).length < 2 ^ (prefixWord ++ tailWord_3059191).sum := by decide
  have hdescent : baseEnd_3059191 < baseStart_3059191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059253 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3059253 : Nat := 118140960795 + 3059253 * 2 ^ 59
def prefixEnd_3059253 : Nat := 4983230072969 + 3 ^ 40 * 3059253 * 2
def baseEnd_3059253 : Nat := 1047244821806149594845505

theorem tailTrace_3059253 : CollatzResearch.WordTrace tailWord_3059253 prefixEnd_3059253 1047244821806149594845505 := by
  unfold tailWord_3059253
  simp only [CollatzResearch.WordTrace]
  refine ⟨111580123585856334660846413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74386749057237556440564275 111580123585856334660846413)
  ·
    refine ⟨41842546344696125497817405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111580123585856334660846413 41842546344696125497817405)
    ·
      refine ⟨15690954879261047061681527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41842546344696125497817405 15690954879261047061681527)
      ·
        refine ⟨23536432318891570592522291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15690954879261047061681527 23536432318891570592522291)
        ·
          refine ⟨35304648478337355888783437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23536432318891570592522291 35304648478337355888783437)
          ·
            refine ⟨13239243179376508458293789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35304648478337355888783437 13239243179376508458293789)
            ·
              refine ⟨4964716192266190671860171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13239243179376508458293789 4964716192266190671860171)
              ·
                refine ⟨7447074288399286007790257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964716192266190671860171 7447074288399286007790257)
                ·
                  refine ⟨5585305716299464505842693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7447074288399286007790257 5585305716299464505842693)
                  ·
                    refine ⟨1047244821806149594845505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585305716299464505842693 1047244821806149594845505)
                    ·
                      rfl

theorem cell22_3059253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3059253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059253 prefixEnd_3059253 := by exact prefixLift 3059253
  have htrace : WordTrace (prefixWord ++ tailWord_3059253) baseStart_3059253 baseEnd_3059253 := by
    simpa [prefixWord, tailWord_3059253, baseEnd_3059253] using wordTrace_append hprefix tailTrace_3059253
  have hstable : (prefixWord ++ tailWord_3059253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059253).length < 2 ^ (prefixWord ++ tailWord_3059253).sum := by decide
  have hdescent : baseEnd_3059253 < baseStart_3059253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059360 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_3059360 : Nat := 118140960795 + 3059360 * 2 ^ 59
def prefixEnd_3059360 : Nat := 4983230072969 + 3 ^ 40 * 3059360 * 2
def baseEnd_3059360 : Nat := 1047281450092836982420177

theorem tailTrace_3059360 : CollatzResearch.WordTrace tailWord_3059360 prefixEnd_3059360 1047281450092836982420177 := by
  unfold tailWord_3059360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55792013098234345967495767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74389350797645794623327689 55792013098234345967495767)
  ·
    refine ⟨83688019647351518951243651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55792013098234345967495767 83688019647351518951243651)
    ·
      refine ⟨125532029471027278426865477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83688019647351518951243651 125532029471027278426865477)
      ·
        refine ⟨23537255525817614705037277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125532029471027278426865477 23537255525817614705037277)
        ·
          refine ⟨8826470822181605514388979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23537255525817614705037277 8826470822181605514388979)
          ·
            refine ⟨13239706233272408271583469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8826470822181605514388979 13239706233272408271583469)
            ·
              refine ⟨4964889837477153101843801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13239706233272408271583469 4964889837477153101843801)
              ·
                refine ⟨3723667378107864826382851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964889837477153101843801 3723667378107864826382851)
                ·
                  refine ⟨5585501067161797239574277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723667378107864826382851 5585501067161797239574277)
                  ·
                    refine ⟨1047281450092836982420177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585501067161797239574277 1047281450092836982420177)
                    ·
                      rfl

theorem cell22_3059360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_3059360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059360 prefixEnd_3059360 := by exact prefixLift 3059360
  have htrace : WordTrace (prefixWord ++ tailWord_3059360) baseStart_3059360 baseEnd_3059360 := by
    simpa [prefixWord, tailWord_3059360, baseEnd_3059360] using wordTrace_append hprefix tailTrace_3059360
  have hstable : (prefixWord ++ tailWord_3059360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059360).length < 2 ^ (prefixWord ++ tailWord_3059360).sum := by decide
  have hdescent : baseEnd_3059360 < baseStart_3059360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059386 : List Nat := [3, 1, 1, 1, 2, 14]
def baseStart_3059386 : Nat := 118140960795 + 3059386 * 2 ^ 59
def prefixEnd_3059386 : Nat := 4983230072969 + 3 ^ 40 * 3059386 * 2
def baseEnd_3059386 : Nat := 12929510499063970139137

theorem tailTrace_3059386 : CollatzResearch.WordTrace tailWord_3059386 prefixEnd_3059386 12929510499063970139137 := by
  unfold tailWord_3059386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896243623593624593859503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74389982996249665583625341 27896243623593624593859503)
  ·
    refine ⟨41844365435390436890789255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27896243623593624593859503 41844365435390436890789255)
    ·
      refine ⟨62766548153085655336183883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41844365435390436890789255 62766548153085655336183883)
      ·
        refine ⟨94149822229628483004275825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62766548153085655336183883 94149822229628483004275825)
        ·
          refine ⟨70612366672221362253206869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94149822229628483004275825 70612366672221362253206869)
          ·
            refine ⟨12929510499063970139137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 70612366672221362253206869 12929510499063970139137)
            ·
              rfl

theorem cell22_3059386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 14].length) (baseStart_3059386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059386 prefixEnd_3059386 := by exact prefixLift 3059386
  have htrace : WordTrace (prefixWord ++ tailWord_3059386) baseStart_3059386 baseEnd_3059386 := by
    simpa [prefixWord, tailWord_3059386, baseEnd_3059386] using wordTrace_append hprefix tailTrace_3059386
  have hstable : (prefixWord ++ tailWord_3059386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059386).length < 2 ^ (prefixWord ++ tailWord_3059386).sum := by decide
  have hdescent : baseEnd_3059386 < baseStart_3059386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059448 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_3059448 : Nat := 118140960795 + 3059448 * 2 ^ 59
def prefixEnd_3059448 : Nat := 4983230072969 + 3 ^ 40 * 3059448 * 2
def baseEnd_3059448 : Nat := 349103858097078028739969

theorem tailTrace_3059448 : CollatzResearch.WordTrace tailWord_3059448 prefixEnd_3059448 349103858097078028739969 := by
  unfold tailWord_3059448
  simp only [CollatzResearch.WordTrace]
  refine ⟨55793617910074941482097499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74391490546766588642796665 55793617910074941482097499)
  ·
    refine ⟨83690426865112412223146249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55793617910074941482097499 83690426865112412223146249)
    ·
      refine ⟨62767820148834309167359687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83690426865112412223146249 62767820148834309167359687)
      ·
        refine ⟨94151730223251463751039531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62767820148834309167359687 94151730223251463751039531)
        ·
          refine ⟨141227595334877195626559297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94151730223251463751039531 141227595334877195626559297)
          ·
            refine ⟨105920696501157896719919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141227595334877195626559297 105920696501157896719919473)
            ·
              refine ⟨79440522375868422539939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105920696501157896719919473 79440522375868422539939605)
              ·
                refine ⟨3723774486368832306559669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79440522375868422539939605 3723774486368832306559669)
                ·
                  refine ⟨349103858097078028739969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3723774486368832306559669 349103858097078028739969)
                  ·
                    rfl

theorem cell22_3059448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_3059448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059448 prefixEnd_3059448 := by exact prefixLift 3059448
  have htrace : WordTrace (prefixWord ++ tailWord_3059448) baseStart_3059448 baseEnd_3059448 := by
    simpa [prefixWord, tailWord_3059448, baseEnd_3059448] using wordTrace_append hprefix tailTrace_3059448
  have hstable : (prefixWord ++ tailWord_3059448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059448).length < 2 ^ (prefixWord ++ tailWord_3059448).sum := by decide
  have hdescent : baseEnd_3059448 < baseStart_3059448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059452 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3059452 : Nat := 118140960795 + 3059452 * 2 ^ 59
def prefixEnd_3059452 : Nat := 4983230072969 + 3 ^ 40 * 3059452 * 2
def baseEnd_3059452 : Nat := 1047312943572979409119895

theorem tailTrace_3059452 : CollatzResearch.WordTrace tailWord_3059452 prefixEnd_3059452 1047312943572979409119895 := by
  unfold tailWord_3059452
  simp only [CollatzResearch.WordTrace]
  refine ⟨55793690856067695823670305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74391587808090261098227073 55793690856067695823670305)
  ·
    refine ⟨41845268142050771867752729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55793690856067695823670305 41845268142050771867752729)
    ·
      refine ⟨31383951106538078900814547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41845268142050771867752729 31383951106538078900814547)
      ·
        refine ⟨47075926659807118351221821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31383951106538078900814547 47075926659807118351221821)
        ·
          refine ⟨17653472497427669381708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47075926659807118351221821 17653472497427669381708183)
          ·
            refine ⟨26480208746141504072562275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17653472497427669381708183 26480208746141504072562275)
            ·
              refine ⟨39720313119212256108843413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26480208746141504072562275 39720313119212256108843413)
              ·
                refine ⟨1861889677463074505102035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39720313119212256108843413 1861889677463074505102035)
                ·
                  refine ⟨2792834516194611757653053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861889677463074505102035 2792834516194611757653053)
                  ·
                    refine ⟨1047312943572979409119895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792834516194611757653053 1047312943572979409119895)
                    ·
                      rfl

theorem cell22_3059452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3059452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059452 prefixEnd_3059452 := by exact prefixLift 3059452
  have htrace : WordTrace (prefixWord ++ tailWord_3059452) baseStart_3059452 baseEnd_3059452 := by
    simpa [prefixWord, tailWord_3059452, baseEnd_3059452] using wordTrace_append hprefix tailTrace_3059452
  have hstable : (prefixWord ++ tailWord_3059452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059452).length < 2 ^ (prefixWord ++ tailWord_3059452).sum := by decide
  have hdescent : baseEnd_3059452 < baseStart_3059452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059555 : List Nat := [1, 1, 1, 5, 5, 9]
def baseStart_3059555 : Nat := 118140960795 + 3059555 * 2 ^ 59
def prefixEnd_3059555 : Nat := 4983230072969 + 3 ^ 40 * 3059555 * 2
def baseEnd_3059555 : Nat := 12930224723184215725859

theorem tailTrace_3059555 : CollatzResearch.WordTrace tailWord_3059555 prefixEnd_3059555 12930224723184215725859 := by
  unfold tailWord_3059555
  simp only [CollatzResearch.WordTrace]
  refine ⟨111591138430762240238340119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74394092287174826825560079 111591138430762240238340119)
  ·
    refine ⟨167386707646143360357510179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111591138430762240238340119 167386707646143360357510179)
    ·
      refine ⟨251080061469215040536265269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167386707646143360357510179 251080061469215040536265269)
      ·
        refine ⟨23538755762738910050274869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251080061469215040536265269 23538755762738910050274869)
        ·
          refine ⟨2206758352756772817213269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23538755762738910050274869 2206758352756772817213269)
          ·
            refine ⟨12930224723184215725859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2206758352756772817213269 12930224723184215725859)
            ·
              rfl

theorem cell22_3059555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 9].length) (baseStart_3059555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059555 prefixEnd_3059555 := by exact prefixLift 3059555
  have htrace : WordTrace (prefixWord ++ tailWord_3059555) baseStart_3059555 baseEnd_3059555 := by
    simpa [prefixWord, tailWord_3059555, baseEnd_3059555] using wordTrace_append hprefix tailTrace_3059555
  have hstable : (prefixWord ++ tailWord_3059555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059555).length < 2 ^ (prefixWord ++ tailWord_3059555).sum := by decide
  have hdescent : baseEnd_3059555 < baseStart_3059555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059583 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 9]
def baseStart_3059583 : Nat := 118140960795 + 3059583 * 2 ^ 59
def prefixEnd_3059583 : Nat := 4983230072969 + 3 ^ 40 * 3059583 * 2
def baseEnd_3059583 : Nat := 349119262516712911364831

theorem tailTrace_3059583 : CollatzResearch.WordTrace tailWord_3059583 prefixEnd_3059583 349119262516712911364831 := by
  unfold tailWord_3059583
  simp only [CollatzResearch.WordTrace]
  refine ⟨111592159674660801020359403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74394773116440534013572935 111592159674660801020359403)
  ·
    refine ⟨167388239511991201530539105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111592159674660801020359403 167388239511991201530539105)
    ·
      refine ⟨125541179633993401147904329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167388239511991201530539105 125541179633993401147904329)
      ·
        refine ⟨94155884725495050860928247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125541179633993401147904329 94155884725495050860928247)
        ·
          refine ⟨141233827088242576291392371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94155884725495050860928247 141233827088242576291392371)
          ·
            refine ⟨211850740632363864437088557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141233827088242576291392371 211850740632363864437088557)
            ·
              refine ⟨79444027737136449163908209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211850740632363864437088557 79444027737136449163908209)
              ·
                refine ⟨59583020802852336872931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79444027737136449163908209 59583020802852336872931157)
                ·
                  refine ⟨349119262516712911364831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59583020802852336872931157 349119262516712911364831)
                  ·
                    rfl

theorem cell22_3059583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_3059583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059583 prefixEnd_3059583 := by exact prefixLift 3059583
  have htrace : WordTrace (prefixWord ++ tailWord_3059583) baseStart_3059583 baseEnd_3059583 := by
    simpa [prefixWord, tailWord_3059583, baseEnd_3059583] using wordTrace_append hprefix tailTrace_3059583
  have hstable : (prefixWord ++ tailWord_3059583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059583).length < 2 ^ (prefixWord ++ tailWord_3059583).sum := by decide
  have hdescent : baseEnd_3059583 < baseStart_3059583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059587 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 3, 3]
def baseStart_3059587 : Nat := 118140960795 + 3059587 * 2 ^ 59
def prefixEnd_3059587 : Nat := 4983230072969 + 3 ^ 40 * 3059587 * 2
def baseEnd_3059587 : Nat := 1047359156831884056994481

theorem tailTrace_3059587 : CollatzResearch.WordTrace tailWord_3059587 prefixEnd_3059587 1047359156831884056994481 := by
  unfold tailWord_3059587
  simp only [CollatzResearch.WordTrace]
  refine ⟨111592305566646309703505015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74394870377764206469003343 111592305566646309703505015)
  ·
    refine ⟨167388458349969464555257523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111592305566646309703505015 167388458349969464555257523)
    ·
      refine ⟨251082687524954196832886285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167388458349969464555257523 251082687524954196832886285)
      ·
        refine ⟨94156007821857823812332357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251082687524954196832886285 94156007821857823812332357)
        ·
          refine ⟨17654251466598341964812317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94156007821857823812332357 17654251466598341964812317)
          ·
            refine ⟨6620344299974378236804619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17654251466598341964812317 6620344299974378236804619)
            ·
              refine ⟨9930516449961567355206929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620344299974378236804619 9930516449961567355206929)
              ·
                refine ⟨7447887337471175516405197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9930516449961567355206929 7447887337471175516405197)
                ·
                  refine ⟨2792957751551690818651949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7447887337471175516405197 2792957751551690818651949)
                  ·
                    refine ⟨1047359156831884056994481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792957751551690818651949 1047359156831884056994481)
                    ·
                      rfl

theorem cell22_3059587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].length) (baseStart_3059587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059587 prefixEnd_3059587 := by exact prefixLift 3059587
  have htrace : WordTrace (prefixWord ++ tailWord_3059587) baseStart_3059587 baseEnd_3059587 := by
    simpa [prefixWord, tailWord_3059587, baseEnd_3059587] using wordTrace_append hprefix tailTrace_3059587
  have hstable : (prefixWord ++ tailWord_3059587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059587).length < 2 ^ (prefixWord ++ tailWord_3059587).sum := by decide
  have hdescent : baseEnd_3059587 < baseStart_3059587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059617 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 7]
def baseStart_3059617 : Nat := 118140960795 + 3059617 * 2 ^ 59
def prefixEnd_3059617 : Nat := 4983230072969 + 3 ^ 40 * 3059617 * 2
def baseEnd_3059617 : Nat := 349123142148324659581463

theorem tailTrace_3059617 : CollatzResearch.WordTrace tailWord_3059617 prefixEnd_3059617 349123142148324659581463 := by
  unfold tailWord_3059617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111593399756537624827097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74395599837691749884731403 111593399756537624827097105)
  ·
    refine ⟨83695049817403218620322829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111593399756537624827097105 83695049817403218620322829)
    ·
      refine ⟨31385643681526206982621061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83695049817403218620322829 31385643681526206982621061)
      ·
        refine ⟨5884808190286163809241449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31385643681526206982621061 5884808190286163809241449)
        ·
          refine ⟨4413606142714622856931087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5884808190286163809241449 4413606142714622856931087)
          ·
            refine ⟨6620409214071934285396631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413606142714622856931087 6620409214071934285396631)
            ·
              refine ⟨9930613821107901428094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620409214071934285396631 9930613821107901428094947)
              ·
                refine ⟨14895920731661852142142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9930613821107901428094947 14895920731661852142142421)
                ·
                  refine ⟨349123142148324659581463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14895920731661852142142421 349123142148324659581463)
                  ·
                    rfl

theorem cell22_3059617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_3059617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059617 prefixEnd_3059617 := by exact prefixLift 3059617
  have htrace : WordTrace (prefixWord ++ tailWord_3059617) baseStart_3059617 baseEnd_3059617 := by
    simpa [prefixWord, tailWord_3059617, baseEnd_3059617] using wordTrace_append hprefix tailTrace_3059617
  have hstable : (prefixWord ++ tailWord_3059617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059617).length < 2 ^ (prefixWord ++ tailWord_3059617).sum := by decide
  have hdescent : baseEnd_3059617 < baseStart_3059617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059647 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 1, 4]
def baseStart_3059647 : Nat := 118140960795 + 3059647 * 2 ^ 59
def prefixEnd_3059647 : Nat := 4983230072969 + 3 ^ 40 * 3059647 * 2
def baseEnd_3059647 : Nat := 1047379696058063900494297

theorem tailTrace_3059647 : CollatzResearch.WordTrace tailWord_3059647 prefixEnd_3059647 1047379696058063900494297 := by
  unfold tailWord_3059647
  simp only [CollatzResearch.WordTrace]
  refine ⟨111594493946428939950689195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74396329297619293300459463 111594493946428939950689195)
  ·
    refine ⟨167391740919643409926033793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111594493946428939950689195 167391740919643409926033793)
    ·
      refine ⟨125543805689732557444525345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167391740919643409926033793 125543805689732557444525345)
      ·
        refine ⟨94157854267299418083394009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125543805689732557444525345 94157854267299418083394009)
        ·
          refine ⟨70618390700474563562545507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94157854267299418083394009 70618390700474563562545507)
          ·
            refine ⟨105927586050711845343818261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70618390700474563562545507 105927586050711845343818261)
            ·
              refine ⟨4965355596127117750491481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105927586050711845343818261 4965355596127117750491481)
              ·
                refine ⟨3724016697095338312868611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965355596127117750491481 3724016697095338312868611)
                ·
                  refine ⟨5586025045643007469302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724016697095338312868611 5586025045643007469302917)
                  ·
                    refine ⟨1047379696058063900494297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586025045643007469302917 1047379696058063900494297)
                    ·
                      rfl

theorem cell22_3059647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_3059647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059647 prefixEnd_3059647 := by exact prefixLift 3059647
  have htrace : WordTrace (prefixWord ++ tailWord_3059647) baseStart_3059647 baseEnd_3059647 := by
    simpa [prefixWord, tailWord_3059647, baseEnd_3059647] using wordTrace_append hprefix tailTrace_3059647
  have hstable : (prefixWord ++ tailWord_3059647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059647).length < 2 ^ (prefixWord ++ tailWord_3059647).sum := by decide
  have hdescent : baseEnd_3059647 < baseStart_3059647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059797 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 6]
def baseStart_3059797 : Nat := 118140960795 + 3059797 * 2 ^ 59
def prefixEnd_3059797 : Nat := 4983230072969 + 3 ^ 40 * 3059797 * 2
def baseEnd_3059797 : Nat := 349143681374504503081279

theorem tailTrace_3059797 : CollatzResearch.WordTrace tailWord_3059797 prefixEnd_3059797 349143681374504503081279 := by
  unfold tailWord_3059797
  simp only [CollatzResearch.WordTrace]
  refine ⟨111599964895885515568649645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74399976597257010379099763 111599964895885515568649645)
  ·
    refine ⟨41849986835957068338243617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111599964895885515568649645 41849986835957068338243617)
    ·
      refine ⟨31387490126967801253682713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41849986835957068338243617 31387490126967801253682713)
      ·
        refine ⟨23540617595225850940262035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31387490126967801253682713 23540617595225850940262035)
        ·
          refine ⟨35310926392838776410393053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23540617595225850940262035 35310926392838776410393053)
          ·
            refine ⟨13241597397314541153897395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35310926392838776410393053 13241597397314541153897395)
            ·
              refine ⟨19862396095971811730846093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13241597397314541153897395 19862396095971811730846093)
              ·
                refine ⟨7448398535989429399067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19862396095971811730846093 7448398535989429399067285)
                ·
                  refine ⟨349143681374504503081279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7448398535989429399067285 349143681374504503081279)
                  ·
                    rfl

theorem cell22_3059797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_3059797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059797 prefixEnd_3059797 := by exact prefixLift 3059797
  have htrace : WordTrace (prefixWord ++ tailWord_3059797) baseStart_3059797 baseEnd_3059797 := by
    simpa [prefixWord, tailWord_3059797, baseEnd_3059797] using wordTrace_append hprefix tailTrace_3059797
  have hstable : (prefixWord ++ tailWord_3059797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059797).length < 2 ^ (prefixWord ++ tailWord_3059797).sum := by decide
  have hdescent : baseEnd_3059797 < baseStart_3059797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059831 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 4]
def baseStart_3059831 : Nat := 118140960795 + 3059831 * 2 ^ 59
def prefixEnd_3059831 : Nat := 4983230072969 + 3 ^ 40 * 3059831 * 2
def baseEnd_3059831 : Nat := 349147561006116251297911

theorem tailTrace_3059831 : CollatzResearch.WordTrace tailWord_3059831 prefixEnd_3059831 349147561006116251297911 := by
  unfold tailWord_3059831
  simp only [CollatzResearch.WordTrace]
  refine ⟨111601204977762339375387347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74400803318508226250258231 111601204977762339375387347)
  ·
    refine ⟨167401807466643509063081021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111601204977762339375387347 167401807466643509063081021)
    ·
      refine ⟨62775677799991315898655383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167401807466643509063081021 62775677799991315898655383)
      ·
        refine ⟨94163516699986973847983075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62775677799991315898655383 94163516699986973847983075)
        ·
          refine ⟨141245275049980460771974613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94163516699986973847983075 141245275049980460771974613)
          ·
            refine ⟨3310436133983917049343155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141245275049980460771974613 3310436133983917049343155)
            ·
              refine ⟨4965654200975875574014733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310436133983917049343155 4965654200975875574014733)
              ·
                refine ⟨1862120325365953340255525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4965654200975875574014733 1862120325365953340255525)
                ·
                  refine ⟨349147561006116251297911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862120325365953340255525 349147561006116251297911)
                  ·
                    rfl

theorem cell22_3059831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 4].length) (baseStart_3059831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059831 prefixEnd_3059831 := by exact prefixLift 3059831
  have htrace : WordTrace (prefixWord ++ tailWord_3059831) baseStart_3059831 baseEnd_3059831 := by
    simpa [prefixWord, tailWord_3059831, baseEnd_3059831] using wordTrace_append hprefix tailTrace_3059831
  have hstable : (prefixWord ++ tailWord_3059831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059831).length < 2 ^ (prefixWord ++ tailWord_3059831).sum := by decide
  have hdescent : baseEnd_3059831 < baseStart_3059831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059844 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3059844 : Nat := 118140960795 + 3059844 * 2 ^ 59
def prefixEnd_3059844 : Nat := 4983230072969 + 3 ^ 40 * 3059844 * 2
def baseEnd_3059844 : Nat := 1047447133184021053318693

theorem tailTrace_3059844 : CollatzResearch.WordTrace tailWord_3059844 prefixEnd_3059844 1047447133184021053318693 := by
  unfold tailWord_3059844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55800839563357621297805293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74401119417810161730407057 55800839563357621297805293)
  ·
    refine ⟨20925314836259107986676985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55800839563357621297805293 20925314836259107986676985)
    ·
      refine ⟨15693986127194330990007739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20925314836259107986676985 15693986127194330990007739)
      ·
        refine ⟨23540979190791496485011609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693986127194330990007739 23540979190791496485011609)
        ·
          refine ⟨17655734393093622363758707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23540979190791496485011609 17655734393093622363758707)
          ·
            refine ⟨26483601589640433545638061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17655734393093622363758707 26483601589640433545638061)
            ·
              refine ⟨9931350596115162579614273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26483601589640433545638061 9931350596115162579614273)
              ·
                refine ⟨7448512947086371934710705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9931350596115162579614273 7448512947086371934710705)
                ·
                  refine ⟨5586384710314778951033029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448512947086371934710705 5586384710314778951033029)
                  ·
                    refine ⟨1047447133184021053318693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586384710314778951033029 1047447133184021053318693)
                    ·
                      rfl

theorem cell22_3059844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3059844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059844 prefixEnd_3059844 := by exact prefixLift 3059844
  have htrace : WordTrace (prefixWord ++ tailWord_3059844) baseStart_3059844 baseEnd_3059844 := by
    simpa [prefixWord, tailWord_3059844, baseEnd_3059844] using wordTrace_append hprefix tailTrace_3059844
  have hstable : (prefixWord ++ tailWord_3059844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059844).length < 2 ^ (prefixWord ++ tailWord_3059844).sum := by decide
  have hdescent : baseEnd_3059844 < baseStart_3059844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059848 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_3059848 : Nat := 118140960795 + 3059848 * 2 ^ 59
def prefixEnd_3059848 : Nat := 4983230072969 + 3 ^ 40 * 3059848 * 2
def baseEnd_3059848 : Nat := 349149500821922125406227

theorem tailTrace_3059848 : CollatzResearch.WordTrace tailWord_3059848 prefixEnd_3059848 349149500821922125406227 := by
  unfold tailWord_3059848
  simp only [CollatzResearch.WordTrace]
  refine ⟨55800912509350375639378099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74401216679133834185837465 55800912509350375639378099)
  ·
    refine ⟨83701368764025563459067149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55800912509350375639378099 83701368764025563459067149)
    ·
      refine ⟨31388013286509586297150181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83701368764025563459067149 31388013286509586297150181)
      ·
        refine ⟨5885252491220547430715659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31388013286509586297150181 5885252491220547430715659)
        ·
          refine ⟨8827878736830821146073489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885252491220547430715659 8827878736830821146073489)
          ·
            refine ⟨6620909052623115859555117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8827878736830821146073489 6620909052623115859555117)
            ·
              refine ⟨2482840894733668447333169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6620909052623115859555117 2482840894733668447333169)
              ·
                refine ⟨1862130671050251335499877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482840894733668447333169 1862130671050251335499877)
                ·
                  refine ⟨349149500821922125406227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862130671050251335499877 349149500821922125406227)
                  ·
                    rfl

theorem cell22_3059848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_3059848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059848 prefixEnd_3059848 := by exact prefixLift 3059848
  have htrace : WordTrace (prefixWord ++ tailWord_3059848) baseStart_3059848 baseEnd_3059848 := by
    simpa [prefixWord, tailWord_3059848, baseEnd_3059848] using wordTrace_append hprefix tailTrace_3059848
  have hstable : (prefixWord ++ tailWord_3059848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059848).length < 2 ^ (prefixWord ++ tailWord_3059848).sum := by decide
  have hdescent : baseEnd_3059848 < baseStart_3059848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059891 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 1, 3]
def baseStart_3059891 : Nat := 118140960795 + 3059891 * 2 ^ 59
def prefixEnd_3059891 : Nat := 4983230072969 + 3 ^ 40 * 3059891 * 2
def baseEnd_3059891 : Nat := 1047463222244528597393549

theorem tailTrace_3059891 : CollatzResearch.WordTrace tailWord_3059891 prefixEnd_3059891 1047463222244528597393549 := by
  unfold tailWord_3059891
  simp only [CollatzResearch.WordTrace]
  refine ⟨111603393357544969622571527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74402262238363313081714351 111603393357544969622571527)
  ·
    refine ⟨167405090036317454433857291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111603393357544969622571527 167405090036317454433857291)
    ·
      refine ⟨251107635054476181650785937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167405090036317454433857291 251107635054476181650785937)
      ·
        refine ⟨188330726290857136238089453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251107635054476181650785937 188330726290857136238089453)
        ·
          refine ⟨70624022359071426089283545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188330726290857136238089453 70624022359071426089283545)
          ·
            refine ⟨52968016769303569566962659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70624022359071426089283545 52968016769303569566962659)
            ·
              refine ⟨79452025153955354350443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52968016769303569566962659 79452025153955354350443989)
              ·
                refine ⟨1862156839545828617588531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79452025153955354350443989 1862156839545828617588531)
                ·
                  refine ⟨2793235259318742926382797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862156839545828617588531 2793235259318742926382797)
                  ·
                    refine ⟨1047463222244528597393549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2793235259318742926382797 1047463222244528597393549)
                    ·
                      rfl

theorem cell22_3059891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 3].length) (baseStart_3059891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059891 prefixEnd_3059891 := by exact prefixLift 3059891
  have htrace : WordTrace (prefixWord ++ tailWord_3059891) baseStart_3059891 baseEnd_3059891 := by
    simpa [prefixWord, tailWord_3059891, baseEnd_3059891] using wordTrace_append hprefix tailTrace_3059891
  have hstable : (prefixWord ++ tailWord_3059891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059891).length < 2 ^ (prefixWord ++ tailWord_3059891).sum := by decide
  have hdescent : baseEnd_3059891 < baseStart_3059891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059904 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_3059904 : Nat := 118140960795 + 3059904 * 2 ^ 59
def prefixEnd_3059904 : Nat := 4983230072969 + 3 ^ 40 * 3059904 * 2
def baseEnd_3059904 : Nat := 349155890803400298939503

theorem tailTrace_3059904 : CollatzResearch.WordTrace tailWord_3059904 prefixEnd_3059904 349155890803400298939503 := by
  unfold tailWord_3059904
  simp only [CollatzResearch.WordTrace]
  refine ⟨55801933753248936421397383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74402578337665248561863177 55801933753248936421397383)
  ·
    refine ⟨83702900629873404632096075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55801933753248936421397383 83702900629873404632096075)
    ·
      refine ⟨125554350944810106948144113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83702900629873404632096075 125554350944810106948144113)
      ·
        refine ⟨94165763208607580211108085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125554350944810106948144113 94165763208607580211108085)
        ·
          refine ⟨8828040300806960644791383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94165763208607580211108085 8828040300806960644791383)
          ·
            refine ⟨13242060451210440967187075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828040300806960644791383 13242060451210440967187075)
            ·
              refine ⟨19863090676815661450780613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13242060451210440967187075 19863090676815661450780613)
              ·
                refine ⟨3724329501902936522021365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19863090676815661450780613 3724329501902936522021365)
                ·
                  refine ⟨349155890803400298939503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3724329501902936522021365 349155890803400298939503)
                  ·
                    rfl

theorem cell22_3059904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_3059904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059904 prefixEnd_3059904 := by exact prefixLift 3059904
  have htrace : WordTrace (prefixWord ++ tailWord_3059904) baseStart_3059904 baseEnd_3059904 := by
    simpa [prefixWord, tailWord_3059904, baseEnd_3059904] using wordTrace_append hprefix tailTrace_3059904
  have hstable : (prefixWord ++ tailWord_3059904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059904).length < 2 ^ (prefixWord ++ tailWord_3059904).sum := by decide
  have hdescent : baseEnd_3059904 < baseStart_3059904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059951 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 1, 4]
def baseStart_3059951 : Nat := 118140960795 + 3059951 * 2 ^ 59
def prefixEnd_3059951 : Nat := 4983230072969 + 3 ^ 40 * 3059951 * 2
def baseEnd_3059951 : Nat := 1047483761470708440893365

theorem tailTrace_3059951 : CollatzResearch.WordTrace tailWord_3059951 prefixEnd_3059951 1047483761470708440893365 := by
  unfold tailWord_3059951
  simp only [CollatzResearch.WordTrace]
  refine ⟨111605581737327599869755707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74403721158218399913170471 111605581737327599869755707)
  ·
    refine ⟨167408372605991399804633561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111605581737327599869755707 167408372605991399804633561)
    ·
      refine ⟨125556279454493549853475171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167408372605991399804633561 125556279454493549853475171)
      ·
        refine ⟨188334419181740324780212757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125556279454493549853475171 188334419181740324780212757)
        ·
          refine ⟨8828175899144077724072473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188334419181740324780212757 8828175899144077724072473)
          ·
            refine ⟨6621131924358058293054355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828175899144077724072473 6621131924358058293054355)
            ·
              refine ⟨9931697886537087439581533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621131924358058293054355 9931697886537087439581533)
              ·
                refine ⟨3724386707451407789843075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9931697886537087439581533 3724386707451407789843075)
                ·
                  refine ⟨5586580061177111684764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724386707451407789843075 5586580061177111684764613)
                  ·
                    refine ⟨1047483761470708440893365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586580061177111684764613 1047483761470708440893365)
                    ·
                      rfl

theorem cell22_3059951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_3059951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059951 prefixEnd_3059951 := by exact prefixLift 3059951
  have htrace : WordTrace (prefixWord ++ tailWord_3059951) baseStart_3059951 baseEnd_3059951 := by
    simpa [prefixWord, tailWord_3059951, baseEnd_3059951] using wordTrace_append hprefix tailTrace_3059951
  have hstable : (prefixWord ++ tailWord_3059951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059951).length < 2 ^ (prefixWord ++ tailWord_3059951).sum := by decide
  have hdescent : baseEnd_3059951 < baseStart_3059951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059966 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3059966 : Nat := 118140960795 + 3059966 * 2 ^ 59
def prefixEnd_3059966 : Nat := 4983230072969 + 3 ^ 40 * 3059966 * 2
def baseEnd_3059966 : Nat := 349162965425751133922773

theorem tailTrace_3059966 : CollatzResearch.WordTrace tailWord_3059966 prefixEnd_3059966 349162965425751133922773 := by
  unfold tailWord_3059966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950766104034157178943969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74404085888182171621034501 13950766104034157178943969)
  ·
    refine ⟨10463074578025617884207977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13950766104034157178943969 10463074578025617884207977)
    ·
      refine ⟨7847305933519213413155983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463074578025617884207977 7847305933519213413155983)
      ·
        refine ⟨11770958900278820119733975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847305933519213413155983 11770958900278820119733975)
        ·
          refine ⟨17656438350418230179600963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11770958900278820119733975 17656438350418230179600963)
          ·
            refine ⟨26484657525627345269401445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17656438350418230179600963 26484657525627345269401445)
            ·
              refine ⟨4965873286055127238012771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26484657525627345269401445 4965873286055127238012771)
              ·
                refine ⟨7448809929082690857019157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965873286055127238012771 7448809929082690857019157)
                ·
                  refine ⟨349162965425751133922773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7448809929082690857019157 349162965425751133922773)
                  ·
                    rfl

theorem cell22_3059966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3059966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3059966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3059966 prefixEnd_3059966 := by exact prefixLift 3059966
  have htrace : WordTrace (prefixWord ++ tailWord_3059966) baseStart_3059966 baseEnd_3059966 := by
    simpa [prefixWord, tailWord_3059966, baseEnd_3059966] using wordTrace_append hprefix tailTrace_3059966
  have hstable : (prefixWord ++ tailWord_3059966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059966).length < 2 ^ (prefixWord ++ tailWord_3059966).sum := by decide
  have hdescent : baseEnd_3059966 < baseStart_3059966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060062 : List Nat := [4, 4, 2, 1, 2, 9]
def baseStart_3060062 : Nat := 118140960795 + 3060062 * 2 ^ 59
def prefixEnd_3060062 : Nat := 4983230072969 + 3 ^ 40 * 3060062 * 2
def baseEnd_3060062 : Nat := 12932367395544952486025

theorem tailTrace_3060062 : CollatzResearch.WordTrace tailWord_3060062 prefixEnd_3060062 12932367395544952486025 := by
  unfold tailWord_3060062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951203779990683228380805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74406420159950310551364293 13951203779990683228380805)
  ·
    refine ⟨2615850708748253105321401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13951203779990683228380805 2615850708748253105321401)
    ·
      refine ⟨1961888031561189828991051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2615850708748253105321401 1961888031561189828991051)
      ·
        refine ⟨2942832047341784743486577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961888031561189828991051 2942832047341784743486577)
        ·
          refine ⟨2207124035506338557614933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2942832047341784743486577 2207124035506338557614933)
          ·
            refine ⟨12932367395544952486025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2207124035506338557614933 12932367395544952486025)
            ·
              rfl

theorem cell22_3060062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 9].length) (baseStart_3060062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060062 prefixEnd_3060062 := by exact prefixLift 3060062
  have htrace : WordTrace (prefixWord ++ tailWord_3060062) baseStart_3060062 baseEnd_3060062 := by
    simpa [prefixWord, tailWord_3060062, baseEnd_3060062] using wordTrace_append hprefix tailTrace_3060062
  have hstable : (prefixWord ++ tailWord_3060062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060062).length < 2 ^ (prefixWord ++ tailWord_3060062).sum := by decide
  have hdescent : baseEnd_3060062 < baseStart_3060062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060120 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_3060120 : Nat := 118140960795 + 3060120 * 2 ^ 59
def prefixEnd_3060120 : Nat := 4983230072969 + 3 ^ 40 * 3060120 * 2
def baseEnd_3060120 : Nat := 1047541613624448333417847

theorem tailTrace_3060120 : CollatzResearch.WordTrace tailWord_3060120 prefixEnd_3060120 1047541613624448333417847 := by
  unfold tailWord_3060120
  simp only [CollatzResearch.WordTrace]
  refine ⟨55805872836857670866328907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74407830449143561155105209 55805872836857670866328907)
  ·
    refine ⟨83708809255286506299493361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55805872836857670866328907 83708809255286506299493361)
    ·
      refine ⟨62781606941464879724620021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83708809255286506299493361 62781606941464879724620021)
      ·
        refine ⟨5885775650762332474183127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62781606941464879724620021 5885775650762332474183127)
        ·
          refine ⟨8828663476143498711274691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885775650762332474183127 8828663476143498711274691)
          ·
            refine ⟨13242995214215248066912037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828663476143498711274691 13242995214215248066912037)
            ·
              refine ⟨2483061602665359012546007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13242995214215248066912037 2483061602665359012546007)
              ·
                refine ⟨3724592403998038518819011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483061602665359012546007 3724592403998038518819011)
                ·
                  refine ⟨5586888605997057778228517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724592403998038518819011 5586888605997057778228517)
                  ·
                    refine ⟨1047541613624448333417847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586888605997057778228517 1047541613624448333417847)
                    ·
                      rfl

theorem cell22_3060120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_3060120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060120 prefixEnd_3060120 := by exact prefixLift 3060120
  have htrace : WordTrace (prefixWord ++ tailWord_3060120) baseStart_3060120 baseEnd_3060120 := by
    simpa [prefixWord, tailWord_3060120, baseEnd_3060120] using wordTrace_append hprefix tailTrace_3060120
  have hstable : (prefixWord ++ tailWord_3060120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060120).length < 2 ^ (prefixWord ++ tailWord_3060120).sum := by decide
  have hdescent : baseEnd_3060120 < baseStart_3060120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060191 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 7]
def baseStart_3060191 : Nat := 118140960795 + 3060191 * 2 ^ 59
def prefixEnd_3060191 : Nat := 4983230072969 + 3 ^ 40 * 3060191 * 2
def baseEnd_3060191 : Nat := 349188639458475938297543

theorem tailTrace_3060191 : CollatzResearch.WordTrace tailWord_3060191 prefixEnd_3060191 349188639458475938297543 := by
  unfold tailWord_3060191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111614335256458120858492427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74409556837638747238994951 111614335256458120858492427)
  ·
    refine ⟨167421502884687181287738641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111614335256458120858492427 167421502884687181287738641)
    ·
      refine ⟨125566127163515385965803981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167421502884687181287738641 125566127163515385965803981)
      ·
        refine ⟨47087297686318269737176493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125566127163515385965803981 47087297686318269737176493)
        ·
          refine ⟨17657736632369351151441185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47087297686318269737176493 17657736632369351151441185)
          ·
            refine ⟨13243302474277013363580889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17657736632369351151441185 13243302474277013363580889)
            ·
              refine ⟨9932476855707760022685667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13243302474277013363580889 9932476855707760022685667)
              ·
                refine ⟨14898715283561640034028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932476855707760022685667 14898715283561640034028501)
                ·
                  refine ⟨349188639458475938297543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14898715283561640034028501 349188639458475938297543)
                  ·
                    rfl

theorem cell22_3060191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_3060191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060191 prefixEnd_3060191 := by exact prefixLift 3060191
  have htrace : WordTrace (prefixWord ++ tailWord_3060191) baseStart_3060191 baseEnd_3060191 := by
    simpa [prefixWord, tailWord_3060191, baseEnd_3060191] using wordTrace_append hprefix tailTrace_3060191
  have hstable : (prefixWord ++ tailWord_3060191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060191).length < 2 ^ (prefixWord ++ tailWord_3060191).sum := by decide
  have hdescent : baseEnd_3060191 < baseStart_3060191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060270 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_3060270 : Nat := 118140960795 + 3060270 * 2 ^ 59
def prefixEnd_3060270 : Nat := 4983230072969 + 3 ^ 40 * 3060270 * 2
def baseEnd_3060270 : Nat := 349197653896632647389129

theorem tailTrace_3060270 : CollatzResearch.WordTrace tailWord_3060270 prefixEnd_3060270 349197653896632647389129 := by
  unfold tailWord_3060270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952152077896489668827283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74411477748781278233745509 13952152077896489668827283)
  ·
    refine ⟨20928228116844734503240925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13952152077896489668827283 20928228116844734503240925)
    ·
      refine ⟨7848085543816775438715347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20928228116844734503240925 7848085543816775438715347)
      ·
        refine ⟨11772128315725163158073021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848085543816775438715347 11772128315725163158073021)
        ·
          refine ⟨4414548118396936184277383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11772128315725163158073021 4414548118396936184277383)
          ·
            refine ⟨6621822177595404276416075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414548118396936184277383 6621822177595404276416075)
            ·
              refine ⟨9932733266393106414624113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621822177595404276416075 9932733266393106414624113)
              ·
                refine ⟨7449549949794829810968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9932733266393106414624113 7449549949794829810968085)
                ·
                  refine ⟨349197653896632647389129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7449549949794829810968085 349197653896632647389129)
                  ·
                    rfl

theorem cell22_3060270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_3060270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060270 prefixEnd_3060270 := by exact prefixLift 3060270
  have htrace : WordTrace (prefixWord ++ tailWord_3060270) baseStart_3060270 baseEnd_3060270 := by
    simpa [prefixWord, tailWord_3060270, baseEnd_3060270] using wordTrace_append hprefix tailTrace_3060270
  have hstable : (prefixWord ++ tailWord_3060270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060270).length < 2 ^ (prefixWord ++ tailWord_3060270).sum := by decide
  have hdescent : baseEnd_3060270 < baseStart_3060270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060296 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3060296 : Nat := 118140960795 + 3060296 * 2 ^ 59
def prefixEnd_3060296 : Nat := 4983230072969 + 3 ^ 40 * 3060296 * 2
def baseEnd_3060296 : Nat := 1047601862021242541017307

theorem tailTrace_3060296 : CollatzResearch.WordTrace tailWord_3060296 prefixEnd_3060296 1047601862021242541017307 := by
  unfold tailWord_3060296
  simp only [CollatzResearch.WordTrace]
  refine ⟨55809082460538861895532371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74412109947385149194043161 55809082460538861895532371)
  ·
    refine ⟨83713623690808292843298557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55809082460538861895532371 83713623690808292843298557)
    ·
      refine ⟨31392608884053109816236959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83713623690808292843298557 31392608884053109816236959)
      ·
        refine ⟨47088913326079664724355439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31392608884053109816236959 47088913326079664724355439)
        ·
          refine ⟨70633369989119497086533159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47088913326079664724355439 70633369989119497086533159)
          ·
            refine ⟨105950054983679245629799739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70633369989119497086533159 105950054983679245629799739)
            ·
              refine ⟨158925082475518868444699609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105950054983679245629799739 158925082475518868444699609)
              ·
                refine ⟨119193811856639151333524707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158925082475518868444699609 119193811856639151333524707)
                ·
                  refine ⟨178790717784958727000287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119193811856639151333524707 178790717784958727000287061)
                  ·
                    refine ⟨1047601862021242541017307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178790717784958727000287061 1047601862021242541017307)
                    ·
                      rfl

theorem cell22_3060296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3060296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060296 prefixEnd_3060296 := by exact prefixLift 3060296
  have htrace : WordTrace (prefixWord ++ tailWord_3060296) baseStart_3060296 baseEnd_3060296 := by
    simpa [prefixWord, tailWord_3060296, baseEnd_3060296] using wordTrace_append hprefix tailTrace_3060296
  have hstable : (prefixWord ++ tailWord_3060296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060296).length < 2 ^ (prefixWord ++ tailWord_3060296).sum := by decide
  have hdescent : baseEnd_3060296 < baseStart_3060296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060330 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3060330 : Nat := 118140960795 + 3060330 * 2 ^ 59
def prefixEnd_3060330 : Nat := 4983230072969 + 3 ^ 40 * 3060330 * 2
def baseEnd_3060330 : Nat := 1047613500916077785667203

theorem tailTrace_3060330 : CollatzResearch.WordTrace tailWord_3060330 prefixEnd_3060330 1047613500916077785667203 := by
  unfold tailWord_3060330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904851250738636899450611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74412936668636365065201629 27904851250738636899450611)
  ·
    refine ⟨41857276876107955349175917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904851250738636899450611 41857276876107955349175917)
    ·
      refine ⟨15696478828540483255940969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41857276876107955349175917 15696478828540483255940969)
      ·
        refine ⟨11772359121405362441955727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15696478828540483255940969 11772359121405362441955727)
        ·
          refine ⟨17658538682108043662933591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772359121405362441955727 17658538682108043662933591)
          ·
            refine ⟨26487808023162065494400387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17658538682108043662933591 26487808023162065494400387)
            ·
              refine ⟨39731712034743098241600581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26487808023162065494400387 39731712034743098241600581)
              ·
                refine ⟨7449696006514330920300109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39731712034743098241600581 7449696006514330920300109)
                ·
                  refine ⟨2793636002442874095112541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7449696006514330920300109 2793636002442874095112541)
                  ·
                    refine ⟨1047613500916077785667203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2793636002442874095112541 1047613500916077785667203)
                    ·
                      rfl

theorem cell22_3060330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3060330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060330 prefixEnd_3060330 := by exact prefixLift 3060330
  have htrace : WordTrace (prefixWord ++ tailWord_3060330) baseStart_3060330 baseEnd_3060330 := by
    simpa [prefixWord, tailWord_3060330, baseEnd_3060330] using wordTrace_append hprefix tailTrace_3060330
  have hstable : (prefixWord ++ tailWord_3060330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060330).length < 2 ^ (prefixWord ++ tailWord_3060330).sum := by decide
  have hdescent : baseEnd_3060330 < baseStart_3060330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060388 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3060388 : Nat := 118140960795 + 3060388 * 2 ^ 59
def prefixEnd_3060388 : Nat := 4983230072969 + 3 ^ 40 * 3060388 * 2
def baseEnd_3060388 : Nat := 349211118500461655905675

theorem tailTrace_3060388 : CollatzResearch.WordTrace tailWord_3060388 prefixEnd_3060388 349211118500461655905675 := by
  unfold tailWord_3060388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55810760218372211751706909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74414346957829615668942545 55810760218372211751706909)
  ·
    refine ⟨20929035081889579406890091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55810760218372211751706909 20929035081889579406890091)
    ·
      refine ⟨31393552622834369110335137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20929035081889579406890091 31393552622834369110335137)
      ·
        refine ⟨23545164467125776832751353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31393552622834369110335137 23545164467125776832751353)
        ·
          refine ⟨17658873350344332624563515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23545164467125776832751353 17658873350344332624563515)
          ·
            refine ⟨26488310025516498936845273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17658873350344332624563515 26488310025516498936845273)
            ·
              refine ⟨19866232519137374202633955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26488310025516498936845273 19866232519137374202633955)
              ·
                refine ⟨29799348778706061303950933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866232519137374202633955 29799348778706061303950933)
                ·
                  refine ⟨349211118500461655905675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29799348778706061303950933 349211118500461655905675)
                  ·
                    rfl

theorem cell22_3060388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3060388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060388 prefixEnd_3060388 := by exact prefixLift 3060388
  have htrace : WordTrace (prefixWord ++ tailWord_3060388) baseStart_3060388 baseEnd_3060388 := by
    simpa [prefixWord, tailWord_3060388, baseEnd_3060388] using wordTrace_append hprefix tailTrace_3060388
  have hstable : (prefixWord ++ tailWord_3060388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060388).length < 2 ^ (prefixWord ++ tailWord_3060388).sum := by decide
  have hdescent : baseEnd_3060388 < baseStart_3060388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060403 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_3060403 : Nat := 118140960795 + 3060403 * 2 ^ 59
def prefixEnd_3060403 : Nat := 4983230072969 + 3 ^ 40 * 3060403 * 2
def baseEnd_3060403 : Nat := 1047638490307929928591979

theorem tailTrace_3060403 : CollatzResearch.WordTrace tailWord_3060403 prefixEnd_3060403 1047638490307929928591979 := by
  unfold tailWord_3060403
  simp only [CollatzResearch.WordTrace]
  refine ⟨111622067531690081065209863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74414711687793387376806575 111622067531690081065209863)
  ·
    refine ⟨167433101297535121597814795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111622067531690081065209863 167433101297535121597814795)
    ·
      refine ⟨251149651946302682396722193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167433101297535121597814795 251149651946302682396722193)
      ·
        refine ⟨188362238959727011797541645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251149651946302682396722193 188362238959727011797541645)
        ·
          refine ⟨70635839609897629424078117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188362238959727011797541645 70635839609897629424078117)
          ·
            refine ⟨13244219926855805517014647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70635839609897629424078117 13244219926855805517014647)
            ·
              refine ⟨19866329890283708275521971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244219926855805517014647 19866329890283708275521971)
              ·
                refine ⟨29799494835425562413282957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866329890283708275521971 29799494835425562413282957)
                ·
                  refine ⟨11174810563284585904981109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29799494835425562413282957 11174810563284585904981109)
                  ·
                    refine ⟨1047638490307929928591979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11174810563284585904981109 1047638490307929928591979)
                    ·
                      rfl

theorem cell22_3060403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_3060403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060403 prefixEnd_3060403 := by exact prefixLift 3060403
  have htrace : WordTrace (prefixWord ++ tailWord_3060403) baseStart_3060403 baseEnd_3060403 := by
    simpa [prefixWord, tailWord_3060403, baseEnd_3060403] using wordTrace_append hprefix tailTrace_3060403
  have hstable : (prefixWord ++ tailWord_3060403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060403).length < 2 ^ (prefixWord ++ tailWord_3060403).sum := by decide
  have hdescent : baseEnd_3060403 < baseStart_3060403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060452 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_3060452 : Nat := 118140960795 + 3060452 * 2 ^ 59
def prefixEnd_3060452 : Nat := 4983230072969 + 3 ^ 40 * 3060452 * 2
def baseEnd_3060452 : Nat := 1047655264009310134116829

theorem tailTrace_3060452 : CollatzResearch.WordTrace tailWord_3060452 prefixEnd_3060452 1047655264009310134116829 := by
  unfold tailWord_3060452
  simp only [CollatzResearch.WordTrace]
  refine ⟨55811927354256281216871805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74415903139008374955829073 55811927354256281216871805)
  ·
    refine ⟨20929472757846105456326927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55811927354256281216871805 20929472757846105456326927)
    ·
      refine ⟨31394209136769158184490391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20929472757846105456326927 31394209136769158184490391)
      ·
        refine ⟨47091313705153737276735587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31394209136769158184490391 47091313705153737276735587)
        ·
          refine ⟨70636970557730605915103381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47091313705153737276735587 70636970557730605915103381)
          ·
            refine ⟨3311107994893622152270471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70636970557730605915103381 3311107994893622152270471)
            ·
              refine ⟨4966661992340433228405707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311107994893622152270471 4966661992340433228405707)
              ·
                refine ⟨7449992988510649842608561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966661992340433228405707 7449992988510649842608561)
                ·
                  refine ⟨5587494741382987381956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449992988510649842608561 5587494741382987381956421)
                  ·
                    refine ⟨1047655264009310134116829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5587494741382987381956421 1047655264009310134116829)
                    ·
                      rfl

theorem cell22_3060452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_3060452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060452 prefixEnd_3060452 := by exact prefixLift 3060452
  have htrace : WordTrace (prefixWord ++ tailWord_3060452) baseStart_3060452 baseEnd_3060452 := by
    simpa [prefixWord, tailWord_3060452, baseEnd_3060452] using wordTrace_append hprefix tailTrace_3060452
  have hstable : (prefixWord ++ tailWord_3060452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060452).length < 2 ^ (prefixWord ++ tailWord_3060452).sum := by decide
  have hdescent : baseEnd_3060452 < baseStart_3060452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060465 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_3060465 : Nat := 118140960795 + 3060465 * 2 ^ 59
def prefixEnd_3060465 : Nat := 4983230072969 + 3 ^ 40 * 3060465 * 2
def baseEnd_3060465 : Nat := 1047659714174982433541789

theorem tailTrace_3060465 : CollatzResearch.WordTrace tailWord_3060465 prefixEnd_3060465 1047659714174982433541789 := by
  unfold tailWord_3060465
  simp only [CollatzResearch.WordTrace]
  refine ⟨111624328857465465653966849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74416219238310310435977899 111624328857465465653966849)
  ·
    refine ⟨83718246643099099240475137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111624328857465465653966849 83718246643099099240475137)
    ·
      refine ⟨62788684982324324430356353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83718246643099099240475137 62788684982324324430356353)
      ·
        refine ⟨47091513736743243322767265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62788684982324324430356353 47091513736743243322767265)
        ·
          refine ⟨35318635302557432492075449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47091513736743243322767265 35318635302557432492075449)
          ·
            refine ⟨26488976476918074369056587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35318635302557432492075449 26488976476918074369056587)
            ·
              refine ⟨39733464715377111553584881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26488976476918074369056587 39733464715377111553584881)
              ·
                refine ⟨29800098536532833665188661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39733464715377111553584881 29800098536532833665188661)
                ·
                  refine ⟨2793759237799953156111437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29800098536532833665188661 2793759237799953156111437)
                  ·
                    refine ⟨1047659714174982433541789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2793759237799953156111437 1047659714174982433541789)
                    ·
                      rfl

theorem cell22_3060465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_3060465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060465 prefixEnd_3060465 := by exact prefixLift 3060465
  have htrace : WordTrace (prefixWord ++ tailWord_3060465) baseStart_3060465 baseEnd_3060465 := by
    simpa [prefixWord, tailWord_3060465, baseEnd_3060465] using wordTrace_append hprefix tailTrace_3060465
  have hstable : (prefixWord ++ tailWord_3060465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060465).length < 2 ^ (prefixWord ++ tailWord_3060465).sum := by decide
  have hdescent : baseEnd_3060465 < baseStart_3060465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060523 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 10]
def baseStart_3060523 : Nat := 118140960795 + 3060523 * 2 ^ 59
def prefixEnd_3060523 : Nat := 4983230072969 + 3 ^ 40 * 3060523 * 2
def baseEnd_3060523 : Nat := 349226522920096538530537

theorem tailTrace_3060523 : CollatzResearch.WordTrace tailWord_3060523 prefixEnd_3060523 349226522920096538530537 := by
  unfold tailWord_3060523
  simp only [CollatzResearch.WordTrace]
  refine ⟨111626444291255341559578223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74417629527503561039718815 111626444291255341559578223)
  ·
    refine ⟨167439666436883012339367335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111626444291255341559578223 167439666436883012339367335)
    ·
      refine ⟨251159499655324518509051003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167439666436883012339367335 251159499655324518509051003)
      ·
        refine ⟨376739249482986777763576505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251159499655324518509051003 376739249482986777763576505)
        ·
          refine ⟨282554437112240083322682379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376739249482986777763576505 282554437112240083322682379)
          ·
            refine ⟨423831655668360124984023569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282554437112240083322682379 423831655668360124984023569)
            ·
              refine ⟨317873741751270093738017677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423831655668360124984023569 317873741751270093738017677)
              ·
                refine ⟨119202653156726285151756629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317873741751270093738017677 119202653156726285151756629)
                ·
                  refine ⟨349226522920096538530537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119202653156726285151756629 349226522920096538530537)
                  ·
                    rfl

theorem cell22_3060523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_3060523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060523 prefixEnd_3060523 := by exact prefixLift 3060523
  have htrace : WordTrace (prefixWord ++ tailWord_3060523) baseStart_3060523 baseEnd_3060523 := by
    simpa [prefixWord, tailWord_3060523, baseEnd_3060523] using wordTrace_append hprefix tailTrace_3060523
  have hstable : (prefixWord ++ tailWord_3060523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060523).length < 2 ^ (prefixWord ++ tailWord_3060523).sum := by decide
  have hdescent : baseEnd_3060523 < baseStart_3060523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060572 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3060572 : Nat := 118140960795 + 3060572 * 2 ^ 59
def prefixEnd_3060572 : Nat := 4983230072969 + 3 ^ 40 * 3060572 * 2
def baseEnd_3060572 : Nat := 1047696342461669821116461

theorem tailTrace_3060572 : CollatzResearch.WordTrace tailWord_3060572 prefixEnd_3060572 1047696342461669821116461 := by
  unfold tailWord_3060572
  simp only [CollatzResearch.WordTrace]
  refine ⟨55814115734038911464055985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74418820978718548618741313 55814115734038911464055985)
  ·
    refine ⟨41860586800529183598041989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55814115734038911464055985 41860586800529183598041989)
    ·
      refine ⟨7848860025099221924632873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41860586800529183598041989 7848860025099221924632873)
      ·
        refine ⟨5886645018824416443474655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7848860025099221924632873 5886645018824416443474655)
        ·
          refine ⟨8829967528236624665211983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886645018824416443474655 8829967528236624665211983)
          ·
            refine ⟨13244951292354936997817975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829967528236624665211983 13244951292354936997817975)
            ·
              refine ⟨19867426938532405496726963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244951292354936997817975 19867426938532405496726963)
              ·
                refine ⟨29801140407798608245090445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19867426938532405496726963 29801140407798608245090445)
                ·
                  refine ⟨11175427652924478091908917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29801140407798608245090445 11175427652924478091908917)
                  ·
                    refine ⟨1047696342461669821116461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11175427652924478091908917 1047696342461669821116461)
                    ·
                      rfl

theorem cell22_3060572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3060572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3060572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3060572 prefixEnd_3060572 := by exact prefixLift 3060572
  have htrace : WordTrace (prefixWord ++ tailWord_3060572) baseStart_3060572 baseEnd_3060572 := by
    simpa [prefixWord, tailWord_3060572, baseEnd_3060572] using wordTrace_append hprefix tailTrace_3060572
  have hstable : (prefixWord ++ tailWord_3060572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060572).length < 2 ^ (prefixWord ++ tailWord_3060572).sum := by decide
  have hdescent : baseEnd_3060572 < baseStart_3060572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
