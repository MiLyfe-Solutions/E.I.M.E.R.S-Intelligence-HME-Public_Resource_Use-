import V185TrunkScan22Chunk360

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3220965 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3220965 : Nat := 118140960795 + 3220965 * 2 ^ 59
def prefixEnd_3220965 : Nat := 4983230072969 + 3 ^ 40 * 3220965 * 2
def baseEnd_3220965 : Nat := 1102602144206063795549705

theorem tailTrace_3220965 : CollatzResearch.WordTrace tailWord_3220965 prefixEnd_3220965 1102602144206063795549705 := by
  unfold tailWord_3220965
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478244776001376871648349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78318829850667584581098899 117478244776001376871648349)
  ·
    refine ⟨44054341791000516326868131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117478244776001376871648349 44054341791000516326868131)
    ·
      refine ⟨66081512686500774490302197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44054341791000516326868131 66081512686500774490302197)
      ·
        refine ⟨6195141814359447608465831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66081512686500774490302197 6195141814359447608465831)
        ·
          refine ⟨9292712721539171412698747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195141814359447608465831 9292712721539171412698747)
          ·
            refine ⟨13939069082308757119048121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9292712721539171412698747 13939069082308757119048121)
            ·
              refine ⟨10454301811731567839286091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13939069082308757119048121 10454301811731567839286091)
              ·
                refine ⟨15681452717597351758929137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10454301811731567839286091 15681452717597351758929137)
                ·
                  refine ⟨11761089538198013819196853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15681452717597351758929137 11761089538198013819196853)
                  ·
                    refine ⟨1102602144206063795549705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11761089538198013819196853 1102602144206063795549705)
                    ·
                      rfl

theorem cell22_3220965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3220965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220965 prefixEnd_3220965 := by exact prefixLift 3220965
  have htrace : WordTrace (prefixWord ++ tailWord_3220965) baseStart_3220965 baseEnd_3220965 := by
    simpa [prefixWord, tailWord_3220965, baseEnd_3220965] using wordTrace_append hprefix tailTrace_3220965
  have hstable : (prefixWord ++ tailWord_3220965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220965).length < 2 ^ (prefixWord ++ tailWord_3220965).sum := by decide
  have hdescent : baseEnd_3220965 < baseStart_3220965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220967 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 5]
def baseStart_3220967 : Nat := 118140960795 + 3220967 * 2 ^ 59
def prefixEnd_3220967 : Nat := 4983230072969 + 3 ^ 40 * 3220967 * 2
def baseEnd_3220967 : Nat := 367534276282312152333233

theorem tailTrace_3220967 : CollatzResearch.WordTrace tailWord_3220967 prefixEnd_3220967 367534276282312152333233 := by
  unfold tailWord_3220967
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478317721994131213221155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78318878481329420808814103 117478317721994131213221155)
  ·
    refine ⟨176217476582991196819831733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117478317721994131213221155 176217476582991196819831733)
    ·
      refine ⟨16520388429655424701859225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176217476582991196819831733 16520388429655424701859225)
      ·
        refine ⟨12390291322241568526394419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16520388429655424701859225 12390291322241568526394419)
        ·
          refine ⟨18585436983362352789591629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390291322241568526394419 18585436983362352789591629)
          ·
            refine ⟨6969538868760882296096861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18585436983362352789591629 6969538868760882296096861)
            ·
              refine ⟨2613577075785330861036323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6969538868760882296096861 2613577075785330861036323)
              ·
                refine ⟨3920365613677996291554485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613577075785330861036323 3920365613677996291554485)
                ·
                  refine ⟨367534276282312152333233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3920365613677996291554485 367534276282312152333233)
                  ·
                    rfl

theorem cell22_3220967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 5].length) (baseStart_3220967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220967 prefixEnd_3220967 := by exact prefixLift 3220967
  have htrace : WordTrace (prefixWord ++ tailWord_3220967) baseStart_3220967 baseEnd_3220967 := by
    simpa [prefixWord, tailWord_3220967, baseEnd_3220967] using wordTrace_append hprefix tailTrace_3220967
  have hstable : (prefixWord ++ tailWord_3220967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220967).length < 2 ^ (prefixWord ++ tailWord_3220967).sum := by decide
  have hdescent : baseEnd_3220967 < baseStart_3220967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220995 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 4]
def baseStart_3220995 : Nat := 118140960795 + 3220995 * 2 ^ 59
def prefixEnd_3220995 : Nat := 4983230072969 + 3 ^ 40 * 3220995 * 2
def baseEnd_3220995 : Nat := 367537471273051239099871

theorem tailTrace_3220995 : CollatzResearch.WordTrace tailWord_3220995 prefixEnd_3220995 367537471273051239099871 := by
  unfold tailWord_3220995
  simp only [CollatzResearch.WordTrace]
  refine ⟨117479338965892691995240439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78319559310595127996826959 117479338965892691995240439)
  ·
    refine ⟨176219008448839037992860659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117479338965892691995240439 176219008448839037992860659)
    ·
      refine ⟨264328512673258556989290989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176219008448839037992860659 264328512673258556989290989)
      ·
        refine ⟨99123192252471958870984121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264328512673258556989290989 99123192252471958870984121)
        ·
          refine ⟨74342394189353969153238091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99123192252471958870984121 74342394189353969153238091)
          ·
            refine ⟨111513591284030953729857137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74342394189353969153238091 111513591284030953729857137)
            ·
              refine ⟨83635193463023215297392853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111513591284030953729857137 83635193463023215297392853)
              ·
                refine ⟨1960199846789606608532645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83635193463023215297392853 1960199846789606608532645)
                ·
                  refine ⟨367537471273051239099871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960199846789606608532645 367537471273051239099871)
                  ·
                    rfl

theorem cell22_3220995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 4].length) (baseStart_3220995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220995 prefixEnd_3220995 := by exact prefixLift 3220995
  have htrace : WordTrace (prefixWord ++ tailWord_3220995) baseStart_3220995 baseEnd_3220995 := by
    simpa [prefixWord, tailWord_3220995, baseEnd_3220995] using wordTrace_append hprefix tailTrace_3220995
  have hstable : (prefixWord ++ tailWord_3220995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220995).length < 2 ^ (prefixWord ++ tailWord_3220995).sum := by decide
  have hdescent : baseEnd_3220995 < baseStart_3220995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221005 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3221005 : Nat := 118140960795 + 3221005 * 2 ^ 59
def prefixEnd_3221005 : Nat := 4983230072969 + 3 ^ 40 * 3221005 * 2
def baseEnd_3221005 : Nat := 1102615837023517024549583

theorem tailTrace_3221005 : CollatzResearch.WordTrace tailWord_3221005 prefixEnd_3221005 1102615837023517024549583 := by
  unfold tailWord_3221005
  simp only [CollatzResearch.WordTrace]
  refine ⟨117479703695856463703104469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78319802463904309135402979 117479703695856463703104469)
  ·
    refine ⟨2753430555371635868041511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117479703695856463703104469 2753430555371635868041511)
    ·
      refine ⟨4130145833057453802062267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2753430555371635868041511 4130145833057453802062267)
      ·
        refine ⟨6195218749586180703093401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130145833057453802062267 6195218749586180703093401)
        ·
          refine ⟨4646414062189635527320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195218749586180703093401 4646414062189635527320051)
          ·
            refine ⟨6969621093284453290980077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646414062189635527320051 6969621093284453290980077)
            ·
              refine ⟨2613607909981669984117529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6969621093284453290980077 2613607909981669984117529)
              ·
                refine ⟨1960205932486252488088147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613607909981669984117529 1960205932486252488088147)
                ·
                  refine ⟨2940308898729378732132221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960205932486252488088147 2940308898729378732132221)
                  ·
                    refine ⟨1102615837023517024549583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940308898729378732132221 1102615837023517024549583)
                    ·
                      rfl

theorem cell22_3221005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3221005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221005 prefixEnd_3221005 := by exact prefixLift 3221005
  have htrace : WordTrace (prefixWord ++ tailWord_3221005) baseStart_3221005 baseEnd_3221005 := by
    simpa [prefixWord, tailWord_3221005, baseEnd_3221005] using wordTrace_append hprefix tailTrace_3221005
  have hstable : (prefixWord ++ tailWord_3221005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221005).length < 2 ^ (prefixWord ++ tailWord_3221005).sum := by decide
  have hdescent : baseEnd_3221005 < baseStart_3221005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221023 : List Nat := [1, 1, 2, 4, 1, 1, 3, 9]
def baseStart_3221023 : Nat := 118140960795 + 3221023 * 2 ^ 59
def prefixEnd_3221023 : Nat := 4983230072969 + 3 ^ 40 * 3221023 * 2
def baseEnd_3221023 : Nat := 122513555421263441955503

theorem tailTrace_3221023 : CollatzResearch.WordTrace tailWord_3221023 prefixEnd_3221023 122513555421263441955503 := by
  unfold tailWord_3221023
  simp only [CollatzResearch.WordTrace]
  refine ⟨117480360209791252777259723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78320240139860835184839815 117480360209791252777259723)
  ·
    refine ⟨176220540314686879165889585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117480360209791252777259723 176220540314686879165889585)
    ·
      refine ⟨132165405236015159374417189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176220540314686879165889585 132165405236015159374417189)
      ·
        refine ⟨24781013481752842382703223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132165405236015159374417189 24781013481752842382703223)
        ·
          refine ⟨37171520222629263574054835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24781013481752842382703223 37171520222629263574054835)
          ·
            refine ⟨55757280333943895361082253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37171520222629263574054835 55757280333943895361082253)
            ·
              refine ⟨20908980125228960760405845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55757280333943895361082253 20908980125228960760405845)
              ·
                refine ⟨122513555421263441955503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20908980125228960760405845 122513555421263441955503)
                ·
                  rfl

theorem cell22_3221023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 9].length) (baseStart_3221023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221023 prefixEnd_3221023 := by exact prefixLift 3221023
  have htrace : WordTrace (prefixWord ++ tailWord_3221023) baseStart_3221023 baseEnd_3221023 := by
    simpa [prefixWord, tailWord_3221023, baseEnd_3221023] using wordTrace_append hprefix tailTrace_3221023
  have hstable : (prefixWord ++ tailWord_3221023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221023).length < 2 ^ (prefixWord ++ tailWord_3221023).sum := by decide
  have hdescent : baseEnd_3221023 < baseStart_3221023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221106 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_3221106 : Nat := 118140960795 + 3221106 * 2 ^ 59
def prefixEnd_3221106 : Nat := 4983230072969 + 3 ^ 40 * 3221106 * 2
def baseEnd_3221106 : Nat := 1102650411387586427774273

theorem tailTrace_3221106 : CollatzResearch.WordTrace tailWord_3221106 prefixEnd_3221106 1102650411387586427774273 := by
  unfold tailWord_3221106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29370846867122639488132793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78322258312327038635020781 29370846867122639488132793)
  ·
    refine ⟨22028135150341979616099595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29370846867122639488132793 22028135150341979616099595)
    ·
      refine ⟨33042202725512969424149393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22028135150341979616099595 33042202725512969424149393)
      ·
        refine ⟨24781652044134727068112045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33042202725512969424149393 24781652044134727068112045)
        ·
          refine ⟨9293119516550522650542017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24781652044134727068112045 9293119516550522650542017)
          ·
            refine ⟨6969839637412891987906513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293119516550522650542017 6969839637412891987906513)
            ·
              refine ⟨5227379728059668990929885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969839637412891987906513 5227379728059668990929885)
              ·
                refine ⟨1960267398022375871598707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5227379728059668990929885 1960267398022375871598707)
                ·
                  refine ⟨2940401097033563807398061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960267398022375871598707 2940401097033563807398061)
                  ·
                    refine ⟨1102650411387586427774273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940401097033563807398061 1102650411387586427774273)
                    ·
                      rfl

theorem cell22_3221106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_3221106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221106 prefixEnd_3221106 := by exact prefixLift 3221106
  have htrace : WordTrace (prefixWord ++ tailWord_3221106) baseStart_3221106 baseEnd_3221106 := by
    simpa [prefixWord, tailWord_3221106, baseEnd_3221106] using wordTrace_append hprefix tailTrace_3221106
  have hstable : (prefixWord ++ tailWord_3221106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221106).length < 2 ^ (prefixWord ++ tailWord_3221106).sum := by decide
  have hdescent : baseEnd_3221106 < baseStart_3221106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221145 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3221145 : Nat := 118140960795 + 3221145 * 2 ^ 59
def prefixEnd_3221145 : Nat := 4983230072969 + 3 ^ 40 * 3221145 * 2
def baseEnd_3221145 : Nat := 1102663761884603326049153

theorem tailTrace_3221145 : CollatzResearch.WordTrace tailWord_3221145 prefixEnd_3221145 1102663761884603326049153 := by
  unfold tailWord_3221145
  simp only [CollatzResearch.WordTrace]
  refine ⟨117484809915349267613200889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78323206610232845075467259 117484809915349267613200889)
  ·
    refine ⟨88113607436511950709900667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117484809915349267613200889 88113607436511950709900667)
    ·
      refine ⟨132170411154767926064851001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88113607436511950709900667 132170411154767926064851001)
      ·
        refine ⟨99127808366075944548638251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132170411154767926064851001 99127808366075944548638251)
        ·
          refine ⟨148691712549113916822957377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99127808366075944548638251 148691712549113916822957377)
          ·
            refine ⟨111518784411835437617218033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148691712549113916822957377 111518784411835437617218033)
            ·
              refine ⟨83639088308876578212913525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111518784411835437617218033 83639088308876578212913525)
              ·
                refine ⟨7841164528957179207460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83639088308876578212913525 7841164528957179207460643)
                ·
                  refine ⟨11761746793435768811190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841164528957179207460643 11761746793435768811190965)
                  ·
                    refine ⟨1102663761884603326049153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11761746793435768811190965 1102663761884603326049153)
                    ·
                      rfl

theorem cell22_3221145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3221145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221145 prefixEnd_3221145 := by exact prefixLift 3221145
  have htrace : WordTrace (prefixWord ++ tailWord_3221145) baseStart_3221145 baseEnd_3221145 := by
    simpa [prefixWord, tailWord_3221145, baseEnd_3221145] using wordTrace_append hprefix tailTrace_3221145
  have hstable : (prefixWord ++ tailWord_3221145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221145).length < 2 ^ (prefixWord ++ tailWord_3221145).sum := by decide
  have hdescent : baseEnd_3221145 < baseStart_3221145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221175 : List Nat := [1, 1, 3, 1, 5, 1, 10]
def baseStart_3221175 : Nat := 118140960795 + 3221175 * 2 ^ 59
def prefixEnd_3221175 : Nat := 4983230072969 + 3 ^ 40 * 3221175 * 2
def baseEnd_3221175 : Nat := 40839778944359009177743

theorem tailTrace_3221175 : CollatzResearch.WordTrace tailWord_3221175 prefixEnd_3221175 40839778944359009177743 := by
  unfold tailWord_3221175
  simp only [CollatzResearch.WordTrace]
  refine ⟨117485904105240582736792979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78323936070160388491195319 117485904105240582736792979)
  ·
    refine ⟨176228856157860874105189469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117485904105240582736792979 176228856157860874105189469)
    ·
      refine ⟨66085821059197827789446051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176228856157860874105189469 66085821059197827789446051)
      ·
        refine ⟨99128731588796741684169077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66085821059197827789446051 99128731588796741684169077)
        ·
          refine ⟨9293318586449694532890851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99128731588796741684169077 9293318586449694532890851)
          ·
            refine ⟨13939977879674541799336277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293318586449694532890851 13939977879674541799336277)
            ·
              refine ⟨40839778944359009177743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13939977879674541799336277 40839778944359009177743)
              ·
                rfl

theorem cell22_3221175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 10].length) (baseStart_3221175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221175 prefixEnd_3221175 := by exact prefixLift 3221175
  have htrace : WordTrace (prefixWord ++ tailWord_3221175) baseStart_3221175 baseEnd_3221175 := by
    simpa [prefixWord, tailWord_3221175, baseEnd_3221175] using wordTrace_append hprefix tailTrace_3221175
  have hstable : (prefixWord ++ tailWord_3221175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221175).length < 2 ^ (prefixWord ++ tailWord_3221175).sum := by decide
  have hdescent : baseEnd_3221175 < baseStart_3221175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221196 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_3221196 : Nat := 118140960795 + 3221196 * 2 ^ 59
def prefixEnd_3221196 : Nat := 4983230072969 + 3 ^ 40 * 3221196 * 2
def baseEnd_3221196 : Nat := 1102681220226856193023997

theorem tailTrace_3221196 : CollatzResearch.WordTrace tailWord_3221196 prefixEnd_3221196 1102681220226856193023997 := by
  unfold tailWord_3221196
  simp only [CollatzResearch.WordTrace]
  refine ⟨58743335019082251661653721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78324446692109668882204961 58743335019082251661653721)
  ·
    refine ⟨44057501264311688746240291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58743335019082251661653721 44057501264311688746240291)
    ·
      refine ⟨66086251896467533119360437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44057501264311688746240291 66086251896467533119360437)
      ·
        refine ⟨6195586115293831229940041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66086251896467533119360437 6195586115293831229940041)
        ·
          refine ⟨4646689586470373422455031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195586115293831229940041 4646689586470373422455031)
          ·
            refine ⟨6970034379705560133682547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646689586470373422455031 6970034379705560133682547)
            ·
              refine ⟨10455051569558340200523821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970034379705560133682547 10455051569558340200523821)
              ·
                refine ⟨3920644338584377575196433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10455051569558340200523821 3920644338584377575196433)
                ·
                  refine ⟨2940483253938283181397325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920644338584377575196433 2940483253938283181397325)
                  ·
                    refine ⟨1102681220226856193023997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940483253938283181397325 1102681220226856193023997)
                    ·
                      rfl

theorem cell22_3221196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_3221196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221196 prefixEnd_3221196 := by exact prefixLift 3221196
  have htrace : WordTrace (prefixWord ++ tailWord_3221196) baseStart_3221196 baseEnd_3221196 := by
    simpa [prefixWord, tailWord_3221196, baseEnd_3221196] using wordTrace_append hprefix tailTrace_3221196
  have hstable : (prefixWord ++ tailWord_3221196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221196).length < 2 ^ (prefixWord ++ tailWord_3221196).sum := by decide
  have hdescent : baseEnd_3221196 < baseStart_3221196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221207 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 5, 3]
def baseStart_3221207 : Nat := 118140960795 + 3221207 * 2 ^ 59
def prefixEnd_3221207 : Nat := 4983230072969 + 3 ^ 40 * 3221207 * 2
def baseEnd_3221207 : Nat := 1102684985751655830998963

theorem tailTrace_3221207 : CollatzResearch.WordTrace tailWord_3221207 prefixEnd_3221207 1102684985751655830998963 := by
  unfold tailWord_3221207
  simp only [CollatzResearch.WordTrace]
  refine ⟨117487071241124652201957875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78324714160749768134638583 117487071241124652201957875)
  ·
    refine ⟨176230606861686978302936813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117487071241124652201957875 176230606861686978302936813)
    ·
      refine ⟨66086477573132616863601305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176230606861686978302936813 66086477573132616863601305)
      ·
        refine ⟨49564858179849462647700979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66086477573132616863601305 49564858179849462647700979)
        ·
          refine ⟨74347287269774193971551469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49564858179849462647700979 74347287269774193971551469)
          ·
            refine ⟨27880232726165322739331801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74347287269774193971551469 27880232726165322739331801)
            ·
              refine ⟨20910174544623992054498851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27880232726165322739331801 20910174544623992054498851)
              ·
                refine ⟨31365261816935988081748277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20910174544623992054498851 31365261816935988081748277)
                ·
                  refine ⟨2940493295337748882663901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31365261816935988081748277 2940493295337748882663901)
                  ·
                    refine ⟨1102684985751655830998963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940493295337748882663901 1102684985751655830998963)
                    ·
                      rfl

theorem cell22_3221207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_3221207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221207 prefixEnd_3221207 := by exact prefixLift 3221207
  have htrace : WordTrace (prefixWord ++ tailWord_3221207) baseStart_3221207 baseEnd_3221207 := by
    simpa [prefixWord, tailWord_3221207, baseEnd_3221207] using wordTrace_append hprefix tailTrace_3221207
  have hstable : (prefixWord ++ tailWord_3221207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221207).length < 2 ^ (prefixWord ++ tailWord_3221207).sum := by decide
  have hdescent : baseEnd_3221207 < baseStart_3221207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221252 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3221252 : Nat := 118140960795 + 3221252 * 2 ^ 59
def prefixEnd_3221252 : Nat := 4983230072969 + 3 ^ 40 * 3221252 * 2
def baseEnd_3221252 : Nat := 1102700390171290713623825

theorem tailTrace_3221252 : CollatzResearch.WordTrace tailWord_3221252 prefixEnd_3221252 1102700390171290713623825 := by
  unfold tailWord_3221252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58744356262980812443673005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78325808350641083258230673 58744356262980812443673005)
  ·
    refine ⟨22029133598617804666377377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58744356262980812443673005 22029133598617804666377377)
    ·
      refine ⟨16521850198963353499783033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22029133598617804666377377 16521850198963353499783033)
      ·
        refine ⟨12391387649222515124837275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521850198963353499783033 12391387649222515124837275)
        ·
          refine ⟨18587081473833772687255913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391387649222515124837275 18587081473833772687255913)
          ·
            refine ⟨13940311105375329515441935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18587081473833772687255913 13940311105375329515441935)
            ·
              refine ⟨20910466658062994273162903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13940311105375329515441935 20910466658062994273162903)
              ·
                refine ⟨31365699987094491409744355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20910466658062994273162903 31365699987094491409744355)
                ·
                  refine ⟨47048549980641737114616533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31365699987094491409744355 47048549980641737114616533)
                  ·
                    refine ⟨1102700390171290713623825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47048549980641737114616533 1102700390171290713623825)
                    ·
                      rfl

theorem cell22_3221252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3221252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221252 prefixEnd_3221252 := by exact prefixLift 3221252
  have htrace : WordTrace (prefixWord ++ tailWord_3221252) baseStart_3221252 baseEnd_3221252 := by
    simpa [prefixWord, tailWord_3221252, baseEnd_3221252] using wordTrace_append hprefix tailTrace_3221252
  have hstable : (prefixWord ++ tailWord_3221252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221252).length < 2 ^ (prefixWord ++ tailWord_3221252).sum := by decide
  have hdescent : baseEnd_3221252 < baseStart_3221252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221282 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3221282 : Nat := 118140960795 + 3221282 * 2 ^ 59
def prefixEnd_3221282 : Nat := 4983230072969 + 3 ^ 40 * 3221282 * 2
def baseEnd_3221282 : Nat := 367570219928126878457911

theorem tailTrace_3221282 : CollatzResearch.WordTrace tailWord_3221282 prefixEnd_3221282 367570219928126878457911 := by
  unfold tailWord_3221282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372451678963235002734525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78326537810568626673958733 29372451678963235002734525)
  ·
    refine ⟨11014669379611213126025447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29372451678963235002734525 11014669379611213126025447)
    ·
      refine ⟨16522004069416819689038171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014669379611213126025447 16522004069416819689038171)
      ·
        refine ⟨24783006104125229533557257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522004069416819689038171 24783006104125229533557257)
        ·
          refine ⟨18587254578093922150167943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24783006104125229533557257 18587254578093922150167943)
          ·
            refine ⟨27880881867140883225251915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587254578093922150167943 27880881867140883225251915)
            ·
              refine ⟨41821322800711324837877873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880881867140883225251915 41821322800711324837877873)
              ·
                refine ⟨31365992100533493628408405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41821322800711324837877873 31365992100533493628408405)
                ·
                  refine ⟨367570219928126878457911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31365992100533493628408405 367570219928126878457911)
                  ·
                    rfl

theorem cell22_3221282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3221282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221282 prefixEnd_3221282 := by exact prefixLift 3221282
  have htrace : WordTrace (prefixWord ++ tailWord_3221282) baseStart_3221282 baseEnd_3221282 := by
    simpa [prefixWord, tailWord_3221282, baseEnd_3221282] using wordTrace_append hprefix tailTrace_3221282
  have hstable : (prefixWord ++ tailWord_3221282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221282).length < 2 ^ (prefixWord ++ tailWord_3221282).sum := by decide
  have hdescent : baseEnd_3221282 < baseStart_3221282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221299 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 6]
def baseStart_3221299 : Nat := 118140960795 + 3221299 * 2 ^ 59
def prefixEnd_3221299 : Nat := 4983230072969 + 3 ^ 40 * 3221299 * 2
def baseEnd_3221299 : Nat := 367572159743932752566227

theorem tailTrace_3221299 : CollatzResearch.WordTrace tailWord_3221299 prefixEnd_3221299 367572159743932752566227 := by
  unfold tailWord_3221299
  simp only [CollatzResearch.WordTrace]
  refine ⟨117490426756791351914306951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78326951171194234609537967 117490426756791351914306951)
  ·
    refine ⟨176235640135187027871460427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117490426756791351914306951 176235640135187027871460427)
    ·
      refine ⟨264353460202780541807190641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176235640135187027871460427 264353460202780541807190641)
      ·
        refine ⟨198265095152085406355392981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264353460202780541807190641 198265095152085406355392981)
        ·
          refine ⟨4646838167627001711454523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 198265095152085406355392981 4646838167627001711454523)
          ·
            refine ⟨6970257251440502567181785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646838167627001711454523 6970257251440502567181785)
            ·
              refine ⟨5227692938580376925386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6970257251440502567181785 5227692938580376925386339)
              ·
                refine ⟨7841539407870565388079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227692938580376925386339 7841539407870565388079509)
                ·
                  refine ⟨367572159743932752566227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7841539407870565388079509 367572159743932752566227)
                  ·
                    rfl

theorem cell22_3221299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_3221299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221299 prefixEnd_3221299 := by exact prefixLift 3221299
  have htrace : WordTrace (prefixWord ++ tailWord_3221299) baseStart_3221299 baseEnd_3221299 := by
    simpa [prefixWord, tailWord_3221299, baseEnd_3221299] using wordTrace_append hprefix tailTrace_3221299
  have hstable : (prefixWord ++ tailWord_3221299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221299).length < 2 ^ (prefixWord ++ tailWord_3221299).sum := by decide
  have hdescent : baseEnd_3221299 < baseStart_3221299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221318 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3221318 : Nat := 118140960795 + 3221318 * 2 ^ 59
def prefixEnd_3221318 : Nat := 4983230072969 + 3 ^ 40 * 3221318 * 2
def baseEnd_3221318 : Nat := 1102722983320088541473623

theorem tailTrace_3221318 : CollatzResearch.WordTrace tailWord_3221318 prefixEnd_3221318 1102722983320088541473623 := by
  unfold tailWord_3221318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671597491991328692476519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78327413162481678772832405 3671597491991328692476519)
  ·
    refine ⟨5507396237986993038714779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671597491991328692476519 5507396237986993038714779)
    ·
      refine ⟨8261094356980489558072169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507396237986993038714779 8261094356980489558072169)
      ·
        refine ⟨6195820767735367168554127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8261094356980489558072169 6195820767735367168554127)
        ·
          refine ⟨9293731151603050752831191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195820767735367168554127 9293731151603050752831191)
          ·
            refine ⟨13940596727404576129246787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293731151603050752831191 13940596727404576129246787)
            ·
              refine ⟨20910895091106864193870181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13940596727404576129246787 20910895091106864193870181)
              ·
                refine ⟨3920792829582537036350659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20910895091106864193870181 3920792829582537036350659)
                ·
                  refine ⟨5881189244373805554525989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920792829582537036350659 5881189244373805554525989)
                  ·
                    refine ⟨1102722983320088541473623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881189244373805554525989 1102722983320088541473623)
                    ·
                      rfl

theorem cell22_3221318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3221318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221318 prefixEnd_3221318 := by exact prefixLift 3221318
  have htrace : WordTrace (prefixWord ++ tailWord_3221318) baseStart_3221318 baseEnd_3221318 := by
    simpa [prefixWord, tailWord_3221318, baseEnd_3221318] using wordTrace_append hprefix tailTrace_3221318
  have hstable : (prefixWord ++ tailWord_3221318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221318).length < 2 ^ (prefixWord ++ tailWord_3221318).sum := by decide
  have hdescent : baseEnd_3221318 < baseStart_3221318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221346 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3221346 : Nat := 118140960795 + 3221346 * 2 ^ 59
def prefixEnd_3221346 : Nat := 4983230072969 + 3 ^ 40 * 3221346 * 2
def baseEnd_3221346 : Nat := 1102732568292305801773537

theorem tailTrace_3221346 : CollatzResearch.WordTrace tailWord_3221346 prefixEnd_3221346 1102732568292305801773537 := by
  unfold tailWord_3221346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373035246905269735316973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78328093991747385960845261 29373035246905269735316973)
  ·
    refine ⟨11014888217589476150743865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29373035246905269735316973 11014888217589476150743865)
    ·
      refine ⟨8261166163192107113057899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11014888217589476150743865 8261166163192107113057899)
      ·
        refine ⟨12391749244788160669586849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8261166163192107113057899 12391749244788160669586849)
        ·
          refine ⟨9293811933591120502190137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12391749244788160669586849 9293811933591120502190137)
          ·
            refine ⟨6970358950193340376642603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293811933591120502190137 6970358950193340376642603)
            ·
              refine ⟨10455538425290010564963905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970358950193340376642603 10455538425290010564963905)
              ·
                refine ⟨7841653818967507923722929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10455538425290010564963905 7841653818967507923722929)
                ·
                  refine ⟨5881240364225630942792197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7841653818967507923722929 5881240364225630942792197)
                  ·
                    refine ⟨1102732568292305801773537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881240364225630942792197 1102732568292305801773537)
                    ·
                      rfl

theorem cell22_3221346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3221346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221346 prefixEnd_3221346 := by exact prefixLift 3221346
  have htrace : WordTrace (prefixWord ++ tailWord_3221346) baseStart_3221346 baseEnd_3221346 := by
    simpa [prefixWord, tailWord_3221346, baseEnd_3221346] using wordTrace_append hprefix tailTrace_3221346
  have hstable : (prefixWord ++ tailWord_3221346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221346).length < 2 ^ (prefixWord ++ tailWord_3221346).sum := by decide
  have hdescent : baseEnd_3221346 < baseStart_3221346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221387 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_3221387 : Nat := 118140960795 + 3221387 * 2 ^ 59
def prefixEnd_3221387 : Nat := 4983230072969 + 3 ^ 40 * 3221387 * 2
def baseEnd_3221387 : Nat := 1102746603430195361498411

theorem tailTrace_3221387 : CollatzResearch.WordTrace tailWord_3221387 prefixEnd_3221387 1102746603430195361498411 := by
  unfold tailWord_3221387
  simp only [CollatzResearch.WordTrace]
  refine ⟨117493636380472542943510415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78329090920315028629006943 117493636380472542943510415)
  ·
    refine ⟨176240454570708814415265623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117493636380472542943510415 176240454570708814415265623)
    ·
      refine ⟨264360681856063221622898435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176240454570708814415265623 264360681856063221622898435)
      ·
        refine ⟨396541022784094832434347653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264360681856063221622898435 396541022784094832434347653)
        ·
          refine ⟨74351441772017781081440185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 396541022784094832434347653 74351441772017781081440185)
          ·
            refine ⟨55763581329013335811080139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74351441772017781081440185 55763581329013335811080139)
            ·
              refine ⟨83645371993520003716620209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55763581329013335811080139 83645371993520003716620209)
              ·
                refine ⟨62734028995140002787465157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83645371993520003716620209 62734028995140002787465157)
                ·
                  refine ⟨11762630436588750522649717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62734028995140002787465157 11762630436588750522649717)
                  ·
                    refine ⟨1102746603430195361498411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11762630436588750522649717 1102746603430195361498411)
                    ·
                      rfl

theorem cell22_3221387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_3221387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221387 prefixEnd_3221387 := by exact prefixLift 3221387
  have htrace : WordTrace (prefixWord ++ tailWord_3221387) baseStart_3221387 baseEnd_3221387 := by
    simpa [prefixWord, tailWord_3221387, baseEnd_3221387] using wordTrace_append hprefix tailTrace_3221387
  have hstable : (prefixWord ++ tailWord_3221387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221387).length < 2 ^ (prefixWord ++ tailWord_3221387).sum := by decide
  have hdescent : baseEnd_3221387 < baseStart_3221387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221410 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3221410 : Nat := 118140960795 + 3221410 * 2 ^ 59
def prefixEnd_3221410 : Nat := 4983230072969 + 3 ^ 40 * 3221410 * 2
def baseEnd_3221410 : Nat := 1102754476800230968173341

theorem tailTrace_3221410 : CollatzResearch.WordTrace tailWord_3221410 prefixEnd_3221410 1102754476800230968173341 := by
  unfold tailWord_3221410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373618814847304467899421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78329650172926145247731789 29373618814847304467899421)
  ·
    refine ⟨11015107055567739175462283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29373618814847304467899421 11015107055567739175462283)
    ·
      refine ⟨16522660583351608763193425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11015107055567739175462283 16522660583351608763193425)
      ·
        refine ⟨12391995437513706572395069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16522660583351608763193425 12391995437513706572395069)
        ·
          refine ⟨4646998289067639964648151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12391995437513706572395069 4646998289067639964648151)
          ·
            refine ⟨6970497433601459946972227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646998289067639964648151 6970497433601459946972227)
            ·
              refine ⟨10455746150402189920458341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970497433601459946972227 10455746150402189920458341)
              ·
                refine ⟨1960452403200410610085939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10455746150402189920458341 1960452403200410610085939)
                ·
                  refine ⟨2940678604800615915128909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960452403200410610085939 2940678604800615915128909)
                  ·
                    refine ⟨1102754476800230968173341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940678604800615915128909 1102754476800230968173341)
                    ·
                      rfl

theorem cell22_3221410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3221410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221410 prefixEnd_3221410 := by exact prefixLift 3221410
  have htrace : WordTrace (prefixWord ++ tailWord_3221410) baseStart_3221410 baseEnd_3221410 := by
    simpa [prefixWord, tailWord_3221410, baseEnd_3221410] using wordTrace_append hprefix tailTrace_3221410
  have hstable : (prefixWord ++ tailWord_3221410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221410).length < 2 ^ (prefixWord ++ tailWord_3221410).sum := by decide
  have hdescent : baseEnd_3221410 < baseStart_3221410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221449 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_3221449 : Nat := 118140960795 + 3221449 * 2 ^ 59
def prefixEnd_3221449 : Nat := 4983230072969 + 3 ^ 40 * 3221449 * 2
def baseEnd_3221449 : Nat := 1102767827297247866448221

theorem tailTrace_3221449 : CollatzResearch.WordTrace tailWord_3221449 prefixEnd_3221449 1102767827297247866448221 := by
  unfold tailWord_3221449
  simp only [CollatzResearch.WordTrace]
  refine ⟨117495897706247927532267401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78330598470831951688178267 117495897706247927532267401)
  ·
    refine ⟨88121923279685945649200551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117495897706247927532267401 88121923279685945649200551)
    ·
      refine ⟨132182884919528918473800827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88121923279685945649200551 132182884919528918473800827)
      ·
        refine ⟨198274327379293377710701241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132182884919528918473800827 198274327379293377710701241)
        ·
          refine ⟨148705745534470033283025931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198274327379293377710701241 148705745534470033283025931)
          ·
            refine ⟨223058618301705049924538897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148705745534470033283025931 223058618301705049924538897)
            ·
              refine ⟨167293963726278787443404173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223058618301705049924538897 167293963726278787443404173)
              ·
                refine ⟨62735236397354545291276565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167293963726278787443404173 62735236397354545291276565)
                ·
                  refine ⟨2940714206125994310528589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62735236397354545291276565 2940714206125994310528589)
                  ·
                    refine ⟨1102767827297247866448221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940714206125994310528589 1102767827297247866448221)
                    ·
                      rfl

theorem cell22_3221449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_3221449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221449 prefixEnd_3221449 := by exact prefixLift 3221449
  have htrace : WordTrace (prefixWord ++ tailWord_3221449) baseStart_3221449 baseEnd_3221449 := by
    simpa [prefixWord, tailWord_3221449, baseEnd_3221449] using wordTrace_append hprefix tailTrace_3221449
  have hstable : (prefixWord ++ tailWord_3221449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221449).length < 2 ^ (prefixWord ++ tailWord_3221449).sum := by decide
  have hdescent : baseEnd_3221449 < baseStart_3221449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221451 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 4]
def baseStart_3221451 : Nat := 118140960795 + 3221451 * 2 ^ 59
def prefixEnd_3221451 : Nat := 4983230072969 + 3 ^ 40 * 3221451 * 2
def baseEnd_3221451 : Nat := 367589503979373509299405

theorem tailTrace_3221451 : CollatzResearch.WordTrace tailWord_3221451 prefixEnd_3221451 367589503979373509299405 := by
  unfold tailWord_3221451
  simp only [CollatzResearch.WordTrace]
  refine ⟨117495970652240681873840207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78330647101493787915893471 117495970652240681873840207)
  ·
    refine ⟨176243955978361022810760311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117495970652240681873840207 176243955978361022810760311)
    ·
      refine ⟨264365933967541534216140467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176243955978361022810760311 264365933967541534216140467)
      ·
        refine ⟨396548900951312301324210701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264365933967541534216140467 396548900951312301324210701)
        ·
          refine ⟨148705837856742112996579013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396548900951312301324210701 148705837856742112996579013)
          ·
            refine ⟨27882344598139146186858565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148705837856742112996579013 27882344598139146186858565)
            ·
              refine ⟨5227939612151089910035981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27882344598139146186858565 5227939612151089910035981)
              ·
                refine ⟨1960477354556658716263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5227939612151089910035981 1960477354556658716263493)
                ·
                  refine ⟨367589503979373509299405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960477354556658716263493 367589503979373509299405)
                  ·
                    rfl

theorem cell22_3221451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 4].length) (baseStart_3221451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221451 prefixEnd_3221451 := by exact prefixLift 3221451
  have htrace : WordTrace (prefixWord ++ tailWord_3221451) baseStart_3221451 baseEnd_3221451 := by
    simpa [prefixWord, tailWord_3221451, baseEnd_3221451] using wordTrace_append hprefix tailTrace_3221451
  have hstable : (prefixWord ++ tailWord_3221451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221451).length < 2 ^ (prefixWord ++ tailWord_3221451).sum := by decide
  have hdescent : baseEnd_3221451 < baseStart_3221451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221464 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3221464 : Nat := 118140960795 + 3221464 * 2 ^ 59
def prefixEnd_3221464 : Nat := 4983230072969 + 3 ^ 40 * 3221464 * 2
def baseEnd_3221464 : Nat := 1102772962103792827323175

theorem tailTrace_3221464 : CollatzResearch.WordTrace tailWord_3221464 prefixEnd_3221464 1102772962103792827323175 := by
  unfold tailWord_3221464
  simp only [CollatzResearch.WordTrace]
  refine ⟨58748222400596792547031723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78330963200795723396042297 58748222400596792547031723)
  ·
    refine ⟨88122333600895188820547585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58748222400596792547031723 88122333600895188820547585)
    ·
      refine ⟨66091750200671391615410689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88122333600895188820547585 66091750200671391615410689)
      ·
        refine ⟨49568812650503543711558017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66091750200671391615410689 49568812650503543711558017)
        ·
          refine ⟨37176609487877657783668513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49568812650503543711558017 37176609487877657783668513)
          ·
            refine ⟨27882457115908243337751385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37176609487877657783668513 27882457115908243337751385)
            ·
              refine ⟨20911842836931182503313539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27882457115908243337751385 20911842836931182503313539)
              ·
                refine ⟨31367764255396773754970309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20911842836931182503313539 31367764255396773754970309)
                ·
                  refine ⟨5881455797886895079056933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31367764255396773754970309 5881455797886895079056933)
                  ·
                    refine ⟨1102772962103792827323175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881455797886895079056933 1102772962103792827323175)
                    ·
                      rfl

theorem cell22_3221464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3221464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221464 prefixEnd_3221464 := by exact prefixLift 3221464
  have htrace : WordTrace (prefixWord ++ tailWord_3221464) baseStart_3221464 baseEnd_3221464 := by
    simpa [prefixWord, tailWord_3221464, baseEnd_3221464] using wordTrace_append hprefix tailTrace_3221464
  have hstable : (prefixWord ++ tailWord_3221464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221464).length < 2 ^ (prefixWord ++ tailWord_3221464).sum := by decide
  have hdescent : baseEnd_3221464 < baseStart_3221464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221539 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_3221539 : Nat := 118140960795 + 3221539 * 2 ^ 59
def prefixEnd_3221539 : Nat := 4983230072969 + 3 ^ 40 * 3221539 * 2
def baseEnd_3221539 : Nat := 1102798636136517631697945

theorem tailTrace_3221539 : CollatzResearch.WordTrace tailWord_3221539 prefixEnd_3221539 1102798636136517631697945 := by
  unfold tailWord_3221539
  simp only [CollatzResearch.WordTrace]
  refine ⟨117499180275921872903043671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78332786850614581935362447 117499180275921872903043671)
  ·
    refine ⟨176248770413882809354565507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117499180275921872903043671 176248770413882809354565507)
    ·
      refine ⟨264373155620824214031848261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176248770413882809354565507 264373155620824214031848261)
      ·
        refine ⟨49569966678904540130971549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264373155620824214031848261 49569966678904540130971549)
        ·
          refine ⟨18588737504589202549114331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49569966678904540130971549 18588737504589202549114331)
          ·
            refine ⟨27883106256883803823671497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18588737504589202549114331 27883106256883803823671497)
            ·
              refine ⟨20912329692662852867753623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27883106256883803823671497 20912329692662852867753623)
              ·
                refine ⟨31368494538994279301630435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20912329692662852867753623 31368494538994279301630435)
                ·
                  refine ⟨47052741808491418952445653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31368494538994279301630435 47052741808491418952445653)
                  ·
                    refine ⟨1102798636136517631697945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47052741808491418952445653 1102798636136517631697945)
                    ·
                      rfl

theorem cell22_3221539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_3221539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221539 prefixEnd_3221539 := by exact prefixLift 3221539
  have htrace : WordTrace (prefixWord ++ tailWord_3221539) baseStart_3221539 baseEnd_3221539 := by
    simpa [prefixWord, tailWord_3221539, baseEnd_3221539] using wordTrace_append hprefix tailTrace_3221539
  have hstable : (prefixWord ++ tailWord_3221539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221539).length < 2 ^ (prefixWord ++ tailWord_3221539).sum := by decide
  have hdescent : baseEnd_3221539 < baseStart_3221539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221541 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3221541 : Nat := 118140960795 + 3221541 * 2 ^ 59
def prefixEnd_3221541 : Nat := 4983230072969 + 3 ^ 40 * 3221541 * 2
def baseEnd_3221541 : Nat := 367599773592463431049313

theorem tailTrace_3221541 : CollatzResearch.WordTrace tailWord_3221541 prefixEnd_3221541 367599773592463431049313 := by
  unfold tailWord_3221541
  simp only [CollatzResearch.WordTrace]
  refine ⟨117499253221914627244616477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78332835481276418163077651 117499253221914627244616477)
  ·
    refine ⟨44062219958217985216731179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117499253221914627244616477 44062219958217985216731179)
    ·
      refine ⟨66093329937326977825096769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44062219958217985216731179 66093329937326977825096769)
      ·
        refine ⟨49569997452995233368822577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66093329937326977825096769 49569997452995233368822577)
        ·
          refine ⟨37177498089746425026616933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49569997452995233368822577 37177498089746425026616933)
          ·
            refine ⟨6970780891827454692490675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37177498089746425026616933 6970780891827454692490675)
            ·
              refine ⟨10456171337741182038736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970780891827454692490675 10456171337741182038736013)
              ·
                refine ⟨3921064251652943264526005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10456171337741182038736013 3921064251652943264526005)
                ·
                  refine ⟨367599773592463431049313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921064251652943264526005 367599773592463431049313)
                  ·
                    rfl

theorem cell22_3221541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3221541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221541 prefixEnd_3221541 := by exact prefixLift 3221541
  have htrace : WordTrace (prefixWord ++ tailWord_3221541) baseStart_3221541 baseEnd_3221541 := by
    simpa [prefixWord, tailWord_3221541, baseEnd_3221541] using wordTrace_append hprefix tailTrace_3221541
  have hstable : (prefixWord ++ tailWord_3221541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221541).length < 2 ^ (prefixWord ++ tailWord_3221541).sum := by decide
  have hdescent : baseEnd_3221541 < baseStart_3221541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221590 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3221590 : Nat := 118140960795 + 3221590 * 2 ^ 59
def prefixEnd_3221590 : Nat := 4983230072969 + 3 ^ 40 * 3221590 * 2
def baseEnd_3221590 : Nat := 1102816094478770498672789

theorem tailTrace_3221590 : CollatzResearch.WordTrace tailWord_3221590 prefixEnd_3221590 1102816094478770498672789 := by
  unfold tailWord_3221590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343815024921069288321889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78334026932491405742100149 7343815024921069288321889)
  ·
    refine ⟨5507861268690801966241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7343815024921069288321889 5507861268690801966241417)
    ·
      refine ⟨4130895951518101474681063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5507861268690801966241417 4130895951518101474681063)
      ·
        refine ⟨6196343927277152212021595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130895951518101474681063 6196343927277152212021595)
        ·
          refine ⟨9294515890915728318032393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196343927277152212021595 9294515890915728318032393)
          ·
            refine ⟨6970886918186796238524295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9294515890915728318032393 6970886918186796238524295)
            ·
              refine ⟨10456330377280194357786443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970886918186796238524295 10456330377280194357786443)
              ·
                refine ⟨15684495565920291536679665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456330377280194357786443 15684495565920291536679665)
                ·
                  refine ⟨11763371674440218652509749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15684495565920291536679665 11763371674440218652509749)
                  ·
                    refine ⟨1102816094478770498672789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11763371674440218652509749 1102816094478770498672789)
                    ·
                      rfl

theorem cell22_3221590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3221590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221590 prefixEnd_3221590 := by exact prefixLift 3221590
  have htrace : WordTrace (prefixWord ++ tailWord_3221590) baseStart_3221590 baseEnd_3221590 := by
    simpa [prefixWord, tailWord_3221590, baseEnd_3221590] using wordTrace_append hprefix tailTrace_3221590
  have hstable : (prefixWord ++ tailWord_3221590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221590).length < 2 ^ (prefixWord ++ tailWord_3221590).sum := by decide
  have hdescent : baseEnd_3221590 < baseStart_3221590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221601 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3221601 : Nat := 118140960795 + 3221601 * 2 ^ 59
def prefixEnd_3221601 : Nat := 4983230072969 + 3 ^ 40 * 3221601 * 2
def baseEnd_3221601 : Nat := 1102819860003570136647755

theorem tailTrace_3221601 : CollatzResearch.WordTrace tailWord_3221601 prefixEnd_3221601 1102819860003570136647755 := by
  unfold tailWord_3221601
  simp only [CollatzResearch.WordTrace]
  refine ⟨117501441601697257491800657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78334294401131504994533771 117501441601697257491800657)
  ·
    refine ⟨88126081201272943118850493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117501441601697257491800657 88126081201272943118850493)
    ·
      refine ⟨33047280450477353669568935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88126081201272943118850493 33047280450477353669568935)
      ·
        refine ⟨49570920675716030504353403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33047280450477353669568935 49570920675716030504353403)
        ·
          refine ⟨74356381013574045756530105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49570920675716030504353403 74356381013574045756530105)
          ·
            refine ⟨55767285760180534317397579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74356381013574045756530105 55767285760180534317397579)
            ·
              refine ⟨83650928640270801476096369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55767285760180534317397579 83650928640270801476096369)
              ·
                refine ⟨62738196480203101107072277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83650928640270801476096369 62738196480203101107072277)
                ·
                  refine ⟨2940852960009520364394013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62738196480203101107072277 2940852960009520364394013)
                  ·
                    refine ⟨1102819860003570136647755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940852960009520364394013 1102819860003570136647755)
                    ·
                      rfl

theorem cell22_3221601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3221601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221601 prefixEnd_3221601 := by exact prefixLift 3221601
  have htrace : WordTrace (prefixWord ++ tailWord_3221601) baseStart_3221601 baseEnd_3221601 := by
    simpa [prefixWord, tailWord_3221601, baseEnd_3221601] using wordTrace_append hprefix tailTrace_3221601
  have hstable : (prefixWord ++ tailWord_3221601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221601).length < 2 ^ (prefixWord ++ tailWord_3221601).sum := by decide
  have hdescent : baseEnd_3221601 < baseStart_3221601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221616 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_3221616 : Nat := 118140960795 + 3221616 * 2 ^ 59
def prefixEnd_3221616 : Nat := 4983230072969 + 3 ^ 40 * 3221616 * 2
def baseEnd_3221616 : Nat := 1102824994810115097522709

theorem tailTrace_3221616 : CollatzResearch.WordTrace tailWord_3221616 prefixEnd_3221616 1102824994810115097522709 := by
  unfold tailWord_3221616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58750994348321457526798351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78334659131095276702397801 58750994348321457526798351)
  ·
    refine ⟨88126491522482186290197527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58750994348321457526798351 88126491522482186290197527)
    ·
      refine ⟨132189737283723279435296291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88126491522482186290197527 132189737283723279435296291)
      ·
        refine ⟨198284605925584919152944437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132189737283723279435296291 198284605925584919152944437)
        ·
          refine ⟨18589181805523586170588541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198284605925584919152944437 18589181805523586170588541)
          ·
            refine ⟨6970943177071344813970703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18589181805523586170588541 6970943177071344813970703)
            ·
              refine ⟨10456414765607017220956055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970943177071344813970703 10456414765607017220956055)
              ·
                refine ⟨15684622148410525831434083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456414765607017220956055 15684622148410525831434083)
                ·
                  refine ⟨23526933222615788747151125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15684622148410525831434083 23526933222615788747151125)
                  ·
                    refine ⟨1102824994810115097522709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23526933222615788747151125 1102824994810115097522709)
                    ·
                      rfl

theorem cell22_3221616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_3221616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221616 prefixEnd_3221616 := by exact prefixLift 3221616
  have htrace : WordTrace (prefixWord ++ tailWord_3221616) baseStart_3221616 baseEnd_3221616 := by
    simpa [prefixWord, tailWord_3221616, baseEnd_3221616] using wordTrace_append hprefix tailTrace_3221616
  have hstable : (prefixWord ++ tailWord_3221616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221616).length < 2 ^ (prefixWord ++ tailWord_3221616).sum := by decide
  have hdescent : baseEnd_3221616 < baseStart_3221616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221622 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3221622 : Nat := 118140960795 + 3221622 * 2 ^ 59
def prefixEnd_3221622 : Nat := 4983230072969 + 3 ^ 40 * 3221622 * 2
def baseEnd_3221622 : Nat := 1102827048732733081872691

theorem tailTrace_3221622 : CollatzResearch.WordTrace tailWord_3221622 prefixEnd_3221622 1102827048732733081872691 := by
  unfold tailWord_3221622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343887970913823629894695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78334805023080785385543413 7343887970913823629894695)
  ·
    refine ⟨11015831956370735444842043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7343887970913823629894695 11015831956370735444842043)
    ·
      refine ⟨16523747934556103167263065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11015831956370735444842043 16523747934556103167263065)
      ·
        refine ⟨12392810950917077375447299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16523747934556103167263065 12392810950917077375447299)
        ·
          refine ⟨18589216426375616063170949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392810950917077375447299 18589216426375616063170949)
          ·
            refine ⟨3485478079945428011844553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18589216426375616063170949 3485478079945428011844553)
            ·
              refine ⟨2614108559959071008883415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485478079945428011844553 2614108559959071008883415)
              ·
                refine ⟨3921162839938606513325123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614108559959071008883415 3921162839938606513325123)
                ·
                  refine ⟨5881744259907909769987685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921162839938606513325123 5881744259907909769987685)
                  ·
                    refine ⟨1102827048732733081872691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881744259907909769987685 1102827048732733081872691)
                    ·
                      rfl

theorem cell22_3221622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3221622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221622 prefixEnd_3221622 := by exact prefixLift 3221622
  have htrace : WordTrace (prefixWord ++ tailWord_3221622) baseStart_3221622 baseEnd_3221622 := by
    simpa [prefixWord, tailWord_3221622, baseEnd_3221622] using wordTrace_append hprefix tailTrace_3221622
  have hstable : (prefixWord ++ tailWord_3221622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221622).length < 2 ^ (prefixWord ++ tailWord_3221622).sum := by decide
  have hdescent : baseEnd_3221622 < baseStart_3221622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221635 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 2, 3]
def baseStart_3221635 : Nat := 118140960795 + 3221635 * 2 ^ 59
def prefixEnd_3221635 : Nat := 4983230072969 + 3 ^ 40 * 3221635 * 2
def baseEnd_3221635 : Nat := 1102831498898405381297651

theorem tailTrace_3221635 : CollatzResearch.WordTrace tailWord_3221635 prefixEnd_3221635 1102831498898405381297651 := by
  unfold tailWord_3221635
  simp only [CollatzResearch.WordTrace]
  refine ⟨117502681683574081298538359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78335121122382720865692239 117502681683574081298538359)
  ·
    refine ⟨176254022525361121947807539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117502681683574081298538359 176254022525361121947807539)
    ·
      refine ⟨264381033788041682921711309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176254022525361121947807539 264381033788041682921711309)
      ·
        refine ⟨99142887670515631095641741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264381033788041682921711309 99142887670515631095641741)
        ·
          refine ⟨37178582876443361660865653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99142887670515631095641741 37178582876443361660865653)
          ·
            refine ⟨3485492144666565155706155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37178582876443361660865653 3485492144666565155706155)
            ·
              refine ⟨5228238216999847733559233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485492144666565155706155 5228238216999847733559233)
              ·
                refine ⟨3921178662749885800169425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228238216999847733559233 3921178662749885800169425)
                ·
                  refine ⟨2940883997062414350127069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921178662749885800169425 2940883997062414350127069)
                  ·
                    refine ⟨1102831498898405381297651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940883997062414350127069 1102831498898405381297651)
                    ·
                      rfl

theorem cell22_3221635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].length) (baseStart_3221635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221635 prefixEnd_3221635 := by exact prefixLift 3221635
  have htrace : WordTrace (prefixWord ++ tailWord_3221635) baseStart_3221635 baseEnd_3221635 := by
    simpa [prefixWord, tailWord_3221635, baseEnd_3221635] using wordTrace_append hprefix tailTrace_3221635
  have hstable : (prefixWord ++ tailWord_3221635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221635).length < 2 ^ (prefixWord ++ tailWord_3221635).sum := by decide
  have hdescent : baseEnd_3221635 < baseStart_3221635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221652 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3221652 : Nat := 118140960795 + 3221652 * 2 ^ 59
def prefixEnd_3221652 : Nat := 4983230072969 + 3 ^ 40 * 3221652 * 2
def baseEnd_3221652 : Nat := 1102837318345823003622599

theorem tailTrace_3221652 : CollatzResearch.WordTrace tailWord_3221652 prefixEnd_3221652 1102837318345823003622599 := by
  unfold tailWord_3221652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58751650862256246600953605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78335534483008328801271473 58751650862256246600953605)
  ·
    refine ⟨11015934536673046237678801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58751650862256246600953605 11015934536673046237678801)
    ·
      refine ⟨8261950902504784678259101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11015934536673046237678801 8261950902504784678259101)
      ·
        refine ⟨3098231588439294254347163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8261950902504784678259101 3098231588439294254347163)
        ·
          refine ⟨4647347382658941381520745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098231588439294254347163 4647347382658941381520745)
          ·
            refine ⟨3485510536994206036140559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647347382658941381520745 3485510536994206036140559)
            ·
              refine ⟨5228265805491309054210839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485510536994206036140559 5228265805491309054210839)
              ·
                refine ⟨7842398708236963581316259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228265805491309054210839 7842398708236963581316259)
                ·
                  refine ⟨11763598062355445371974389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842398708236963581316259 11763598062355445371974389)
                  ·
                    refine ⟨1102837318345823003622599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11763598062355445371974389 1102837318345823003622599)
                    ·
                      rfl

theorem cell22_3221652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3221652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221652 prefixEnd_3221652 := by exact prefixLift 3221652
  have htrace : WordTrace (prefixWord ++ tailWord_3221652) baseStart_3221652 baseEnd_3221652 := by
    simpa [prefixWord, tailWord_3221652, baseEnd_3221652] using wordTrace_append hprefix tailTrace_3221652
  have hstable : (prefixWord ++ tailWord_3221652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221652).length < 2 ^ (prefixWord ++ tailWord_3221652).sum := by decide
  have hdescent : baseEnd_3221652 < baseStart_3221652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221684 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3221684 : Nat := 118140960795 + 3221684 * 2 ^ 59
def prefixEnd_3221684 : Nat := 4983230072969 + 3 ^ 40 * 3221684 * 2
def baseEnd_3221684 : Nat := 1102848272599785586822501

theorem tailTrace_3221684 : CollatzResearch.WordTrace tailWord_3221684 prefixEnd_3221684 1102848272599785586822501 := by
  unfold tailWord_3221684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752234430198281333536053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78336312573597708444714737 58752234430198281333536053)
  ·
    refine ⟨5508021977831088875019005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58752234430198281333536053 5508021977831088875019005)
    ·
      refine ⟨2065508241686658328132127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5508021977831088875019005 2065508241686658328132127)
      ·
        refine ⟨3098262362529987492198191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065508241686658328132127 3098262362529987492198191)
        ·
          refine ⟨4647393543794981238297287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098262362529987492198191 4647393543794981238297287)
          ·
            refine ⟨6971090315692471857445931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647393543794981238297287 6971090315692471857445931)
            ·
              refine ⟨10456635473538707786168897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971090315692471857445931 10456635473538707786168897)
              ·
                refine ⟨7842476605154030839626673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456635473538707786168897 7842476605154030839626673)
                ·
                  refine ⟨5881857453865523129720005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842476605154030839626673 5881857453865523129720005)
                  ·
                    refine ⟨1102848272599785586822501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881857453865523129720005 1102848272599785586822501)
                    ·
                      rfl

theorem cell22_3221684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3221684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221684 prefixEnd_3221684 := by exact prefixLift 3221684
  have htrace : WordTrace (prefixWord ++ tailWord_3221684) baseStart_3221684 baseEnd_3221684 := by
    simpa [prefixWord, tailWord_3221684, baseEnd_3221684] using wordTrace_append hprefix tailTrace_3221684
  have hstable : (prefixWord ++ tailWord_3221684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221684).length < 2 ^ (prefixWord ++ tailWord_3221684).sum := by decide
  have hdescent : baseEnd_3221684 < baseStart_3221684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221710 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3221710 : Nat := 118140960795 + 3221710 * 2 ^ 59
def prefixEnd_3221710 : Nat := 4983230072969 + 3 ^ 40 * 3221710 * 2
def baseEnd_3221710 : Nat := 367619057643710061890807

theorem tailTrace_3221710 : CollatzResearch.WordTrace tailWord_3221710 prefixEnd_3221710 367619057643710061890807 := by
  unfold tailWord_3221710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688177144787796138439823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78336944772201579405012389 14688177144787796138439823)
  ·
    refine ⟨22032265717181694207659735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14688177144787796138439823 22032265717181694207659735)
    ·
      refine ⟨33048398575772541311489603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22032265717181694207659735 33048398575772541311489603)
      ·
        refine ⟨49572597863658811967234405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33048398575772541311489603 49572597863658811967234405)
        ·
          refine ⟨9294862099436027243856451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49572597863658811967234405 9294862099436027243856451)
          ·
            refine ⟨13942293149154040865784677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294862099436027243856451 13942293149154040865784677)
            ·
              refine ⟨2614179965466382662334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13942293149154040865784677 2614179965466382662334627)
              ·
                refine ⟨3921269948199573993501941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614179965466382662334627 3921269948199573993501941)
                ·
                  refine ⟨367619057643710061890807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921269948199573993501941 367619057643710061890807)
                  ·
                    rfl

theorem cell22_3221710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3221710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221710 prefixEnd_3221710 := by exact prefixLift 3221710
  have htrace : WordTrace (prefixWord ++ tailWord_3221710) baseStart_3221710 baseEnd_3221710 := by
    simpa [prefixWord, tailWord_3221710, baseEnd_3221710] using wordTrace_append hprefix tailTrace_3221710
  have hstable : (prefixWord ++ tailWord_3221710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221710).length < 2 ^ (prefixWord ++ tailWord_3221710).sum := by decide
  have hdescent : baseEnd_3221710 < baseStart_3221710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221721 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 6]
def baseStart_3221721 : Nat := 118140960795 + 3221721 * 2 ^ 59
def prefixEnd_3221721 : Nat := 4983230072969 + 3 ^ 40 * 3221721 * 2
def baseEnd_3221721 : Nat := 367620312818643274549129

theorem tailTrace_3221721 : CollatzResearch.WordTrace tailWord_3221721 prefixEnd_3221721 367620312818643274549129 := by
  unfold tailWord_3221721
  simp only [CollatzResearch.WordTrace]
  refine ⟨117505818361262517986169017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78337212240841678657446011 117505818361262517986169017)
  ·
    refine ⟨88129363770946888489626763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117505818361262517986169017 88129363770946888489626763)
    ·
      refine ⟨132194045656420332734440145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88129363770946888489626763 132194045656420332734440145)
      ·
        refine ⟨99145534242315249550830109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132194045656420332734440145 99145534242315249550830109)
        ·
          refine ⟨37179575340868218581561291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99145534242315249550830109 37179575340868218581561291)
          ·
            refine ⟨55769363011302327872341937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37179575340868218581561291 55769363011302327872341937)
            ·
              refine ⟨41827022258476745904256453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55769363011302327872341937 41827022258476745904256453)
              ·
                refine ⟨7842566673464389857048085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41827022258476745904256453 7842566673464389857048085)
                ·
                  refine ⟨367620312818643274549129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7842566673464389857048085 367620312818643274549129)
                  ·
                    rfl

theorem cell22_3221721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_3221721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221721 prefixEnd_3221721 := by exact prefixLift 3221721
  have htrace : WordTrace (prefixWord ++ tailWord_3221721) baseStart_3221721 baseEnd_3221721 := by
    simpa [prefixWord, tailWord_3221721, baseEnd_3221721] using wordTrace_append hprefix tailTrace_3221721
  have hstable : (prefixWord ++ tailWord_3221721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221721).length < 2 ^ (prefixWord ++ tailWord_3221721).sum := by decide
  have hdescent : baseEnd_3221721 < baseStart_3221721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221740 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_3221740 : Nat := 118140960795 + 3221740 * 2 ^ 59
def prefixEnd_3221740 : Nat := 4983230072969 + 3 ^ 40 * 3221740 * 2
def baseEnd_3221740 : Nat := 1102867442544220107422329

theorem tailTrace_3221740 : CollatzResearch.WordTrace tailWord_3221740 prefixEnd_3221740 1102867442544220107422329 := by
  unfold tailWord_3221740
  simp only [CollatzResearch.WordTrace]
  refine ⟨58753255674096842115555337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78337674232129122820740449 58753255674096842115555337)
  ·
    refine ⟨44064941755572631586666503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58753255674096842115555337 44064941755572631586666503)
    ·
      refine ⟨66097412633358947379999755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44064941755572631586666503 66097412633358947379999755)
      ·
        refine ⟨99146118950038421069999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66097412633358947379999755 99146118950038421069999633)
        ·
          refine ⟨74359589212528815802499725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99146118950038421069999633 74359589212528815802499725)
          ·
            refine ⟨27884845954698305925937397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74359589212528815802499725 27884845954698305925937397)
            ·
              refine ⟨2614204308252966180556631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27884845954698305925937397 2614204308252966180556631)
              ·
                refine ⟨3921306462379449270834947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614204308252966180556631 3921306462379449270834947)
                ·
                  refine ⟨5881959693569173906252421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921306462379449270834947 5881959693569173906252421)
                  ·
                    refine ⟨1102867442544220107422329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881959693569173906252421 1102867442544220107422329)
                    ·
                      rfl

theorem cell22_3221740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_3221740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221740 prefixEnd_3221740 := by exact prefixLift 3221740
  have htrace : WordTrace (prefixWord ++ tailWord_3221740) baseStart_3221740 baseEnd_3221740 := by
    simpa [prefixWord, tailWord_3221740, baseEnd_3221740] using wordTrace_append hprefix tailTrace_3221740
  have hstable : (prefixWord ++ tailWord_3221740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221740).length < 2 ^ (prefixWord ++ tailWord_3221740).sum := by decide
  have hdescent : baseEnd_3221740 < baseStart_3221740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221770 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_3221770 : Nat := 118140960795 + 3221770 * 2 ^ 59
def prefixEnd_3221770 : Nat := 4983230072969 + 3 ^ 40 * 3221770 * 2
def baseEnd_3221770 : Nat := 1102877712157310029172237

theorem tailTrace_3221770 : CollatzResearch.WordTrace tailWord_3221770 prefixEnd_3221770 1102877712157310029172237 := by
  unfold tailWord_3221770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29376901384521249838675691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78338403692056666236468509 29376901384521249838675691)
  ·
    refine ⟨44065352076781874758013537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29376901384521249838675691 44065352076781874758013537)
    ·
      refine ⟨33049014057586406068510153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44065352076781874758013537 33049014057586406068510153)
      ·
        refine ⟨24786760543189804551382615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33049014057586406068510153 24786760543189804551382615)
        ·
          refine ⟨37180140814784706827073923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24786760543189804551382615 37180140814784706827073923)
          ·
            refine ⟨55770211222177060240610885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37180140814784706827073923 55770211222177060240610885)
            ·
              refine ⟨10456914604158198795114541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55770211222177060240610885 10456914604158198795114541)
              ·
                refine ⟨3921342976559324548167953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10456914604158198795114541 3921342976559324548167953)
                ·
                  refine ⟨2941007232419493411125965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921342976559324548167953 2941007232419493411125965)
                  ·
                    refine ⟨1102877712157310029172237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941007232419493411125965 1102877712157310029172237)
                    ·
                      rfl

theorem cell22_3221770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_3221770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221770 prefixEnd_3221770 := by exact prefixLift 3221770
  have htrace : WordTrace (prefixWord ++ tailWord_3221770) baseStart_3221770 baseEnd_3221770 := by
    simpa [prefixWord, tailWord_3221770, baseEnd_3221770] using wordTrace_append hprefix tailTrace_3221770
  have hstable : (prefixWord ++ tailWord_3221770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221770).length < 2 ^ (prefixWord ++ tailWord_3221770).sum := by decide
  have hdescent : baseEnd_3221770 < baseStart_3221770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221866 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_3221866 : Nat := 118140960795 + 3221866 * 2 ^ 59
def prefixEnd_3221866 : Nat := 4983230072969 + 3 ^ 40 * 3221866 * 2
def baseEnd_3221866 : Nat := 1102910574919197778771943

theorem tailTrace_3221866 : CollatzResearch.WordTrace tailWord_3221866 prefixEnd_3221866 1102910574919197778771943 := by
  unfold tailWord_3221866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377776736434301937549363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78340737963824805166798301 29377776736434301937549363)
  ·
    refine ⟨44066665104651452906324045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29377776736434301937549363 44066665104651452906324045)
    ·
      refine ⟨16524999414244294839871517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44066665104651452906324045 16524999414244294839871517)
      ·
        refine ⟨6196874780341610564951819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16524999414244294839871517 6196874780341610564951819)
        ·
          refine ⟨9295312170512415847427729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196874780341610564951819 9295312170512415847427729)
          ·
            refine ⟨6971484127884311885570797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9295312170512415847427729 6971484127884311885570797)
            ·
              refine ⟨2614306547956616957089049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6971484127884311885570797 2614306547956616957089049)
              ·
                refine ⟨1960729910967462717816787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614306547956616957089049 1960729910967462717816787)
                ·
                  refine ⟨2941094866451194076725181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960729910967462717816787 2941094866451194076725181)
                  ·
                    refine ⟨1102910574919197778771943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941094866451194076725181 1102910574919197778771943)
                    ·
                      rfl

theorem cell22_3221866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_3221866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221866 prefixEnd_3221866 := by exact prefixLift 3221866
  have htrace : WordTrace (prefixWord ++ tailWord_3221866) baseStart_3221866 baseEnd_3221866 := by
    simpa [prefixWord, tailWord_3221866, baseEnd_3221866] using wordTrace_append hprefix tailTrace_3221866
  have hstable : (prefixWord ++ tailWord_3221866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221866).length < 2 ^ (prefixWord ++ tailWord_3221866).sum := by decide
  have hdescent : baseEnd_3221866 < baseStart_3221866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221920 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_3221920 : Nat := 118140960795 + 3221920 * 2 ^ 59
def prefixEnd_3221920 : Nat := 4983230072969 + 3 ^ 40 * 3221920 * 2
def baseEnd_3221920 : Nat := 1102929060222759637921777

theorem tailTrace_3221920 : CollatzResearch.WordTrace tailWord_3221920 prefixEnd_3221920 1102929060222759637921777 := by
  unfold tailWord_3221920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58756538243770787486331607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78342050991694383315108809 58756538243770787486331607)
  ·
    refine ⟨88134807365656181229497411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58756538243770787486331607 88134807365656181229497411)
    ·
      refine ⟨132202211048484271844246117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88134807365656181229497411 132202211048484271844246117)
      ·
        refine ⟨24787914571590800970796147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132202211048484271844246117 24787914571590800970796147)
        ·
          refine ⟨37181871857386201456194221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24787914571590800970796147 37181871857386201456194221)
          ·
            refine ⟨13943201946519825546072833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37181871857386201456194221 13943201946519825546072833)
            ·
              refine ⟨10457401459889869159554625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13943201946519825546072833 10457401459889869159554625)
              ·
                refine ⟨7843051094917401869665969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10457401459889869159554625 7843051094917401869665969)
                ·
                  refine ⟨5882288321188051402249477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843051094917401869665969 5882288321188051402249477)
                  ·
                    refine ⟨1102929060222759637921777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882288321188051402249477 1102929060222759637921777)
                    ·
                      rfl

theorem cell22_3221920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_3221920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221920 prefixEnd_3221920 := by exact prefixLift 3221920
  have htrace : WordTrace (prefixWord ++ tailWord_3221920) baseStart_3221920 baseEnd_3221920 := by
    simpa [prefixWord, tailWord_3221920, baseEnd_3221920] using wordTrace_append hprefix tailTrace_3221920
  have hstable : (prefixWord ++ tailWord_3221920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221920).length < 2 ^ (prefixWord ++ tailWord_3221920).sum := by decide
  have hdescent : baseEnd_3221920 < baseStart_3221920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221963 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 7]
def baseStart_3221963 : Nat := 118140960795 + 3221963 * 2 ^ 59
def prefixEnd_3221963 : Nat := 4983230072969 + 3 ^ 40 * 3221963 * 2
def baseEnd_3221963 : Nat := 367647926667173953032215

theorem tailTrace_3221963 : CollatzResearch.WordTrace tailWord_3221963 prefixEnd_3221963 367647926667173953032215 := by
  unfold tailWord_3221963
  simp only [CollatzResearch.WordTrace]
  refine ⟨117514644826385793316478543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78343096550923862210985695 117514644826385793316478543)
  ·
    refine ⟨176271967239578689974717815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117514644826385793316478543 176271967239578689974717815)
    ·
      refine ⟨264407950859368034962076723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176271967239578689974717815 264407950859368034962076723)
      ·
        refine ⟨396611926289052052443115085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264407950859368034962076723 396611926289052052443115085)
        ·
          refine ⟨148729472358394519666168157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396611926289052052443115085 148729472358394519666168157)
          ·
            refine ⟨55773552134397944874813059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148729472358394519666168157 55773552134397944874813059)
            ·
              refine ⟨83660328201596917312219589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55773552134397944874813059 83660328201596917312219589)
              ·
                refine ⟨15686311537799421996041173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83660328201596917312219589 15686311537799421996041173)
                ·
                  refine ⟨367647926667173953032215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15686311537799421996041173 367647926667173953032215)
                  ·
                    rfl

theorem cell22_3221963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_3221963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221963 prefixEnd_3221963 := by exact prefixLift 3221963
  have htrace : WordTrace (prefixWord ++ tailWord_3221963) baseStart_3221963 baseEnd_3221963 := by
    simpa [prefixWord, tailWord_3221963, baseEnd_3221963] using wordTrace_append hprefix tailTrace_3221963
  have hstable : (prefixWord ++ tailWord_3221963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221963).length < 2 ^ (prefixWord ++ tailWord_3221963).sum := by decide
  have hdescent : baseEnd_3221963 < baseStart_3221963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3221993 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3221993 : Nat := 118140960795 + 3221993 * 2 ^ 59
def prefixEnd_3221993 : Nat := 4983230072969 + 3 ^ 40 * 3221993 * 2
def baseEnd_3221993 : Nat := 1102954049614611780846553

theorem tailTrace_3221993 : CollatzResearch.WordTrace tailWord_3221993 prefixEnd_3221993 1102954049614611780846553 := by
  unfold tailWord_3221993
  simp only [CollatzResearch.WordTrace]
  refine ⟨117515739016277108440070633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78343826010851405626713755 117515739016277108440070633)
  ·
    refine ⟨88136804262207831330052975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117515739016277108440070633 88136804262207831330052975)
    ·
      refine ⟨132205206393311746995079463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88136804262207831330052975 132205206393311746995079463)
      ·
        refine ⟨198307809589967620492619195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132205206393311746995079463 198307809589967620492619195)
        ·
          refine ⟨297461714384951430738928793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198307809589967620492619195 297461714384951430738928793)
          ·
            refine ⟨223096285788713573054196595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297461714384951430738928793 223096285788713573054196595)
            ·
              refine ⟨334644428683070359581294893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223096285788713573054196595 334644428683070359581294893)
              ·
                refine ⟨125491660756151384842985585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334644428683070359581294893 125491660756151384842985585)
                ·
                  refine ⟨94118745567113538632239189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125491660756151384842985585 94118745567113538632239189)
                  ·
                    refine ⟨1102954049614611780846553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94118745567113538632239189 1102954049614611780846553)
                    ·
                      rfl

theorem cell22_3221993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3221993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3221993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3221993 prefixEnd_3221993 := by exact prefixLift 3221993
  have htrace : WordTrace (prefixWord ++ tailWord_3221993) baseStart_3221993 baseEnd_3221993 := by
    simpa [prefixWord, tailWord_3221993, baseEnd_3221993] using wordTrace_append hprefix tailTrace_3221993
  have hstable : (prefixWord ++ tailWord_3221993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3221993).length < 2 ^ (prefixWord ++ tailWord_3221993).sum := by decide
  have hdescent : baseEnd_3221993 < baseStart_3221993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3221993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222027 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 1, 4]
def baseStart_3222027 : Nat := 118140960795 + 3222027 * 2 ^ 59
def prefixEnd_3222027 : Nat := 4983230072969 + 3 ^ 40 * 3222027 * 2
def baseEnd_3222027 : Nat := 1102965688509447025496449

theorem tailTrace_3222027 : CollatzResearch.WordTrace tailWord_3222027 prefixEnd_3222027 1102965688509447025496449 := by
  unfold tailWord_3222027
  simp only [CollatzResearch.WordTrace]
  refine ⟨117516979098153932246808335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78344652732102621497872223 117516979098153932246808335)
  ·
    refine ⟨176275468647230898370212503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117516979098153932246808335 176275468647230898370212503)
    ·
      refine ⟨264413202970846347555318755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176275468647230898370212503 264413202970846347555318755)
      ·
        refine ⟨396619804456269521332978133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264413202970846347555318755 396619804456269521332978133)
        ·
          refine ⟨9295776666943816906241675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 396619804456269521332978133 9295776666943816906241675)
          ·
            refine ⟨13943665000415725359362513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295776666943816906241675 13943665000415725359362513)
            ·
              refine ⟨10457748750311794019521885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13943665000415725359362513 10457748750311794019521885)
              ·
                refine ⟨3921655781366922757320707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10457748750311794019521885 3921655781366922757320707)
                ·
                  refine ⟨5882483672050384135981061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921655781366922757320707 5882483672050384135981061)
                  ·
                    refine ⟨1102965688509447025496449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882483672050384135981061 1102965688509447025496449)
                    ·
                      rfl

theorem cell22_3222027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_3222027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222027 prefixEnd_3222027 := by exact prefixLift 3222027
  have htrace : WordTrace (prefixWord ++ tailWord_3222027) baseStart_3222027 baseEnd_3222027 := by
    simpa [prefixWord, tailWord_3222027, baseEnd_3222027] using wordTrace_append hprefix tailTrace_3222027
  have hstable : (prefixWord ++ tailWord_3222027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222027).length < 2 ^ (prefixWord ++ tailWord_3222027).sum := by decide
  have hdescent : baseEnd_3222027 < baseStart_3222027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222042 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_3222042 : Nat := 118140960795 + 3222042 * 2 ^ 59
def prefixEnd_3222042 : Nat := 4983230072969 + 3 ^ 40 * 3222042 * 2
def baseEnd_3222042 : Nat := 367656941105330662123801

theorem tailTrace_3222042 : CollatzResearch.WordTrace tailWord_3222042 prefixEnd_3222042 367656941105330662123801 := by
  unfold tailWord_3222042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29379381548274897452151095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78345017462066393205736253 29379381548274897452151095)
  ·
    refine ⟨44069072322412346178226643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29379381548274897452151095 44069072322412346178226643)
    ·
      refine ⟨66103608483618519267339965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44069072322412346178226643 66103608483618519267339965)
      ·
        refine ⟨24788853181356944725252487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66103608483618519267339965 24788853181356944725252487)
        ·
          refine ⟨37183279772035417087878731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788853181356944725252487 37183279772035417087878731)
          ·
            refine ⟨55774919658053125631818097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37183279772035417087878731 55774919658053125631818097)
            ·
              refine ⟨41831189743539844223863573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55774919658053125631818097 41831189743539844223863573)
              ·
                refine ⟨1960837019228430197993605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41831189743539844223863573 1960837019228430197993605)
                ·
                  refine ⟨367656941105330662123801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960837019228430197993605 367656941105330662123801)
                  ·
                    rfl

theorem cell22_3222042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_3222042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222042 prefixEnd_3222042 := by exact prefixLift 3222042
  have htrace : WordTrace (prefixWord ++ tailWord_3222042) baseStart_3222042 baseEnd_3222042 := by
    simpa [prefixWord, tailWord_3222042, baseEnd_3222042] using wordTrace_append hprefix tailTrace_3222042
  have hstable : (prefixWord ++ tailWord_3222042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222042).length < 2 ^ (prefixWord ++ tailWord_3222042).sum := by decide
  have hdescent : baseEnd_3222042 < baseStart_3222042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222072 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3222072 : Nat := 118140960795 + 3222072 * 2 ^ 59
def prefixEnd_3222072 : Nat := 4983230072969 + 3 ^ 40 * 3222072 * 2
def baseEnd_3222072 : Nat := 1102981092929081908121311

theorem tailTrace_3222072 : CollatzResearch.WordTrace tailWord_3222072 prefixEnd_3222072 1102981092929081908121311 := by
  unfold tailWord_3222072
  simp only [CollatzResearch.WordTrace]
  refine ⟨58759310191495452466098235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78345746921993936621464313 58759310191495452466098235)
  ·
    refine ⟨88138965287243178699147353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58759310191495452466098235 88138965287243178699147353)
    ·
      refine ⟨66104223965432384024360515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88138965287243178699147353 66104223965432384024360515)
      ·
        refine ⟨99156335948148576036540773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66104223965432384024360515 99156335948148576036540773)
        ·
          refine ⟨18591812990277858006851395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99156335948148576036540773 18591812990277858006851395)
          ·
            refine ⟨27887719485416787010277093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18591812990277858006851395 27887719485416787010277093)
            ·
              refine ⟨5228947403515647564426955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27887719485416787010277093 5228947403515647564426955)
              ·
                refine ⟨7843421105273471346640433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228947403515647564426955 7843421105273471346640433)
                ·
                  refine ⟨5882565828955103509980325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843421105273471346640433 5882565828955103509980325)
                  ·
                    refine ⟨1102981092929081908121311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882565828955103509980325 1102981092929081908121311)
                    ·
                      rfl

theorem cell22_3222072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3222072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222072 prefixEnd_3222072 := by exact prefixLift 3222072
  have htrace : WordTrace (prefixWord ++ tailWord_3222072) baseStart_3222072 baseEnd_3222072 := by
    simpa [prefixWord, tailWord_3222072, baseEnd_3222072] using wordTrace_append hprefix tailTrace_3222072
  have hstable : (prefixWord ++ tailWord_3222072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222072).length < 2 ^ (prefixWord ++ tailWord_3222072).sum := by decide
  have hdescent : baseEnd_3222072 < baseStart_3222072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222078 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_3222078 : Nat := 118140960795 + 3222078 * 2 ^ 59
def prefixEnd_3222078 : Nat := 4983230072969 + 3 ^ 40 * 3222078 * 2
def baseEnd_3222078 : Nat := 1102983146851699892471293

theorem tailTrace_3222078 : CollatzResearch.WordTrace tailWord_3222078 prefixEnd_3222078 1102983146851699892471293 := by
  unfold tailWord_3222078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689854902621145994614361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78345892813979445304609925 14689854902621145994614361)
  ·
    refine ⟨11017391176965859495960771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14689854902621145994614361 11017391176965859495960771)
    ·
      refine ⟨16526086765448789243941157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017391176965859495960771 16526086765448789243941157)
      ·
        refine ⟨3098641268521647983238967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16526086765448789243941157 3098641268521647983238967)
        ·
          refine ⟨4647961902782471974858451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098641268521647983238967 4647961902782471974858451)
          ·
            refine ⟨6971942854173707962287677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647961902782471974858451 6971942854173707962287677)
            ·
              refine ⟨2614478570315140485857879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6971942854173707962287677 2614478570315140485857879)
              ·
                refine ⟨3921717855472710728786819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614478570315140485857879 3921717855472710728786819)
                ·
                  refine ⟨5882576783209066093180229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921717855472710728786819 5882576783209066093180229)
                  ·
                    refine ⟨1102983146851699892471293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882576783209066093180229 1102983146851699892471293)
                    ·
                      rfl

theorem cell22_3222078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_3222078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222078 prefixEnd_3222078 := by exact prefixLift 3222078
  have htrace : WordTrace (prefixWord ++ tailWord_3222078) baseStart_3222078 baseEnd_3222078 := by
    simpa [prefixWord, tailWord_3222078, baseEnd_3222078] using wordTrace_append hprefix tailTrace_3222078
  have hstable : (prefixWord ++ tailWord_3222078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222078).length < 2 ^ (prefixWord ++ tailWord_3222078).sum := by decide
  have hdescent : baseEnd_3222078 < baseStart_3222078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222093 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3222093 : Nat := 118140960795 + 3222093 * 2 ^ 59
def prefixEnd_3222093 : Nat := 4983230072969 + 3 ^ 40 * 3222093 * 2
def baseEnd_3222093 : Nat := 367662760552748284448749

theorem tailTrace_3222093 : CollatzResearch.WordTrace tailWord_3222093 prefixEnd_3222093 367662760552748284448749 := by
  unfold tailWord_3222093
  simp only [CollatzResearch.WordTrace]
  refine ⟨117519386315914825518710933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78346257543943217012473955 117519386315914825518710933)
  ·
    refine ⟨5508721233558507446189575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117519386315914825518710933 5508721233558507446189575)
    ·
      refine ⟨8263081850337761169284363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508721233558507446189575 8263081850337761169284363)
      ·
        refine ⟨12394622775506641753926545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263081850337761169284363 12394622775506641753926545)
        ·
          refine ⟨9295967081629981315444909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12394622775506641753926545 9295967081629981315444909)
          ·
            refine ⟨3485987655611242993291841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9295967081629981315444909 3485987655611242993291841)
            ·
              refine ⟨2614490741708432244968881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485987655611242993291841 2614490741708432244968881)
              ·
                refine ⟨1960868056281324183726661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614490741708432244968881 1960868056281324183726661)
                ·
                  refine ⟨367662760552748284448749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960868056281324183726661 367662760552748284448749)
                  ·
                    rfl

theorem cell22_3222093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3222093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222093 prefixEnd_3222093 := by exact prefixLift 3222093
  have htrace : WordTrace (prefixWord ++ tailWord_3222093) baseStart_3222093 baseEnd_3222093 := by
    simpa [prefixWord, tailWord_3222093, baseEnd_3222093] using wordTrace_append hprefix tailTrace_3222093
  have hstable : (prefixWord ++ tailWord_3222093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222093).length < 2 ^ (prefixWord ++ tailWord_3222093).sum := by decide
  have hdescent : baseEnd_3222093 < baseStart_3222093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222149 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 5]
def baseStart_3222149 : Nat := 118140960795 + 3222149 * 2 ^ 59
def prefixEnd_3222149 : Nat := 4983230072969 + 3 ^ 40 * 3222149 * 2
def baseEnd_3222149 : Nat := 367669150534226457982025

theorem tailTrace_3222149 : CollatzResearch.WordTrace tailWord_3222149 prefixEnd_3222149 367669150534226457982025 := by
  unfold tailWord_3222149
  simp only [CollatzResearch.WordTrace]
  refine ⟨117521428803711947082749501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78347619202474631388499667 117521428803711947082749501)
  ·
    refine ⟨44070535801391980156031063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117521428803711947082749501 44070535801391980156031063)
    ·
      refine ⟨66105803702087970234046595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44070535801391980156031063 66105803702087970234046595)
      ·
        refine ⟨99158705553131955351069893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66105803702087970234046595 99158705553131955351069893)
        ·
          refine ⟨18592257291212241628325605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99158705553131955351069893 18592257291212241628325605)
          ·
            refine ⟨3486048242102295305311051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18592257291212241628325605 3486048242102295305311051)
            ·
              refine ⟨5229072363153442957966577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486048242102295305311051 5229072363153442957966577)
              ·
                refine ⟨3921804272365082218474933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229072363153442957966577 3921804272365082218474933)
                ·
                  refine ⟨367669150534226457982025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921804272365082218474933 367669150534226457982025)
                  ·
                    rfl

theorem cell22_3222149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_3222149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222149 prefixEnd_3222149 := by exact prefixLift 3222149
  have htrace : WordTrace (prefixWord ++ tailWord_3222149) baseStart_3222149 baseEnd_3222149 := by
    simpa [prefixWord, tailWord_3222149, baseEnd_3222149] using wordTrace_append hprefix tailTrace_3222149
  have hstable : (prefixWord ++ tailWord_3222149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222149).length < 2 ^ (prefixWord ++ tailWord_3222149).sum := by decide
  have hdescent : baseEnd_3222149 < baseStart_3222149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222164 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3222164 : Nat := 118140960795 + 3222164 * 2 ^ 59
def prefixEnd_3222164 : Nat := 4983230072969 + 3 ^ 40 * 3222164 * 2
def baseEnd_3222164 : Nat := 1103012586409224334821029

theorem tailTrace_3222164 : CollatzResearch.WordTrace tailWord_3222164 prefixEnd_3222164 1103012586409224334821029 := by
  unfold tailWord_3222164
  simp only [CollatzResearch.WordTrace]
  refine ⟨58760987949328802322272773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78347983932438403096363697 58760987949328802322272773)
  ·
    refine ⟨11017685240499150435426145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58760987949328802322272773 11017685240499150435426145)
    ·
      refine ⟨8263263930374362826569609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11017685240499150435426145 8263263930374362826569609)
      ·
        refine ⟨6197447947780772119927207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8263263930374362826569609 6197447947780772119927207)
        ·
          refine ⟨9296171921671158179890811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197447947780772119927207 9296171921671158179890811)
          ·
            refine ⟨13944257882506737269836217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9296171921671158179890811 13944257882506737269836217)
            ·
              refine ⟨10458193411880052952377163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13944257882506737269836217 10458193411880052952377163)
              ·
                refine ⟨15687290117820079428565745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458193411880052952377163 15687290117820079428565745)
                ·
                  refine ⟨11765467588365059571424309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15687290117820079428565745 11765467588365059571424309)
                  ·
                    refine ⟨1103012586409224334821029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11765467588365059571424309 1103012586409224334821029)
                    ·
                      rfl

theorem cell22_3222164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3222164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222164 prefixEnd_3222164 := by exact prefixLift 3222164
  have htrace : WordTrace (prefixWord ++ tailWord_3222164) baseStart_3222164 baseEnd_3222164 := by
    simpa [prefixWord, tailWord_3222164, baseEnd_3222164] using wordTrace_append hprefix tailTrace_3222164
  have hstable : (prefixWord ++ tailWord_3222164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222164).length < 2 ^ (prefixWord ++ tailWord_3222164).sum := by decide
  have hdescent : baseEnd_3222164 < baseStart_3222164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222207 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_3222207 : Nat := 118140960795 + 3222207 * 2 ^ 59
def prefixEnd_3222207 : Nat := 4983230072969 + 3 ^ 40 * 3222207 * 2
def baseEnd_3222207 : Nat := 1103027306187986555995897

theorem tailTrace_3222207 : CollatzResearch.WordTrace tailWord_3222207 prefixEnd_3222207 1103027306187986555995897 := by
  unfold tailWord_3222207
  simp only [CollatzResearch.WordTrace]
  refine ⟨117523544237501822988360875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78349029491667881992240583 117523544237501822988360875)
  ·
    refine ⟨176285316356252734482541313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117523544237501822988360875 176285316356252734482541313)
    ·
      refine ⟨132213987267189550861905985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176285316356252734482541313 132213987267189550861905985)
      ·
        refine ⟨99160490450392163146429489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132213987267189550861905985 99160490450392163146429489)
        ·
          refine ⟨74370367837794122359822117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99160490450392163146429489 74370367837794122359822117)
          ·
            refine ⟨13944443969586397942466647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74370367837794122359822117 13944443969586397942466647)
            ·
              refine ⟨20916665954379596913699971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13944443969586397942466647 20916665954379596913699971)
              ·
                refine ⟨31374998931569395370549957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20916665954379596913699971 31374998931569395370549957)
                ·
                  refine ⟨5882812299669261631978117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31374998931569395370549957 5882812299669261631978117)
                  ·
                    refine ⟨1103027306187986555995897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882812299669261631978117 1103027306187986555995897)
                    ·
                      rfl

theorem cell22_3222207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_3222207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222207 prefixEnd_3222207 := by exact prefixLift 3222207
  have htrace : WordTrace (prefixWord ++ tailWord_3222207) baseStart_3222207 baseEnd_3222207 := by
    simpa [prefixWord, tailWord_3222207, baseEnd_3222207] using wordTrace_append hprefix tailTrace_3222207
  have hstable : (prefixWord ++ tailWord_3222207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222207).length < 2 ^ (prefixWord ++ tailWord_3222207).sum := by decide
  have hdescent : baseEnd_3222207 < baseStart_3222207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222222 : List Nat := [4, 1, 1, 1, 3, 2, 1, 9]
def baseStart_3222222 : Nat := 118140960795 + 3222222 * 2 ^ 59
def prefixEnd_3222222 : Nat := 4983230072969 + 3 ^ 40 * 3222222 * 2
def baseEnd_3222222 : Nat := 122559160110503501874539

theorem tailTrace_3222222 : CollatzResearch.WordTrace tailWord_3222222 prefixEnd_3222222 122559160110503501874539 := by
  unfold tailWord_3222222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14690511416555935068769615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78349394221631653700104613 14690511416555935068769615)
  ·
    refine ⟨22035767124833902603154423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14690511416555935068769615 22035767124833902603154423)
    ·
      refine ⟨33053650687250853904731635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22035767124833902603154423 33053650687250853904731635)
      ·
        refine ⟨49580476030876280857097453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33053650687250853904731635 49580476030876280857097453)
        ·
          refine ⟨18592678511578605321411545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49580476030876280857097453 18592678511578605321411545)
          ·
            refine ⟨13944508883683953991058659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18592678511578605321411545 13944508883683953991058659)
            ·
              refine ⟨20916763325525930986587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13944508883683953991058659 20916763325525930986587989)
              ·
                refine ⟨122559160110503501874539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20916763325525930986587989 122559160110503501874539)
                ·
                  rfl

theorem cell22_3222222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_3222222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222222 prefixEnd_3222222 := by exact prefixLift 3222222
  have htrace : WordTrace (prefixWord ++ tailWord_3222222) baseStart_3222222 baseEnd_3222222 := by
    simpa [prefixWord, tailWord_3222222, baseEnd_3222222] using wordTrace_append hprefix tailTrace_3222222
  have hstable : (prefixWord ++ tailWord_3222222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222222).length < 2 ^ (prefixWord ++ tailWord_3222222).sum := by decide
  have hdescent : baseEnd_3222222 < baseStart_3222222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222318 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_3222318 : Nat := 118140960795 + 3222318 * 2 ^ 59
def prefixEnd_3222318 : Nat := 4983230072969 + 3 ^ 40 * 3222318 * 2
def baseEnd_3222318 : Nat := 367688434585473088823519

theorem tailTrace_3222318 : CollatzResearch.WordTrace tailWord_3222318 prefixEnd_3222318 367688434585473088823519 := by
  unfold tailWord_3222318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14690949092512461118206451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78351728493399792630434405 14690949092512461118206451)
  ·
    refine ⟨22036423638768691677309677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14690949092512461118206451 22036423638768691677309677)
    ·
      refine ⟨8263658864538259378991129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22036423638768691677309677 8263658864538259378991129)
      ·
        refine ⟨6197744148403694534243347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8263658864538259378991129 6197744148403694534243347)
        ·
          refine ⟨9296616222605541801365021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197744148403694534243347 9296616222605541801365021)
          ·
            refine ⟨3486231083477078175511883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9296616222605541801365021 3486231083477078175511883)
            ·
              refine ⟨5229346625215617263267825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486231083477078175511883 5229346625215617263267825)
              ·
                refine ⟨3922009968911712947450869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229346625215617263267825 3922009968911712947450869)
                ·
                  refine ⟨367688434585473088823519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922009968911712947450869 367688434585473088823519)
                  ·
                    rfl

theorem cell22_3222318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_3222318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222318 prefixEnd_3222318 := by exact prefixLift 3222318
  have htrace : WordTrace (prefixWord ++ tailWord_3222318) baseStart_3222318 baseEnd_3222318 := by
    simpa [prefixWord, tailWord_3222318, baseEnd_3222318] using wordTrace_append hprefix tailTrace_3222318
  have hstable : (prefixWord ++ tailWord_3222318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222318).length < 2 ^ (prefixWord ++ tailWord_3222318).sum := by decide
  have hdescent : baseEnd_3222318 < baseStart_3222318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222359 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3222359 : Nat := 118140960795 + 3222359 * 2 ^ 59
def prefixEnd_3222359 : Nat := 4983230072969 + 3 ^ 40 * 3222359 * 2
def baseEnd_3222359 : Nat := 1103079338894308826195431

theorem tailTrace_3222359 : CollatzResearch.WordTrace tailWord_3222359 prefixEnd_3222359 1103079338894308826195431 := by
  unfold tailWord_3222359
  simp only [CollatzResearch.WordTrace]
  refine ⟨117529088132951152947894131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78352725421967435298596087 117529088132951152947894131)
  ·
    refine ⟨176293632199426729421841197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117529088132951152947894131 176293632199426729421841197)
    ·
      refine ⟨66110112074785023533190449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176293632199426729421841197 66110112074785023533190449)
      ·
        refine ⟨49582584056088767649892837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66110112074785023533190449 49582584056088767649892837)
        ·
          refine ⟨9296734510516643934354907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49582584056088767649892837 9296734510516643934354907)
          ·
            refine ⟨13945101765774965901532361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9296734510516643934354907 13945101765774965901532361)
            ·
              refine ⟨10458826324331224426149271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13945101765774965901532361 10458826324331224426149271)
              ·
                refine ⟨15688239486496836639223907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458826324331224426149271 15688239486496836639223907)
                ·
                  refine ⟨23532359229745254958835861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688239486496836639223907 23532359229745254958835861)
                  ·
                    refine ⟨1103079338894308826195431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23532359229745254958835861 1103079338894308826195431)
                    ·
                      rfl

theorem cell22_3222359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3222359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222359 prefixEnd_3222359 := by exact prefixLift 3222359
  have htrace : WordTrace (prefixWord ++ tailWord_3222359) baseStart_3222359 baseEnd_3222359 := by
    simpa [prefixWord, tailWord_3222359, baseEnd_3222359] using wordTrace_append hprefix tailTrace_3222359
  have hstable : (prefixWord ++ tailWord_3222359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222359).length < 2 ^ (prefixWord ++ tailWord_3222359).sum := by decide
  have hdescent : baseEnd_3222359 < baseStart_3222359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222376 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3222376 : Nat := 118140960795 + 3222376 * 2 ^ 59
def prefixEnd_3222376 : Nat := 4983230072969 + 3 ^ 40 * 3222376 * 2
def baseEnd_3222376 : Nat := 1103085158341726448520379

theorem tailTrace_3222376 : CollatzResearch.WordTrace tailWord_3222376 prefixEnd_3222376 1103085158341726448520379 := by
  unfold tailWord_3222376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58764854086944782425631491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78353138782593043234175321 58764854086944782425631491)
  ·
    refine ⟨88147281130417173638447237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58764854086944782425631491 88147281130417173638447237)
    ·
      refine ⟨16527615211953220057208857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88147281130417173638447237 16527615211953220057208857)
      ·
        refine ⟨12395711408964915042906643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16527615211953220057208857 12395711408964915042906643)
        ·
          refine ⟨18593567113447372564359965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395711408964915042906643 18593567113447372564359965)
          ·
            refine ⟨6972587667542764711634987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18593567113447372564359965 6972587667542764711634987)
            ·
              refine ⟨10458881501314147067452481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972587667542764711634987 10458881501314147067452481)
              ·
                refine ⟨7844161125985610300589361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10458881501314147067452481 7844161125985610300589361)
                ·
                  refine ⟨5883120844489207725442021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7844161125985610300589361 5883120844489207725442021)
                  ·
                    refine ⟨1103085158341726448520379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883120844489207725442021 1103085158341726448520379)
                    ·
                      rfl

theorem cell22_3222376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3222376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222376 prefixEnd_3222376 := by exact prefixLift 3222376
  have htrace : WordTrace (prefixWord ++ tailWord_3222376) baseStart_3222376 baseEnd_3222376 := by
    simpa [prefixWord, tailWord_3222376, baseEnd_3222376] using wordTrace_append hprefix tailTrace_3222376
  have hstable : (prefixWord ++ tailWord_3222376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222376).length < 2 ^ (prefixWord ++ tailWord_3222376).sum := by decide
  have hdescent : baseEnd_3222376 < baseStart_3222376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222423 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 1, 3]
def baseStart_3222423 : Nat := 118140960795 + 3222423 * 2 ^ 59
def prefixEnd_3222423 : Nat := 4983230072969 + 3 ^ 40 * 3222423 * 2
def baseEnd_3222423 : Nat := 1103101247402233992595235

theorem tailTrace_3222423 : CollatzResearch.WordTrace tailWord_3222423 prefixEnd_3222423 1103101247402233992595235 := by
  unfold tailWord_3222423
  simp only [CollatzResearch.WordTrace]
  refine ⟨117531422404719291878223923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78354281603146194585482615 117531422404719291878223923)
  ·
    refine ⟨176297133607078937817335885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117531422404719291878223923 176297133607078937817335885)
    ·
      refine ⟨66111425102654601681500957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176297133607078937817335885 66111425102654601681500957)
      ·
        refine ⟨24791784413495475630562859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66111425102654601681500957 24791784413495475630562859)
        ·
          refine ⟨37187676620243213445844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791784413495475630562859 37187676620243213445844289)
          ·
            refine ⟨27890757465182410084383217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37187676620243213445844289 27890757465182410084383217)
            ·
              refine ⟨20918068098886807563287413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27890757465182410084383217 20918068098886807563287413)
              ·
                refine ⟨1961068884270638209058195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20918068098886807563287413 1961068884270638209058195)
                ·
                  refine ⟨2941603326405957313587293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961068884270638209058195 2941603326405957313587293)
                  ·
                    refine ⟨1103101247402233992595235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941603326405957313587293 1103101247402233992595235)
                    ·
                      rfl

theorem cell22_3222423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_3222423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222423 prefixEnd_3222423 := by exact prefixLift 3222423
  have htrace : WordTrace (prefixWord ++ tailWord_3222423) baseStart_3222423 baseEnd_3222423 := by
    simpa [prefixWord, tailWord_3222423, baseEnd_3222423] using wordTrace_append hprefix tailTrace_3222423
  have hstable : (prefixWord ++ tailWord_3222423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222423).length < 2 ^ (prefixWord ++ tailWord_3222423).sum := by decide
  have hdescent : baseEnd_3222423 < baseStart_3222423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222436 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3222436 : Nat := 118140960795 + 3222436 * 2 ^ 59
def prefixEnd_3222436 : Nat := 4983230072969 + 3 ^ 40 * 3222436 * 2
def baseEnd_3222436 : Nat := 367701899189302097340065

theorem tailTrace_3222436 : CollatzResearch.WordTrace tailWord_3222436 prefixEnd_3222436 367701899189302097340065 := by
  unfold tailWord_3222436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58765948276836097549223581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78354597702448130065631441 58765948276836097549223581)
  ·
    refine ⟨22037230603813536580958843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58765948276836097549223581 22037230603813536580958843)
    ·
      refine ⟨33055845905720304871438265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22037230603813536580958843 33055845905720304871438265)
      ·
        refine ⟨24791884429290228653578699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33055845905720304871438265 24791884429290228653578699)
        ·
          refine ⟨37187826643935342980368049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791884429290228653578699 37187826643935342980368049)
          ·
            refine ⟨27890869982951507235276037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37187826643935342980368049 27890869982951507235276037)
            ·
              refine ⟨5229538121803407606614257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27890869982951507235276037 5229538121803407606614257)
              ·
                refine ⟨3922153591352555704960693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229538121803407606614257 3922153591352555704960693)
                ·
                  refine ⟨367701899189302097340065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922153591352555704960693 367701899189302097340065)
                  ·
                    rfl

theorem cell22_3222436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3222436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222436 prefixEnd_3222436 := by exact prefixLift 3222436
  have htrace : WordTrace (prefixWord ++ tailWord_3222436) baseStart_3222436 baseEnd_3222436 := by
    simpa [prefixWord, tailWord_3222436, baseEnd_3222436] using wordTrace_append hprefix tailTrace_3222436
  have hstable : (prefixWord ++ tailWord_3222436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222436).length < 2 ^ (prefixWord ++ tailWord_3222436).sum := by decide
  have hdescent : baseEnd_3222436 < baseStart_3222436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222464 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_3222464 : Nat := 118140960795 + 3222464 * 2 ^ 59
def prefixEnd_3222464 : Nat := 4983230072969 + 3 ^ 40 * 3222464 * 2
def baseEnd_3222464 : Nat := 367705094180041184106703

theorem tailTrace_3222464 : CollatzResearch.WordTrace tailWord_3222464 prefixEnd_3222464 367705094180041184106703 := by
  unfold tailWord_3222464
  simp only [CollatzResearch.WordTrace]
  refine ⟨58766458898785377940233223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78355278531713837253644297 58766458898785377940233223)
  ·
    refine ⟨88149688348178066910349835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58766458898785377940233223 88149688348178066910349835)
    ·
      refine ⟨132224532522267100365524753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88149688348178066910349835 132224532522267100365524753)
      ·
        refine ⟨99168399391700325274143565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132224532522267100365524753 99168399391700325274143565)
        ·
          refine ⟨37188149771887621977803837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99168399391700325274143565 37188149771887621977803837)
          ·
            refine ⟨13945556164457858241676439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37188149771887621977803837 13945556164457858241676439)
            ·
              refine ⟨20918334246686787362514659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945556164457858241676439 20918334246686787362514659)
              ·
                refine ⟨31377501370030181043771989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20918334246686787362514659 31377501370030181043771989)
                ·
                  refine ⟨367705094180041184106703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31377501370030181043771989 367705094180041184106703)
                  ·
                    rfl

theorem cell22_3222464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_3222464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222464 prefixEnd_3222464 := by exact prefixLift 3222464
  have htrace : WordTrace (prefixWord ++ tailWord_3222464) baseStart_3222464 baseEnd_3222464 := by
    simpa [prefixWord, tailWord_3222464, baseEnd_3222464] using wordTrace_append hprefix tailTrace_3222464
  have hstable : (prefixWord ++ tailWord_3222464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222464).length < 2 ^ (prefixWord ++ tailWord_3222464).sum := by decide
  have hdescent : baseEnd_3222464 < baseStart_3222464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222498 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3222498 : Nat := 118140960795 + 3222498 * 2 ^ 59
def prefixEnd_3222498 : Nat := 4983230072969 + 3 ^ 40 * 3222498 * 2
def baseEnd_3222498 : Nat := 367708973811652932323335

theorem tailTrace_3222498 : CollatzResearch.WordTrace tailWord_3222498 prefixEnd_3222498 367708973811652932323335 := by
  unfold tailWord_3222498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29383539469861894921801037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78356105252965053124802765 29383539469861894921801037)
  ·
    refine ⟨11018827301198210595675389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29383539469861894921801037 11018827301198210595675389)
    ·
      refine ⟨4132060237949328973378271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11018827301198210595675389 4132060237949328973378271)
      ·
        refine ⟨6198090356923993460067407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132060237949328973378271 6198090356923993460067407)
        ·
          refine ⟨9297135535385990190101111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198090356923993460067407 9297135535385990190101111)
          ·
            refine ⟨13945703303078985285151667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297135535385990190101111 13945703303078985285151667)
            ·
              refine ⟨20918554954618477927727501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945703303078985285151667 20918554954618477927727501)
              ·
                refine ⟨7844458107981929222897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20918554954618477927727501 7844458107981929222897813)
                ·
                  refine ⟨367708973811652932323335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7844458107981929222897813 367708973811652932323335)
                  ·
                    rfl

theorem cell22_3222498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3222498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222498 prefixEnd_3222498 := by exact prefixLift 3222498
  have htrace : WordTrace (prefixWord ++ tailWord_3222498) baseStart_3222498 baseEnd_3222498 := by
    simpa [prefixWord, tailWord_3222498, baseEnd_3222498] using wordTrace_append hprefix tailTrace_3222498
  have hstable : (prefixWord ++ tailWord_3222498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222498).length < 2 ^ (prefixWord ++ tailWord_3222498).sum := by decide
  have hdescent : baseEnd_3222498 < baseStart_3222498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222513 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_3222513 : Nat := 118140960795 + 3222513 * 2 ^ 59
def prefixEnd_3222513 : Nat := 4983230072969 + 3 ^ 40 * 3222513 * 2
def baseEnd_3222513 : Nat := 1103132056241503757844959

theorem tailTrace_3222513 : CollatzResearch.WordTrace tailWord_3222513 prefixEnd_3222513 1103132056241503757844959 := by
  unfold tailWord_3222513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117534704974393237249000193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78356469982928824832666795 117534704974393237249000193)
  ·
    refine ⟨88151028730794927936750145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117534704974393237249000193 88151028730794927936750145)
    ·
      refine ⟨66113271548096195952562609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88151028730794927936750145 66113271548096195952562609)
      ·
        refine ⟨49584953661072146964421957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66113271548096195952562609 49584953661072146964421957)
        ·
          refine ⟨9297178811451027555829117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49584953661072146964421957 9297178811451027555829117)
          ·
            refine ⟨3486442054294135333435919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9297178811451027555829117 3486442054294135333435919)
            ·
              refine ⟨5229663081441203000153879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486442054294135333435919 5229663081441203000153879)
              ·
                refine ⟨7844494622161804500230819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229663081441203000153879 7844494622161804500230819)
                ·
                  refine ⟨11766741933242706750346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844494622161804500230819 11766741933242706750346229)
                  ·
                    refine ⟨1103132056241503757844959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11766741933242706750346229 1103132056241503757844959)
                    ·
                      rfl

theorem cell22_3222513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_3222513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222513 prefixEnd_3222513 := by exact prefixLift 3222513
  have htrace : WordTrace (prefixWord ++ tailWord_3222513) baseStart_3222513 baseEnd_3222513 := by
    simpa [prefixWord, tailWord_3222513, baseEnd_3222513] using wordTrace_append hprefix tailTrace_3222513
  have hstable : (prefixWord ++ tailWord_3222513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222513).length < 2 ^ (prefixWord ++ tailWord_3222513).sum := by decide
  have hdescent : baseEnd_3222513 < baseStart_3222513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222517 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3222517 : Nat := 118140960795 + 3222517 * 2 ^ 59
def prefixEnd_3222517 : Nat := 4983230072969 + 3 ^ 40 * 3222517 * 2
def baseEnd_3222517 : Nat := 1103133425523249080744947

theorem tailTrace_3222517 : CollatzResearch.WordTrace tailWord_3222517 prefixEnd_3222517 1103133425523249080744947 := by
  unfold tailWord_3222517
  simp only [CollatzResearch.WordTrace]
  refine ⟨117534850866378745932145805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78356567244252497288097203 117534850866378745932145805)
  ·
    refine ⟨44075569074892029724554677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117534850866378745932145805 44075569074892029724554677)
    ·
      refine ⟨4132084600771127786677001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44075569074892029724554677 4132084600771127786677001)
      ·
        refine ⟨3099063450578345840007751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132084600771127786677001 3099063450578345840007751)
        ·
          refine ⟨4648595175867518760011627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099063450578345840007751 4648595175867518760011627)
          ·
            refine ⟨6972892763801278140017441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648595175867518760011627 6972892763801278140017441)
            ·
              refine ⟨5229669572850958605013081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6972892763801278140017441 5229669572850958605013081)
              ·
                refine ⟨3922252179638218953759811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229669572850958605013081 3922252179638218953759811)
                ·
                  refine ⟨5883378269457328430639717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922252179638218953759811 5883378269457328430639717)
                  ·
                    refine ⟨1103133425523249080744947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883378269457328430639717 1103133425523249080744947)
                    ·
                      rfl

theorem cell22_3222517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3222517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222517 prefixEnd_3222517 := by exact prefixLift 3222517
  have htrace : WordTrace (prefixWord ++ tailWord_3222517) baseStart_3222517 baseEnd_3222517 := by
    simpa [prefixWord, tailWord_3222517, baseEnd_3222517] using wordTrace_append hprefix tailTrace_3222517
  have hstable : (prefixWord ++ tailWord_3222517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222517).length < 2 ^ (prefixWord ++ tailWord_3222517).sum := by decide
  have hdescent : baseEnd_3222517 < baseStart_3222517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222571 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 5]
def baseStart_3222571 : Nat := 118140960795 + 3222571 * 2 ^ 59
def prefixEnd_3222571 : Nat := 4983230072969 + 3 ^ 40 * 3222571 * 2
def baseEnd_3222571 : Nat := 367717303608936979964927

theorem tailTrace_3222571 : CollatzResearch.WordTrace tailWord_3222571 prefixEnd_3222571 367717303608936979964927 := by
  unfold tailWord_3222571
  simp only [CollatzResearch.WordTrace]
  refine ⟨117536820408183113154611567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78357880272122075436407711 117536820408183113154611567)
  ·
    refine ⟨176305230612274669731917351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117536820408183113154611567 176305230612274669731917351)
    ·
      refine ⟨264457845918412004597876027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176305230612274669731917351 264457845918412004597876027)
      ·
        refine ⟨396686768877618006896814041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264457845918412004597876027 396686768877618006896814041)
        ·
          refine ⟨297515076658213505172610531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396686768877618006896814041 297515076658213505172610531)
          ·
            refine ⟨446272614987320257758915797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297515076658213505172610531 446272614987320257758915797)
            ·
              refine ⟨10459514413765318541224589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 446272614987320257758915797 10459514413765318541224589)
              ·
                refine ⟨3922317905161994452959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10459514413765318541224589 3922317905161994452959221)
                ·
                  refine ⟨367717303608936979964927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922317905161994452959221 367717303608936979964927)
                  ·
                    rfl

theorem cell22_3222571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].length) (baseStart_3222571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222571 prefixEnd_3222571 := by exact prefixLift 3222571
  have htrace : WordTrace (prefixWord ++ tailWord_3222571) baseStart_3222571 baseEnd_3222571 := by
    simpa [prefixWord, tailWord_3222571, baseEnd_3222571] using wordTrace_append hprefix tailTrace_3222571
  have hstable : (prefixWord ++ tailWord_3222571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222571).length < 2 ^ (prefixWord ++ tailWord_3222571).sum := by decide
  have hdescent : baseEnd_3222571 < baseStart_3222571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222605 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3222605 : Nat := 118140960795 + 3222605 * 2 ^ 59
def prefixEnd_3222605 : Nat := 4983230072969 + 3 ^ 40 * 3222605 * 2
def baseEnd_3222605 : Nat := 367721183240548728181559

theorem tailTrace_3222605 : CollatzResearch.WordTrace tailWord_3222605 prefixEnd_3222605 367721183240548728181559 := by
  unfold tailWord_3222605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117538060490059936961349269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78358706993373291307566179 117538060490059936961349269)
  ·
    refine ⟨5509596585471559545063247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117538060490059936961349269 5509596585471559545063247)
    ·
      refine ⟨8264394878207339317594871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509596585471559545063247 8264394878207339317594871)
      ·
        refine ⟨12396592317311008976392307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8264394878207339317594871 12396592317311008976392307)
        ·
          refine ⟨18594888475966513464588461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12396592317311008976392307 18594888475966513464588461)
          ·
            refine ⟨6973083178487442549220673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18594888475966513464588461 6973083178487442549220673)
            ·
              refine ⟨5229812383865581911915505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973083178487442549220673 5229812383865581911915505)
              ·
                refine ⟨3922359287899186433936629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229812383865581911915505 3922359287899186433936629)
                ·
                  refine ⟨367721183240548728181559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922359287899186433936629 367721183240548728181559)
                  ·
                    rfl

theorem cell22_3222605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3222605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222605 prefixEnd_3222605 := by exact prefixLift 3222605
  have htrace : WordTrace (prefixWord ++ tailWord_3222605) baseStart_3222605 baseEnd_3222605 := by
    simpa [prefixWord, tailWord_3222605, baseEnd_3222605] using wordTrace_append hprefix tailTrace_3222605
  have hstable : (prefixWord ++ tailWord_3222605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222605).length < 2 ^ (prefixWord ++ tailWord_3222605).sum := by decide
  have hdescent : baseEnd_3222605 < baseStart_3222605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222616 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_3222616 : Nat := 118140960795 + 3222616 * 2 ^ 59
def prefixEnd_3222616 : Nat := 4983230072969 + 3 ^ 40 * 3222616 * 2
def baseEnd_3222616 : Nat := 367722438415481940839881

theorem tailTrace_3222616 : CollatzResearch.WordTrace tailWord_3222616 prefixEnd_3222616 367722438415481940839881 := by
  unfold tailWord_3222616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58769230846510042919999851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78358974462013390559999801 58769230846510042919999851)
  ·
    refine ⟨88153846269765064379999777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58769230846510042919999851 88153846269765064379999777)
    ·
      refine ⟨66115384702323798284999833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88153846269765064379999777 66115384702323798284999833)
      ·
        refine ⟨49586538526742848713749875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66115384702323798284999833 49586538526742848713749875)
        ·
          refine ⟨74379807790114273070624813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49586538526742848713749875 74379807790114273070624813)
          ·
            refine ⟨27892427921292852401484305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74379807790114273070624813 27892427921292852401484305)
            ·
              refine ⟨20919320940969639301113229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27892427921292852401484305 20919320940969639301113229)
              ·
                refine ⟨7844745352863614737917461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20919320940969639301113229 7844745352863614737917461)
                ·
                  refine ⟨367722438415481940839881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7844745352863614737917461 367722438415481940839881)
                  ·
                    rfl

theorem cell22_3222616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_3222616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222616 prefixEnd_3222616 := by exact prefixLift 3222616
  have htrace : WordTrace (prefixWord ++ tailWord_3222616) baseStart_3222616 baseEnd_3222616 := by
    simpa [prefixWord, tailWord_3222616, baseEnd_3222616] using wordTrace_append hprefix tailTrace_3222616
  have hstable : (prefixWord ++ tailWord_3222616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222616).length < 2 ^ (prefixWord ++ tailWord_3222616).sum := by decide
  have hdescent : baseEnd_3222616 < baseStart_3222616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222622 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3222622 : Nat := 118140960795 + 3222622 * 2 ^ 59
def prefixEnd_3222622 : Nat := 4983230072969 + 3 ^ 40 * 3222622 * 2
def baseEnd_3222622 : Nat := 367723123056354602289875

theorem tailTrace_3222622 : CollatzResearch.WordTrace tailWord_3222622 prefixEnd_3222622 367723123056354602289875 := by
  unfold tailWord_3222622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692335066374793608089765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78359120353998899243145413 14692335066374793608089765)
  ·
    refine ⟨2754812824945273801516831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14692335066374793608089765 2754812824945273801516831)
    ·
      refine ⟨4132219237417910702275247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754812824945273801516831 4132219237417910702275247)
      ·
        refine ⟨6198328856126866053412871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132219237417910702275247 6198328856126866053412871)
        ·
          refine ⟨9297493284190299080119307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198328856126866053412871 9297493284190299080119307)
          ·
            refine ⟨13946239926285448620178961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297493284190299080119307 13946239926285448620178961)
            ·
              refine ⟨10459679944714086465134221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13946239926285448620178961 10459679944714086465134221)
              ·
                refine ⟨3922379979267782424425333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10459679944714086465134221 3922379979267782424425333)
                ·
                  refine ⟨367723123056354602289875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922379979267782424425333 367723123056354602289875)
                  ·
                    rfl

theorem cell22_3222622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3222622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222622 prefixEnd_3222622 := by exact prefixLift 3222622
  have htrace : WordTrace (prefixWord ++ tailWord_3222622) baseStart_3222622 baseEnd_3222622 := by
    simpa [prefixWord, tailWord_3222622, baseEnd_3222622] using wordTrace_append hprefix tailTrace_3222622
  have hstable : (prefixWord ++ tailWord_3222622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222622).length < 2 ^ (prefixWord ++ tailWord_3222622).sum := by decide
  have hdescent : baseEnd_3222622 < baseStart_3222622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222665 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_3222665 : Nat := 118140960795 + 3222665 * 2 ^ 59
def prefixEnd_3222665 : Nat := 4983230072969 + 3 ^ 40 * 3222665 * 2
def baseEnd_3222665 : Nat := 1103184088947826028044493

theorem tailTrace_3222665 : CollatzResearch.WordTrace tailWord_3222665 prefixEnd_3222665 1103184088947826028044493 := by
  unfold tailWord_3222665
  simp only [CollatzResearch.WordTrace]
  refine ⟨117540248869842567208533449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78360165913228378139022299 117540248869842567208533449)
  ·
    refine ⟨88155186652381925406400087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117540248869842567208533449 88155186652381925406400087)
    ·
      refine ⟨132232779978572888109600131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88155186652381925406400087 132232779978572888109600131)
      ·
        refine ⟨198349169967859332164400197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132232779978572888109600131 198349169967859332164400197)
        ·
          refine ⟨37190469368973624780825037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198349169967859332164400197 37190469368973624780825037)
          ·
            refine ⟨13946426013365109292809389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37190469368973624780825037 13946426013365109292809389)
            ·
              refine ⟨5229909755011915984803521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13946426013365109292809389 5229909755011915984803521)
              ·
                refine ⟨3922432316258936988602641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229909755011915984803521 3922432316258936988602641)
                ·
                  refine ⟨2941824237194202741451981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3922432316258936988602641 2941824237194202741451981)
                  ·
                    refine ⟨1103184088947826028044493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941824237194202741451981 1103184088947826028044493)
                    ·
                      rfl

theorem cell22_3222665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_3222665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222665 prefixEnd_3222665 := by exact prefixLift 3222665
  have htrace : WordTrace (prefixWord ++ tailWord_3222665) baseStart_3222665 baseEnd_3222665 := by
    simpa [prefixWord, tailWord_3222665, baseEnd_3222665] using wordTrace_append hprefix tailTrace_3222665
  have hstable : (prefixWord ++ tailWord_3222665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222665).length < 2 ^ (prefixWord ++ tailWord_3222665).sum := by decide
  have hdescent : baseEnd_3222665 < baseStart_3222665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222691 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_3222691 : Nat := 118140960795 + 3222691 * 2 ^ 59
def prefixEnd_3222691 : Nat := 4983230072969 + 3 ^ 40 * 3222691 * 2
def baseEnd_3222691 : Nat := 1103192989279170626894413

theorem tailTrace_3222691 : CollatzResearch.WordTrace tailWord_3222691 prefixEnd_3222691 1103192989279170626894413 := by
  unfold tailWord_3222691
  simp only [CollatzResearch.WordTrace]
  refine ⟨117541197167748373648979927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78360798111832249099319951 117541197167748373648979927)
  ·
    refine ⟨176311795751622560473469891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117541197167748373648979927 176311795751622560473469891)
    ·
      refine ⟨264467693627433840710204837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176311795751622560473469891 264467693627433840710204837)
      ·
        refine ⟨49587692555143845133163407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264467693627433840710204837 49587692555143845133163407)
        ·
          refine ⟨74381538832715767699745111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49587692555143845133163407 74381538832715767699745111)
          ·
            refine ⟨111572308249073651549617667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74381538832715767699745111 111572308249073651549617667)
            ·
              refine ⟨167358462373610477324426501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111572308249073651549617667 167358462373610477324426501)
              ·
                refine ⟨31379711695051964498329969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167358462373610477324426501 31379711695051964498329969)
                ·
                  refine ⟨23534783771288973373747477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31379711695051964498329969 23534783771288973373747477)
                  ·
                    refine ⟨1103192989279170626894413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23534783771288973373747477 1103192989279170626894413)
                    ·
                      rfl

theorem cell22_3222691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_3222691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222691 prefixEnd_3222691 := by exact prefixLift 3222691
  have htrace : WordTrace (prefixWord ++ tailWord_3222691) baseStart_3222691 baseEnd_3222691 := by
    simpa [prefixWord, tailWord_3222691, baseEnd_3222691] using wordTrace_append hprefix tailTrace_3222691
  have hstable : (prefixWord ++ tailWord_3222691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222691).length < 2 ^ (prefixWord ++ tailWord_3222691).sum := by decide
  have hdescent : baseEnd_3222691 < baseStart_3222691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222695 : List Nat := [1, 1, 6, 2, 1, 1, 4, 6]
def baseStart_3222695 : Nat := 118140960795 + 3222695 * 2 ^ 59
def prefixEnd_3222695 : Nat := 4983230072969 + 3 ^ 40 * 3222695 * 2
def baseEnd_3222695 : Nat := 122577150951212883310489

theorem tailTrace_3222695 : CollatzResearch.WordTrace tailWord_3222695 prefixEnd_3222695 122577150951212883310489 := by
  unfold tailWord_3222695
  simp only [CollatzResearch.WordTrace]
  refine ⟨117541343059733882332125539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78360895373155921554750359 117541343059733882332125539)
  ·
    refine ⟨176312014589600823498188309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117541343059733882332125539 176312014589600823498188309)
    ·
      refine ⟨8264625683887538601477577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176312014589600823498188309 8264625683887538601477577)
      ·
        refine ⟨6198469262915653951108183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264625683887538601477577 6198469262915653951108183)
        ·
          refine ⟨9297703894373480926662275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198469262915653951108183 9297703894373480926662275)
          ·
            refine ⟨13946555841560221389993413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297703894373480926662275 13946555841560221389993413)
            ·
              refine ⟨2614979220292541510623765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13946555841560221389993413 2614979220292541510623765)
              ·
                refine ⟨122577150951212883310489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2614979220292541510623765 122577150951212883310489)
                ·
                  rfl

theorem cell22_3222695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 6].length) (baseStart_3222695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222695 prefixEnd_3222695 := by exact prefixLift 3222695
  have htrace : WordTrace (prefixWord ++ tailWord_3222695) baseStart_3222695 baseEnd_3222695 := by
    simpa [prefixWord, tailWord_3222695, baseEnd_3222695] using wordTrace_append hprefix tailTrace_3222695
  have hstable : (prefixWord ++ tailWord_3222695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222695).length < 2 ^ (prefixWord ++ tailWord_3222695).sum := by decide
  have hdescent : baseEnd_3222695 < baseStart_3222695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222733 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3222733 : Nat := 118140960795 + 3222733 * 2 ^ 59
def prefixEnd_3222733 : Nat := 4983230072969 + 3 ^ 40 * 3222733 * 2
def baseEnd_3222733 : Nat := 1103207366737496517344285

theorem tailTrace_3222733 : CollatzResearch.WordTrace tailWord_3222733 prefixEnd_3222733 1103207366737496517344285 := by
  unfold tailWord_3222733
  simp only [CollatzResearch.WordTrace]
  refine ⟨117542729033596214822008853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78361819355730809881339235 117542729033596214822008853)
  ·
    refine ⟨5509815423449822569781665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117542729033596214822008853 5509815423449822569781665)
    ·
      refine ⟨4132361567587366927336249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509815423449822569781665 4132361567587366927336249)
      ·
        refine ⟨3099271175690525195502187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132361567587366927336249 3099271175690525195502187)
        ·
          refine ⟨4648906763535787793253281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099271175690525195502187 4648906763535787793253281)
          ·
            refine ⟨3486680072651840844939961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648906763535787793253281 3486680072651840844939961)
            ·
              refine ⟨2615010054488880633704971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486680072651840844939961 2615010054488880633704971)
              ·
                refine ⟨3922515081733320950557457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615010054488880633704971 3922515081733320950557457)
                ·
                  refine ⟨2941886311299990712918093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3922515081733320950557457 2941886311299990712918093)
                  ·
                    refine ⟨1103207366737496517344285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941886311299990712918093 1103207366737496517344285)
                    ·
                      rfl

theorem cell22_3222733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3222733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222733 prefixEnd_3222733 := by exact prefixLift 3222733
  have htrace : WordTrace (prefixWord ++ tailWord_3222733) baseStart_3222733 baseEnd_3222733 := by
    simpa [prefixWord, tailWord_3222733, baseEnd_3222733] using wordTrace_append hprefix tailTrace_3222733
  have hstable : (prefixWord ++ tailWord_3222733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222733).length < 2 ^ (prefixWord ++ tailWord_3222733).sum := by decide
  have hdescent : baseEnd_3222733 < baseStart_3222733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222738 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3222738 : Nat := 118140960795 + 3222738 * 2 ^ 59
def prefixEnd_3222738 : Nat := 4983230072969 + 3 ^ 40 * 3222738 * 2
def baseEnd_3222738 : Nat := 1103209078339678170969269

theorem tailTrace_3222738 : CollatzResearch.WordTrace tailWord_3222738 prefixEnd_3222738 1103209078339678170969269 := by
  unfold tailWord_3222738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29385727849644525168985217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78361940932385400450627245 29385727849644525168985217)
  ·
    refine ⟨22039295887233393876738913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29385727849644525168985217 22039295887233393876738913)
    ·
      refine ⟨16529471915425045407554185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22039295887233393876738913 16529471915425045407554185)
      ·
        refine ⟨12397103936568784055665639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16529471915425045407554185 12397103936568784055665639)
        ·
          refine ⟨18595655904853176083498459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12397103936568784055665639 18595655904853176083498459)
          ·
            refine ⟨27893483857279764125247689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595655904853176083498459 27893483857279764125247689)
            ·
              refine ⟨20920112892959823093935767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27893483857279764125247689 20920112892959823093935767)
              ·
                refine ⟨31380169339439734640903651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20920112892959823093935767 31380169339439734640903651)
                ·
                  refine ⟨47070254009159601961355477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31380169339439734640903651 47070254009159601961355477)
                  ·
                    refine ⟨1103209078339678170969269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47070254009159601961355477 1103209078339678170969269)
                    ·
                      rfl

theorem cell22_3222738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3222738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222738 prefixEnd_3222738 := by exact prefixLift 3222738
  have htrace : WordTrace (prefixWord ++ tailWord_3222738) baseStart_3222738 baseEnd_3222738 := by
    simpa [prefixWord, tailWord_3222738, baseEnd_3222738] using wordTrace_append hprefix tailTrace_3222738
  have hstable : (prefixWord ++ tailWord_3222738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222738).length < 2 ^ (prefixWord ++ tailWord_3222738).sum := by decide
  have hdescent : baseEnd_3222738 < baseStart_3222738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222815 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_3222815 : Nat := 118140960795 + 3222815 * 2 ^ 59
def prefixEnd_3222815 : Nat := 4983230072969 + 3 ^ 40 * 3222815 * 2
def baseEnd_3222815 : Nat := 1103235437013275636794033

theorem tailTrace_3222815 : CollatzResearch.WordTrace tailWord_3222815 prefixEnd_3222815 1103235437013275636794033 := by
  unfold tailWord_3222815
  simp only [CollatzResearch.WordTrace]
  refine ⟨117545719819299142826493899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78363813212866095217662599 117545719819299142826493899)
  ·
    refine ⟨176318579728948714239740849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117545719819299142826493899 176318579728948714239740849)
    ·
      refine ⟨132238934796711535679805637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176318579728948714239740849 132238934796711535679805637)
      ·
        refine ⟨24794800274383412939963557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132238934796711535679805637 24794800274383412939963557)
        ·
          refine ⟨4649025051446889926243167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24794800274383412939963557 4649025051446889926243167)
          ·
            refine ⟨6973537577170334889364751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649025051446889926243167 6973537577170334889364751)
            ·
              refine ⟨10460306365755502334047127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973537577170334889364751 10460306365755502334047127)
              ·
                refine ⟨15690459548633253501070691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460306365755502334047127 15690459548633253501070691)
                ·
                  refine ⟨23535689322949880251606037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15690459548633253501070691 23535689322949880251606037)
                  ·
                    refine ⟨1103235437013275636794033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23535689322949880251606037 1103235437013275636794033)
                    ·
                      rfl

theorem cell22_3222815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_3222815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222815 prefixEnd_3222815 := by exact prefixLift 3222815
  have htrace : WordTrace (prefixWord ++ tailWord_3222815) baseStart_3222815 baseEnd_3222815 := by
    simpa [prefixWord, tailWord_3222815, baseEnd_3222815] using wordTrace_append hprefix tailTrace_3222815
  have hstable : (prefixWord ++ tailWord_3222815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222815).length < 2 ^ (prefixWord ++ tailWord_3222815).sum := by decide
  have hdescent : baseEnd_3222815 < baseStart_3222815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222834 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_3222834 : Nat := 118140960795 + 3222834 * 2 ^ 59
def prefixEnd_3222834 : Nat := 4983230072969 + 3 ^ 40 * 3222834 * 2
def baseEnd_3222834 : Nat := 1103241941101565920568975

theorem tailTrace_3222834 : CollatzResearch.WordTrace tailWord_3222834 prefixEnd_3222834 1103241941101565920568975 := by
  unfold tailWord_3222834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386603201557577267858889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78364275204153539380957037 29386603201557577267858889)
  ·
    refine ⟨22039952401168182950894167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29386603201557577267858889 22039952401168182950894167)
    ·
      refine ⟨33059928601752274426341251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22039952401168182950894167 33059928601752274426341251)
      ·
        refine ⟨49589892902628411639511877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33059928601752274426341251 49589892902628411639511877)
        ·
          refine ⟨9298104919242827182408477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49589892902628411639511877 9298104919242827182408477)
          ·
            refine ⟨3486789344716060193403179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9298104919242827182408477 3486789344716060193403179)
            ·
              refine ⟨5230184017074090290104769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486789344716060193403179 5230184017074090290104769)
              ·
                refine ⟨3922638012805567717578577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5230184017074090290104769 3922638012805567717578577)
                ·
                  refine ⟨2941978509604175788183933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3922638012805567717578577 2941978509604175788183933)
                  ·
                    refine ⟨1103241941101565920568975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941978509604175788183933 1103241941101565920568975)
                    ·
                      rfl

theorem cell22_3222834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_3222834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222834 prefixEnd_3222834 := by exact prefixLift 3222834
  have htrace : WordTrace (prefixWord ++ tailWord_3222834) baseStart_3222834 baseEnd_3222834 := by
    simpa [prefixWord, tailWord_3222834, baseEnd_3222834] using wordTrace_append hprefix tailTrace_3222834
  have hstable : (prefixWord ++ tailWord_3222834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222834).length < 2 ^ (prefixWord ++ tailWord_3222834).sum := by decide
  have hdescent : baseEnd_3222834 < baseStart_3222834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222870 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3222870 : Nat := 118140960795 + 3222870 * 2 ^ 59
def prefixEnd_3222870 : Nat := 4983230072969 + 3 ^ 40 * 3222870 * 2
def baseEnd_3222870 : Nat := 367751421545757942222955

theorem tailTrace_3222870 : CollatzResearch.WordTrace tailWord_3222870 prefixEnd_3222870 367751421545757942222955 := by
  unfold tailWord_3222870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346732864631242951234129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78365150556066591479830709 7346732864631242951234129)
  ·
    refine ⟨5510049648473432213425597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7346732864631242951234129 5510049648473432213425597)
    ·
      refine ⟨2066268618177537080034599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5510049648473432213425597 2066268618177537080034599)
      ·
        refine ⟨3099402927266305620051899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066268618177537080034599 3099402927266305620051899)
        ·
          refine ⟨4649104390899458430077849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099402927266305620051899 4649104390899458430077849)
          ·
            refine ⟨3486828293174593822558387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4649104390899458430077849 3486828293174593822558387)
            ·
              refine ⟨5230242439761890733837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486828293174593822558387 5230242439761890733837581)
              ·
                refine ⟨1961340914910709025189093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5230242439761890733837581 1961340914910709025189093)
                ·
                  refine ⟨367751421545757942222955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961340914910709025189093 367751421545757942222955)
                  ·
                    rfl

theorem cell22_3222870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3222870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222870 prefixEnd_3222870 := by exact prefixLift 3222870
  have htrace : WordTrace (prefixWord ++ tailWord_3222870) baseStart_3222870 baseEnd_3222870 := by
    simpa [prefixWord, tailWord_3222870, baseEnd_3222870] using wordTrace_append hprefix tailTrace_3222870
  have hstable : (prefixWord ++ tailWord_3222870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222870).length < 2 ^ (prefixWord ++ tailWord_3222870).sum := by decide
  have hdescent : baseEnd_3222870 < baseStart_3222870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222873 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3222873 : Nat := 118140960795 + 3222873 * 2 ^ 59
def prefixEnd_3222873 : Nat := 4983230072969 + 3 ^ 40 * 3222873 * 2
def baseEnd_3222873 : Nat := 1103255291598582818843855

theorem tailTrace_3222873 : CollatzResearch.WordTrace tailWord_3222873 prefixEnd_3222873 1103255291598582818843855 := by
  unfold tailWord_3222873
  simp only [CollatzResearch.WordTrace]
  refine ⟨117547835253089018732105273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78365223502059345821403515 117547835253089018732105273)
  ·
    refine ⟨88160876439816764049078955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117547835253089018732105273 88160876439816764049078955)
    ·
      refine ⟨132241314659725146073618433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88160876439816764049078955 132241314659725146073618433)
      ·
        refine ⟨99180985994793859555213825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132241314659725146073618433 99180985994793859555213825)
        ·
          refine ⟨74385739496095394666410369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99180985994793859555213825 74385739496095394666410369)
          ·
            refine ⟨55789304622071545999807777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74385739496095394666410369 55789304622071545999807777)
            ·
              refine ⟨41841978466553659499855833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55789304622071545999807777 41841978466553659499855833)
              ·
                refine ⟨31381483849915244624891875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41841978466553659499855833 31381483849915244624891875)
                ·
                  refine ⟨47072225774872866937337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31381483849915244624891875 47072225774872866937337813)
                  ·
                    refine ⟨1103255291598582818843855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47072225774872866937337813 1103255291598582818843855)
                    ·
                      rfl

theorem cell22_3222873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3222873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222873 prefixEnd_3222873 := by exact prefixLift 3222873
  have htrace : WordTrace (prefixWord ++ tailWord_3222873) baseStart_3222873 baseEnd_3222873 := by
    simpa [prefixWord, tailWord_3222873, baseEnd_3222873] using wordTrace_append hprefix tailTrace_3222873
  have hstable : (prefixWord ++ tailWord_3222873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222873).length < 2 ^ (prefixWord ++ tailWord_3222873).sum := by decide
  have hdescent : baseEnd_3222873 < baseStart_3222873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222997 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3222997 : Nat := 118140960795 + 3222997 * 2 ^ 59
def prefixEnd_3222997 : Nat := 4983230072969 + 3 ^ 40 * 3222997 * 2
def baseEnd_3222997 : Nat := 1103297739332687828743475

theorem tailTrace_3222997 : CollatzResearch.WordTrace tailWord_3222997 prefixEnd_3222997 1103297739332687828743475 := by
  unfold tailWord_3222997
  simp only [CollatzResearch.WordTrace]
  refine ⟨117552357904639787909619245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78368238603093191939746163 117552357904639787909619245)
  ·
    refine ⟨44082134214239920466107217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117552357904639787909619245 44082134214239920466107217)
    ·
      refine ⟨33061600660679940349580413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44082134214239920466107217 33061600660679940349580413)
      ·
        refine ⟨12398100247754977631092655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33061600660679940349580413 12398100247754977631092655)
        ·
          refine ⟨18597150371632466446638983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398100247754977631092655 18597150371632466446638983)
          ·
            refine ⟨27895725557448699669958475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18597150371632466446638983 27895725557448699669958475)
            ·
              refine ⟨41843588336173049504937713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27895725557448699669958475 41843588336173049504937713)
              ·
                refine ⟨31382691252129787128703285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41843588336173049504937713 31382691252129787128703285)
                ·
                  refine ⟨2942127304887167543315933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31382691252129787128703285 2942127304887167543315933)
                  ·
                    refine ⟨1103297739332687828743475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942127304887167543315933 1103297739332687828743475)
                    ·
                      rfl

theorem cell22_3222997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3222997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3222997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3222997 prefixEnd_3222997 := by exact prefixLift 3222997
  have htrace : WordTrace (prefixWord ++ tailWord_3222997) baseStart_3222997 baseEnd_3222997 := by
    simpa [prefixWord, tailWord_3222997, baseEnd_3222997] using wordTrace_append hprefix tailTrace_3222997
  have hstable : (prefixWord ++ tailWord_3222997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222997).length < 2 ^ (prefixWord ++ tailWord_3222997).sum := by decide
  have hdescent : baseEnd_3222997 < baseStart_3222997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223057 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3223057 : Nat := 118140960795 + 3223057 * 2 ^ 59
def prefixEnd_3223057 : Nat := 4983230072969 + 3 ^ 40 * 3223057 * 2
def baseEnd_3223057 : Nat := 1103318278558867672243291

theorem tailTrace_3223057 : CollatzResearch.WordTrace tailWord_3223057 prefixEnd_3223057 1103318278558867672243291 := by
  unfold tailWord_3223057
  simp only [CollatzResearch.WordTrace]
  refine ⟨117554546284422418156803425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78369697522948278771202283 117554546284422418156803425)
  ·
    refine ⟨88165909713316813617602569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117554546284422418156803425 88165909713316813617602569)
    ·
      refine ⟨66124432284987610213201927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88165909713316813617602569 66124432284987610213201927)
      ·
        refine ⟨99186648427481415319802891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66124432284987610213201927 99186648427481415319802891)
        ·
          refine ⟨148779972641222122979704337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99186648427481415319802891 148779972641222122979704337)
          ·
            refine ⟨111584979480916592234778253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148779972641222122979704337 111584979480916592234778253)
            ·
              refine ⟨41844367305343722088041845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111584979480916592234778253 41844367305343722088041845)
              ·
                refine ⟨3922909434875973945753923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41844367305343722088041845 3922909434875973945753923)
                ·
                  refine ⟨5884364152313960918630885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922909434875973945753923 5884364152313960918630885)
                  ·
                    refine ⟨1103318278558867672243291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884364152313960918630885 1103318278558867672243291)
                    ·
                      rfl

theorem cell22_3223057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3223057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223057 prefixEnd_3223057 := by exact prefixLift 3223057
  have htrace : WordTrace (prefixWord ++ tailWord_3223057) baseStart_3223057 baseEnd_3223057 := by
    simpa [prefixWord, tailWord_3223057, baseEnd_3223057] using wordTrace_append hprefix tailTrace_3223057
  have hstable : (prefixWord ++ tailWord_3223057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223057).length < 2 ^ (prefixWord ++ tailWord_3223057).sum := by decide
  have hdescent : baseEnd_3223057 < baseStart_3223057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223117 : List Nat := [1, 6, 1, 1, 13]
def baseStart_3223117 : Nat := 118140960795 + 3223117 * 2 ^ 59
def prefixEnd_3223117 : Nat := 4983230072969 + 3 ^ 40 * 3223117 * 2
def baseEnd_3223117 : Nat := 4540488962078384838449

theorem tailTrace_3223117 : CollatzResearch.WordTrace tailWord_3223117 prefixEnd_3223117 4540488962078384838449 := by
  unfold tailWord_3223117
  simp only [CollatzResearch.WordTrace]
  refine ⟨117556734664205048403987605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78371156442803365602658403 117556734664205048403987605)
  ·
    refine ⟨5510471937384611643936919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117556734664205048403987605 5510471937384611643936919)
    ·
      refine ⟨8265707906076917465905379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510471937384611643936919 8265707906076917465905379)
      ·
        refine ⟨12398561859115376198858069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265707906076917465905379 12398561859115376198858069)
        ·
          refine ⟨4540488962078384838449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12398561859115376198858069 4540488962078384838449)
          ·
            rfl

theorem cell22_3223117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 13].length) (baseStart_3223117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223117 prefixEnd_3223117 := by exact prefixLift 3223117
  have htrace : WordTrace (prefixWord ++ tailWord_3223117) baseStart_3223117 baseEnd_3223117 := by
    simpa [prefixWord, tailWord_3223117, baseEnd_3223117] using wordTrace_append hprefix tailTrace_3223117
  have hstable : (prefixWord ++ tailWord_3223117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223117).length < 2 ^ (prefixWord ++ tailWord_3223117).sum := by decide
  have hdescent : baseEnd_3223117 < baseStart_3223117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223177 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3223177 : Nat := 118140960795 + 3223177 * 2 ^ 59
def prefixEnd_3223177 : Nat := 4983230072969 + 3 ^ 40 * 3223177 * 2
def baseEnd_3223177 : Nat := 1103359357011227359242923

theorem tailTrace_3223177 : CollatzResearch.WordTrace tailWord_3223177 prefixEnd_3223177 1103359357011227359242923 := by
  unfold tailWord_3223177
  simp only [CollatzResearch.WordTrace]
  refine ⟨117558923043987678651171785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78372615362658452434114523 117558923043987678651171785)
  ·
    refine ⟨88169192282990758988378839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117558923043987678651171785 88169192282990758988378839)
    ·
      refine ⟨132253788424486138482568259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88169192282990758988378839 132253788424486138482568259)
      ·
        refine ⟨198380682636729207723852389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132253788424486138482568259 198380682636729207723852389)
        ·
          refine ⟨37196377994386726448222323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198380682636729207723852389 37196377994386726448222323)
          ·
            refine ⟨55794566991580089672333485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37196377994386726448222323 55794566991580089672333485)
            ·
              refine ⟨20922962621842533627125057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55794566991580089672333485 20922962621842533627125057)
              ·
                refine ⟨15692221966381900220343793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20922962621842533627125057 15692221966381900220343793)
                ·
                  refine ⟨11769166474786425165257845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15692221966381900220343793 11769166474786425165257845)
                  ·
                    refine ⟨1103359357011227359242923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11769166474786425165257845 1103359357011227359242923)
                    ·
                      rfl

theorem cell22_3223177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3223177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223177 prefixEnd_3223177 := by exact prefixLift 3223177
  have htrace : WordTrace (prefixWord ++ tailWord_3223177) baseStart_3223177 baseEnd_3223177 := by
    simpa [prefixWord, tailWord_3223177, baseEnd_3223177] using wordTrace_append hprefix tailTrace_3223177
  have hstable : (prefixWord ++ tailWord_3223177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223177).length < 2 ^ (prefixWord ++ tailWord_3223177).sum := by decide
  have hdescent : baseEnd_3223177 < baseStart_3223177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223234 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3223234 : Nat := 118140960795 + 3223234 * 2 ^ 59
def prefixEnd_3223234 : Nat := 4983230072969 + 3 ^ 40 * 3223234 * 2
def baseEnd_3223234 : Nat := 1103378869276098210567749

theorem tailTrace_3223234 : CollatzResearch.WordTrace tailWord_3223234 prefixEnd_3223234 1103378869276098210567749 := by
  unfold tailWord_3223234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390250501195294346499189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78374001336520784923997837 29390250501195294346499189)
  ·
    refine ⟨2755335984487058844984299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29390250501195294346499189 2755335984487058844984299)
    ·
      refine ⟨4133003976730588267476449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755335984487058844984299 4133003976730588267476449)
      ·
        refine ⟨3099752982547941200607337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4133003976730588267476449 3099752982547941200607337)
        ·
          refine ⟨2324814736910955900455503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099752982547941200607337 2324814736910955900455503)
          ·
            refine ⟨3487222105366433850683255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324814736910955900455503 3487222105366433850683255)
            ·
              refine ⟨5230833158049650776024883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487222105366433850683255 5230833158049650776024883)
              ·
                refine ⟨7846249737074476164037325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230833158049650776024883 7846249737074476164037325)
                ·
                  refine ⟨2942343651402928561513997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7846249737074476164037325 2942343651402928561513997)
                  ·
                    refine ⟨1103378869276098210567749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942343651402928561513997 1103378869276098210567749)
                    ·
                      rfl

theorem cell22_3223234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3223234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223234 prefixEnd_3223234 := by exact prefixLift 3223234
  have htrace : WordTrace (prefixWord ++ tailWord_3223234) baseStart_3223234 baseEnd_3223234 := by
    simpa [prefixWord, tailWord_3223234, baseEnd_3223234] using wordTrace_append hprefix tailTrace_3223234
  have hstable : (prefixWord ++ tailWord_3223234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223234).length < 2 ^ (prefixWord ++ tailWord_3223234).sum := by decide
  have hdescent : baseEnd_3223234 < baseStart_3223234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223239 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3223239 : Nat := 118140960795 + 3223239 * 2 ^ 59
def prefixEnd_3223239 : Nat := 4983230072969 + 3 ^ 40 * 3223239 * 2
def baseEnd_3223239 : Nat := 1103380580878279864192733

theorem tailTrace_3223239 : CollatzResearch.WordTrace tailWord_3223239 prefixEnd_3223239 1103380580878279864192733 := by
  unfold tailWord_3223239
  simp only [CollatzResearch.WordTrace]
  refine ⟨117561184369763063239928771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78374122913175375493285847 117561184369763063239928771)
  ·
    refine ⟨176341776554644594859893157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117561184369763063239928771 176341776554644594859893157)
    ·
      refine ⟨33064083103995861536229967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176341776554644594859893157 33064083103995861536229967)
      ·
        refine ⟨49596124655993792304344951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33064083103995861536229967 49596124655993792304344951)
        ·
          refine ⟨74394186983990688456517427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49596124655993792304344951 74394186983990688456517427)
          ·
            refine ⟨111591280475986032684776141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74394186983990688456517427 111591280475986032684776141)
            ·
              refine ⟨41846730178494762256791053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111591280475986032684776141 41846730178494762256791053)
              ·
                refine ⟨15692523816935535846296645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41846730178494762256791053 15692523816935535846296645)
                ·
                  refine ⟨2942348215675412971180621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15692523816935535846296645 2942348215675412971180621)
                  ·
                    refine ⟨1103380580878279864192733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942348215675412971180621 1103380580878279864192733)
                    ·
                      rfl

theorem cell22_3223239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3223239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223239 prefixEnd_3223239 := by exact prefixLift 3223239
  have htrace : WordTrace (prefixWord ++ tailWord_3223239) baseStart_3223239 baseEnd_3223239 := by
    simpa [prefixWord, tailWord_3223239, baseEnd_3223239] using wordTrace_append hprefix tailTrace_3223239
  have hstable : (prefixWord ++ tailWord_3223239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223239).length < 2 ^ (prefixWord ++ tailWord_3223239).sum := by decide
  have hdescent : baseEnd_3223239 < baseStart_3223239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223256 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_3223256 : Nat := 118140960795 + 3223256 * 2 ^ 59
def prefixEnd_3223256 : Nat := 4983230072969 + 3 ^ 40 * 3223256 * 2
def baseEnd_3223256 : Nat := 1103386400325697486517681

theorem tailTrace_3223256 : CollatzResearch.WordTrace tailWord_3223256 prefixEnd_3223256 1103386400325697486517681 := by
  unfold tailWord_3223256
  simp only [CollatzResearch.WordTrace]
  refine ⟨58780902205350737571648811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78374536273800983428865081 58780902205350737571648811)
  ·
    refine ⟨88171353308026106357473217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58780902205350737571648811 88171353308026106357473217)
    ·
      refine ⟨66128514981019579768104913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88171353308026106357473217 66128514981019579768104913)
      ·
        refine ⟨49596386235764684826078685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66128514981019579768104913 49596386235764684826078685)
        ·
          refine ⟨18598644838411756809779507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49596386235764684826078685 18598644838411756809779507)
          ·
            refine ⟨27897967257617635214669261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598644838411756809779507 27897967257617635214669261)
            ·
              refine ⟨10461737721606613205500973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27897967257617635214669261 10461737721606613205500973)
              ·
                refine ⟨3923151645602479952062865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10461737721606613205500973 3923151645602479952062865)
                ·
                  refine ⟨2942363734201859964047149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3923151645602479952062865 2942363734201859964047149)
                  ·
                    refine ⟨1103386400325697486517681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942363734201859964047149 1103386400325697486517681)
                    ·
                      rfl

theorem cell22_3223256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_3223256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223256 prefixEnd_3223256 := by exact prefixLift 3223256
  have htrace : WordTrace (prefixWord ++ tailWord_3223256) baseStart_3223256 baseEnd_3223256 := by
    simpa [prefixWord, tailWord_3223256, baseEnd_3223256] using wordTrace_append hprefix tailTrace_3223256
  have hstable : (prefixWord ++ tailWord_3223256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223256).length < 2 ^ (prefixWord ++ tailWord_3223256).sum := by decide
  have hdescent : baseEnd_3223256 < baseStart_3223256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223260 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3223260 : Nat := 118140960795 + 3223260 * 2 ^ 59
def prefixEnd_3223260 : Nat := 4983230072969 + 3 ^ 40 * 3223260 * 2
def baseEnd_3223260 : Nat := 1103387769607442809417669

theorem tailTrace_3223260 : CollatzResearch.WordTrace tailWord_3223260 prefixEnd_3223260 1103387769607442809417669 := by
  unfold tailWord_3223260
  simp only [CollatzResearch.WordTrace]
  refine ⟨58780975151343491913221617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78374633535124655884295489 58780975151343491913221617)
  ·
    refine ⟨44085731363507618934916213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58780975151343491913221617 44085731363507618934916213)
    ·
      refine ⟨4133037315328839275148395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44085731363507618934916213 4133037315328839275148395)
      ·
        refine ⟨6199555972993258912722593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133037315328839275148395 6199555972993258912722593)
        ·
          refine ⟨4649666979744944184541945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199555972993258912722593 4649666979744944184541945)
          ·
            refine ⟨3487250234808708138406459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4649666979744944184541945 3487250234808708138406459)
            ·
              refine ⟨5230875352213062207609689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487250234808708138406459 5230875352213062207609689)
              ·
                refine ⟨3923156514159796655707267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5230875352213062207609689 3923156514159796655707267)
                ·
                  refine ⟨5884734771239694983560901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923156514159796655707267 5884734771239694983560901)
                  ·
                    refine ⟨1103387769607442809417669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884734771239694983560901 1103387769607442809417669)
                    ·
                      rfl

theorem cell22_3223260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3223260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223260 prefixEnd_3223260 := by exact prefixLift 3223260
  have htrace : WordTrace (prefixWord ++ tailWord_3223260) baseStart_3223260 baseEnd_3223260 := by
    simpa [prefixWord, tailWord_3223260, baseEnd_3223260] using wordTrace_append hprefix tailTrace_3223260
  have hstable : (prefixWord ++ tailWord_3223260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223260).length < 2 ^ (prefixWord ++ tailWord_3223260).sum := by decide
  have hdescent : baseEnd_3223260 < baseStart_3223260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223303 : List Nat := [1, 1, 4, 4, 3, 1, 1, 7]
def baseStart_3223303 : Nat := 118140960795 + 3223303 * 2 ^ 59
def prefixEnd_3223303 : Nat := 4983230072969 + 3 ^ 40 * 3223303 * 2
def baseEnd_3223303 : Nat := 122600276598467225621393

theorem tailTrace_3223303 : CollatzResearch.WordTrace tailWord_3223303 prefixEnd_3223303 122600276598467225621393 := by
  unfold tailWord_3223303
  simp only [CollatzResearch.WordTrace]
  refine ⟨117563518641531202170258563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78375679094354134780172375 117563518641531202170258563)
  ·
    refine ⟨176345277962296803255387845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117563518641531202170258563 176345277962296803255387845)
    ·
      refine ⟨33064739617930650610385221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176345277962296803255387845 33064739617930650610385221)
      ·
        refine ⟨6199638678361996989447229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33064739617930650610385221 6199638678361996989447229)
        ·
          refine ⟨2324864504385748871042711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6199638678361996989447229 2324864504385748871042711)
          ·
            refine ⟨3487296756578623306564067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324864504385748871042711 3487296756578623306564067)
            ·
              refine ⟨5230945134867934959846101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487296756578623306564067 5230945134867934959846101)
              ·
                refine ⟨122600276598467225621393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5230945134867934959846101 122600276598467225621393)
                ·
                  rfl

theorem cell22_3223303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 7].length) (baseStart_3223303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223303 prefixEnd_3223303 := by exact prefixLift 3223303
  have htrace : WordTrace (prefixWord ++ tailWord_3223303) baseStart_3223303 baseEnd_3223303 := by
    simpa [prefixWord, tailWord_3223303, baseEnd_3223303] using wordTrace_append hprefix tailTrace_3223303
  have hstable : (prefixWord ++ tailWord_3223303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223303).length < 2 ^ (prefixWord ++ tailWord_3223303).sum := by decide
  have hdescent : baseEnd_3223303 < baseStart_3223303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223348 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3223348 : Nat := 118140960795 + 3223348 * 2 ^ 59
def prefixEnd_3223348 : Nat := 4983230072969 + 3 ^ 40 * 3223348 * 2
def baseEnd_3223348 : Nat := 367805964601946637739133

theorem tailTrace_3223348 : CollatzResearch.WordTrace tailWord_3223348 prefixEnd_3223348 367805964601946637739133 := by
  unfold tailWord_3223348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58782579963184087427823349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78376773284245449903764465 58782579963184087427823349)
  ·
    refine ⟨5510866871548508196358439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58782579963184087427823349 5510866871548508196358439)
    ·
      refine ⟨8266300307322762294537659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510866871548508196358439 8266300307322762294537659)
      ·
        refine ⟨12399450460984143441806489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266300307322762294537659 12399450460984143441806489)
        ·
          refine ⟨9299587845738107581354867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12399450460984143441806489 9299587845738107581354867)
          ·
            refine ⟨13949381768607161372032301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299587845738107581354867 13949381768607161372032301)
            ·
              refine ⟨5231018163227685514512113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13949381768607161372032301 5231018163227685514512113)
              ·
                refine ⟨3923263622420764135884085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231018163227685514512113 3923263622420764135884085)
                ·
                  refine ⟨367805964601946637739133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923263622420764135884085 367805964601946637739133)
                  ·
                    rfl

theorem cell22_3223348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3223348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223348 prefixEnd_3223348 := by exact prefixLift 3223348
  have htrace : WordTrace (prefixWord ++ tailWord_3223348) baseStart_3223348 baseEnd_3223348 := by
    simpa [prefixWord, tailWord_3223348, baseEnd_3223348] using wordTrace_append hprefix tailTrace_3223348
  have hstable : (prefixWord ++ tailWord_3223348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223348).length < 2 ^ (prefixWord ++ tailWord_3223348).sum := by decide
  have hdescent : baseEnd_3223348 < baseStart_3223348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223378 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3223378 : Nat := 118140960795 + 3223378 * 2 ^ 59
def prefixEnd_3223378 : Nat := 4983230072969 + 3 ^ 40 * 3223378 * 2
def baseEnd_3223378 : Nat := 1103428163418929834967307

theorem tailTrace_3223378 : CollatzResearch.WordTrace tailWord_3223378 prefixEnd_3223378 1103428163418929834967307 := by
  unfold tailWord_3223378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29391563529064872494809697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78377502744172993319492525 29391563529064872494809697)
  ·
    refine ⟨22043672646798654371107273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29391563529064872494809697 22043672646798654371107273)
    ·
      refine ⟨16532754485098990778330455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22043672646798654371107273 16532754485098990778330455)
      ·
        refine ⟨24799131727648486167495683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16532754485098990778330455 24799131727648486167495683)
        ·
          refine ⟨37198697591472729251243525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24799131727648486167495683 37198697591472729251243525)
          ·
            refine ⟨6974755798401136734608161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37198697591472729251243525 6974755798401136734608161)
            ·
              refine ⟨5231066848800852550956121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974755798401136734608161 5231066848800852550956121)
              ·
                refine ⟨3923300136600639413217091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231066848800852550956121 3923300136600639413217091)
                ·
                  refine ⟨5884950204900959119825637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923300136600639413217091 5884950204900959119825637)
                  ·
                    refine ⟨1103428163418929834967307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884950204900959119825637 1103428163418929834967307)
                    ·
                      rfl

theorem cell22_3223378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3223378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223378 prefixEnd_3223378 := by exact prefixLift 3223378
  have htrace : WordTrace (prefixWord ++ tailWord_3223378) baseStart_3223378 baseEnd_3223378 := by
    simpa [prefixWord, tailWord_3223378, baseEnd_3223378] using wordTrace_append hprefix tailTrace_3223378
  have hstable : (prefixWord ++ tailWord_3223378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223378).length < 2 ^ (prefixWord ++ tailWord_3223378).sum := by decide
  have hdescent : baseEnd_3223378 < baseStart_3223378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223391 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 4, 3]
def baseStart_3223391 : Nat := 118140960795 + 3223391 * 2 ^ 59
def prefixEnd_3223391 : Nat := 4983230072969 + 3 ^ 40 * 3223391 * 2
def baseEnd_3223391 : Nat := 1103432613584602134392267

theorem tailTrace_3223391 : CollatzResearch.WordTrace tailWord_3223391 prefixEnd_3223391 1103432613584602134392267 := by
  unfold tailWord_3223391
  simp only [CollatzResearch.WordTrace]
  refine ⟨117566728265212393199462027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78377818843474928799641351 117566728265212393199462027)
  ·
    refine ⟨176350092397818589799193041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117566728265212393199462027 176350092397818589799193041)
    ·
      refine ⟨132262569298363942349394781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176350092397818589799193041 132262569298363942349394781)
      ·
        refine ⟨49598463486886478381023043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132262569298363942349394781 49598463486886478381023043)
        ·
          refine ⟨74397695230329717571534565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49598463486886478381023043 74397695230329717571534565)
          ·
            refine ⟨13949567855686822044662731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74397695230329717571534565 13949567855686822044662731)
            ·
              refine ⟨20924351783530233066994097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13949567855686822044662731 20924351783530233066994097)
              ·
                refine ⟨15693263837647674800245573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20924351783530233066994097 15693263837647674800245573)
                ·
                  refine ⟨2942486969558939025046045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15693263837647674800245573 2942486969558939025046045)
                  ·
                    refine ⟨1103432613584602134392267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942486969558939025046045 1103432613584602134392267)
                    ·
                      rfl

theorem cell22_3223391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_3223391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223391 prefixEnd_3223391 := by exact prefixLift 3223391
  have htrace : WordTrace (prefixWord ++ tailWord_3223391) baseStart_3223391 baseEnd_3223391 := by
    simpa [prefixWord, tailWord_3223391, baseEnd_3223391] using wordTrace_append hprefix tailTrace_3223391
  have hstable : (prefixWord ++ tailWord_3223391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223391).length < 2 ^ (prefixWord ++ tailWord_3223391).sum := by decide
  have hdescent : baseEnd_3223391 < baseStart_3223391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223404 : List Nat := [2, 2, 1, 1, 4, 2, 10]
def baseStart_3223404 : Nat := 118140960795 + 3223404 * 2 ^ 59
def prefixEnd_3223404 : Nat := 4983230072969 + 3 ^ 40 * 3223404 * 2
def baseEnd_3223404 : Nat := 40868039398158312363601

theorem tailTrace_3223404 : CollatzResearch.WordTrace tailWord_3223404 prefixEnd_3223404 40868039398158312363601 := by
  unfold tailWord_3223404
  simp only [CollatzResearch.WordTrace]
  refine ⟨58783601207082648209842633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78378134942776864279790177 58783601207082648209842633)
  ·
    refine ⟨44087700905311986157381975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58783601207082648209842633 44087700905311986157381975)
    ·
      refine ⟨66131551357967979236072963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44087700905311986157381975 66131551357967979236072963)
      ·
        refine ⟨99197327036951968854109445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66131551357967979236072963 99197327036951968854109445)
        ·
          refine ⟨18599498819428494160145521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99197327036951968854109445 18599498819428494160145521)
          ·
            refine ⟨13949624114571370620109141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18599498819428494160145521 13949624114571370620109141)
            ·
              refine ⟨40868039398158312363601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13949624114571370620109141 40868039398158312363601)
              ·
                rfl

theorem cell22_3223404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 10].length) (baseStart_3223404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223404 prefixEnd_3223404 := by exact prefixLift 3223404
  have htrace : WordTrace (prefixWord ++ tailWord_3223404) baseStart_3223404 baseEnd_3223404 := by
    simpa [prefixWord, tailWord_3223404, baseEnd_3223404] using wordTrace_append hprefix tailTrace_3223404
  have hstable : (prefixWord ++ tailWord_3223404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223404).length < 2 ^ (prefixWord ++ tailWord_3223404).sum := by decide
  have hdescent : baseEnd_3223404 < baseStart_3223404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223436 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_3223436 : Nat := 118140960795 + 3223436 * 2 ^ 59
def prefixEnd_3223436 : Nat := 4983230072969 + 3 ^ 40 * 3223436 * 2
def baseEnd_3223436 : Nat := 1103448018004237017017129

theorem tailTrace_3223436 : CollatzResearch.WordTrace tailWord_3223436 prefixEnd_3223436 1103448018004237017017129 := by
  unfold tailWord_3223436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784184775024682942425081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78378913033366243923233441 58784184775024682942425081)
  ·
    refine ⟨44088138581268512206818811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58784184775024682942425081 44088138581268512206818811)
    ·
      refine ⟨66132207871902768310228217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44088138581268512206818811 66132207871902768310228217)
      ·
        refine ⟨49599155903927076232671163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66132207871902768310228217 49599155903927076232671163)
        ·
          refine ⟨74398733855890614349006745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49599155903927076232671163 74398733855890614349006745)
          ·
            refine ⟨55799050391917960761755059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74398733855890614349006745 55799050391917960761755059)
            ·
              refine ⟨83698575587876941142632589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55799050391917960761755059 83698575587876941142632589)
              ·
                refine ⟨31386965845453852928487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83698575587876941142632589 31386965845453852928487221)
                ·
                  refine ⟨2942528048011298712045677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31386965845453852928487221 2942528048011298712045677)
                  ·
                    refine ⟨1103448018004237017017129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942528048011298712045677 1103448018004237017017129)
                    ·
                      rfl

theorem cell22_3223436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_3223436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223436 prefixEnd_3223436 := by exact prefixLift 3223436
  have htrace : WordTrace (prefixWord ++ tailWord_3223436) baseStart_3223436 baseEnd_3223436 := by
    simpa [prefixWord, tailWord_3223436, baseEnd_3223436] using wordTrace_append hprefix tailTrace_3223436
  have hstable : (prefixWord ++ tailWord_3223436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223436).length < 2 ^ (prefixWord ++ tailWord_3223436).sum := by decide
  have hdescent : baseEnd_3223436 < baseStart_3223436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223449 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 9]
def baseStart_3223449 : Nat := 118140960795 + 3223449 * 2 ^ 59
def prefixEnd_3223449 : Nat := 4983230072969 + 3 ^ 40 * 3223449 * 2
def baseEnd_3223449 : Nat := 367817489389969772147363

theorem tailTrace_3223449 : CollatzResearch.WordTrace tailWord_3223449 prefixEnd_3223449 367817489389969772147363 := by
  unfold tailWord_3223449
  simp only [CollatzResearch.WordTrace]
  refine ⟨117568843699002269105073401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78379229132668179403382267 117568843699002269105073401)
  ·
    refine ⟨88176632774251701828805051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117568843699002269105073401 88176632774251701828805051)
    ·
      refine ⟨132264949161377552743207577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88176632774251701828805051 132264949161377552743207577)
      ·
        refine ⟨99198711871033164557405683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132264949161377552743207577 99198711871033164557405683)
        ·
          refine ⟨148798067806549746836108525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99198711871033164557405683 148798067806549746836108525)
          ·
            refine ⟨55799275427456155063540697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148798067806549746836108525 55799275427456155063540697)
            ·
              refine ⟨41849456570592116297655523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55799275427456155063540697 41849456570592116297655523)
              ·
                refine ⟨62774184855888174446483285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41849456570592116297655523 62774184855888174446483285)
                ·
                  refine ⟨367817489389969772147363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62774184855888174446483285 367817489389969772147363)
                  ·
                    rfl

theorem cell22_3223449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_3223449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223449 prefixEnd_3223449 := by exact prefixLift 3223449
  have htrace : WordTrace (prefixWord ++ tailWord_3223449) baseStart_3223449 baseEnd_3223449 := by
    simpa [prefixWord, tailWord_3223449, baseEnd_3223449] using wordTrace_append hprefix tailTrace_3223449
  have hstable : (prefixWord ++ tailWord_3223449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223449).length < 2 ^ (prefixWord ++ tailWord_3223449).sum := by decide
  have hdescent : baseEnd_3223449 < baseStart_3223449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223481 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_3223481 : Nat := 118140960795 + 3223481 * 2 ^ 59
def prefixEnd_3223481 : Nat := 4983230072969 + 3 ^ 40 * 3223481 * 2
def baseEnd_3223481 : Nat := 1103463422423871899641991

theorem tailTrace_3223481 : CollatzResearch.WordTrace tailWord_3223481 prefixEnd_3223481 1103463422423871899641991 := by
  unfold tailWord_3223481
  simp only [CollatzResearch.WordTrace]
  refine ⟨117570010834886338570238297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78380007223257559046825531 117570010834886338570238297)
  ·
    refine ⟨88177508126164753927678723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117570010834886338570238297 88177508126164753927678723)
    ·
      refine ⟨132266262189247130891518085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88177508126164753927678723 132266262189247130891518085)
      ·
        refine ⟨24799924160483837042159641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132266262189247130891518085 24799924160483837042159641)
        ·
          refine ⟨18599943120362877781619731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24799924160483837042159641 18599943120362877781619731)
          ·
            refine ⟨27899914680544316672429597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599943120362877781619731 27899914680544316672429597)
            ·
              refine ⟨10462468005204118752161099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27899914680544316672429597 10462468005204118752161099)
              ·
                refine ⟨15693702007806178128241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462468005204118752161099 15693702007806178128241649)
                ·
                  refine ⟨11770276505854633596181237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15693702007806178128241649 11770276505854633596181237)
                  ·
                    refine ⟨1103463422423871899641991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11770276505854633596181237 1103463422423871899641991)
                    ·
                      rfl

theorem cell22_3223481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_3223481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223481 prefixEnd_3223481 := by exact prefixLift 3223481
  have htrace : WordTrace (prefixWord ++ tailWord_3223481) baseStart_3223481 baseEnd_3223481 := by
    simpa [prefixWord, tailWord_3223481, baseEnd_3223481] using wordTrace_append hprefix tailTrace_3223481
  have hstable : (prefixWord ++ tailWord_3223481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223481).length < 2 ^ (prefixWord ++ tailWord_3223481).sum := by decide
  have hdescent : baseEnd_3223481 < baseStart_3223481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223517 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 5]
def baseStart_3223517 : Nat := 118140960795 + 3223517 * 2 ^ 59
def prefixEnd_3223517 : Nat := 4983230072969 + 3 ^ 40 * 3223517 * 2
def baseEnd_3223517 : Nat := 367825248653193268580627

theorem tailTrace_3223517 : CollatzResearch.WordTrace tailWord_3223517 prefixEnd_3223517 367825248653193268580627 := by
  unfold tailWord_3223517
  simp only [CollatzResearch.WordTrace]
  refine ⟨117571323862755916718548805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78380882575170611145699203 117571323862755916718548805)
  ·
    refine ⟨22044623224266734384727901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117571323862755916718548805 22044623224266734384727901)
    ·
      refine ⟨8266733709100025394272963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22044623224266734384727901 8266733709100025394272963)
      ·
        refine ⟨12400100563650038091409445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266733709100025394272963 12400100563650038091409445)
        ·
          refine ⟨2325018855684382142139271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12400100563650038091409445 2325018855684382142139271)
          ·
            refine ⟨3487528283526573213208907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325018855684382142139271 3487528283526573213208907)
            ·
              refine ⟨5231292425289859819813361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487528283526573213208907 5231292425289859819813361)
              ·
                refine ⟨3923469318967394864860021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231292425289859819813361 3923469318967394864860021)
                ·
                  refine ⟨367825248653193268580627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923469318967394864860021 367825248653193268580627)
                  ·
                    rfl

theorem cell22_3223517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_3223517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223517 prefixEnd_3223517 := by exact prefixLift 3223517
  have htrace : WordTrace (prefixWord ++ tailWord_3223517) baseStart_3223517 baseEnd_3223517 := by
    simpa [prefixWord, tailWord_3223517, baseEnd_3223517] using wordTrace_append hprefix tailTrace_3223517
  have hstable : (prefixWord ++ tailWord_3223517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223517).length < 2 ^ (prefixWord ++ tailWord_3223517).sum := by decide
  have hdescent : baseEnd_3223517 < baseStart_3223517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223562 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_3223562 : Nat := 118140960795 + 3223562 * 2 ^ 59
def prefixEnd_3223562 : Nat := 4983230072969 + 3 ^ 40 * 3223562 * 2
def baseEnd_3223562 : Nat := 367830383459738229455581

theorem tailTrace_3223562 : CollatzResearch.WordTrace tailWord_3223562 prefixEnd_3223562 367830383459738229455581 := by
  unfold tailWord_3223562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393241286898222350984235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78381976765061926269291293 29393241286898222350984235)
  ·
    refine ⟨44089861930347333526476353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29393241286898222350984235 44089861930347333526476353)
    ·
      refine ⟨33067396447760500144857265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44089861930347333526476353 33067396447760500144857265)
      ·
        refine ⟨24800547335820375108642949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33067396447760500144857265 24800547335820375108642949)
        ·
          refine ⟨4650102625466320332870553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24800547335820375108642949 4650102625466320332870553)
          ·
            refine ⟨3487576969099740249652915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650102625466320332870553 3487576969099740249652915)
            ·
              refine ⟨5231365453649610374479373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487576969099740249652915 5231365453649610374479373)
              ·
                refine ⟨1961762045118603890429765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5231365453649610374479373 1961762045118603890429765)
                ·
                  refine ⟨367830383459738229455581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961762045118603890429765 367830383459738229455581)
                  ·
                    rfl

theorem cell22_3223562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_3223562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223562 prefixEnd_3223562 := by exact prefixLift 3223562
  have htrace : WordTrace (prefixWord ++ tailWord_3223562) baseStart_3223562 baseEnd_3223562 := by
    simpa [prefixWord, tailWord_3223562, baseEnd_3223562] using wordTrace_append hprefix tailTrace_3223562
  have hstable : (prefixWord ++ tailWord_3223562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223562).length < 2 ^ (prefixWord ++ tailWord_3223562).sum := by decide
  have hdescent : baseEnd_3223562 < baseStart_3223562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223573 : List Nat := [1, 3, 2, 1, 5, 2, 8]
def baseStart_3223573 : Nat := 118140960795 + 3223573 * 2 ^ 59
def prefixEnd_3223573 : Nat := 4983230072969 + 3 ^ 40 * 3223573 * 2
def baseEnd_3223573 : Nat := 40870182070519049123767

theorem tailTrace_3223573 : CollatzResearch.WordTrace tailWord_3223573 prefixEnd_3223573 40870182070519049123767 := by
  unfold tailWord_3223573
  simp only [CollatzResearch.WordTrace]
  refine ⟨117573366350553038282587373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78382244233702025521724915 117573366350553038282587373)
  ·
    refine ⟨44090012381457389355970265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117573366350553038282587373 44090012381457389355970265)
    ·
      refine ⟨33067509286093042016977699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44090012381457389355970265 33067509286093042016977699)
      ·
        refine ⟨49601263929139563025466549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33067509286093042016977699 49601263929139563025466549)
        ·
          refine ⟨4650118493356834033637489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49601263929139563025466549 4650118493356834033637489)
          ·
            refine ⟨3487588870017625525228117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650118493356834033637489 3487588870017625525228117)
            ·
              refine ⟨40870182070519049123767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3487588870017625525228117 40870182070519049123767)
              ·
                rfl

theorem cell22_3223573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 8].length) (baseStart_3223573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223573 prefixEnd_3223573 := by exact prefixLift 3223573
  have htrace : WordTrace (prefixWord ++ tailWord_3223573) baseStart_3223573 baseEnd_3223573 := by
    simpa [prefixWord, tailWord_3223573, baseEnd_3223573] using wordTrace_append hprefix tailTrace_3223573
  have hstable : (prefixWord ++ tailWord_3223573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223573).length < 2 ^ (prefixWord ++ tailWord_3223573).sum := by decide
  have hdescent : baseEnd_3223573 < baseStart_3223573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223575 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3223575 : Nat := 118140960795 + 3223575 * 2 ^ 59
def prefixEnd_3223575 : Nat := 4983230072969 + 3 ^ 40 * 3223575 * 2
def baseEnd_3223575 : Nat := 1103495600544886987791703

theorem tailTrace_3223575 : CollatzResearch.WordTrace tailWord_3223575 prefixEnd_3223575 1103495600544886987791703 := by
  unfold tailWord_3223575
  simp only [CollatzResearch.WordTrace]
  refine ⟨117573439296545792624160179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78382292864363861749440119 117573439296545792624160179)
  ·
    refine ⟨176360158944818688936240269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117573439296545792624160179 176360158944818688936240269)
    ·
      refine ⟨66135059604307008351090101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176360158944818688936240269 66135059604307008351090101)
      ·
        refine ⟨6200161837903782032914697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66135059604307008351090101 6200161837903782032914697)
        ·
          refine ⟨4650121378427836524686023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6200161837903782032914697 4650121378427836524686023)
          ·
            refine ⟨6975182067641754787029035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650121378427836524686023 6975182067641754787029035)
            ·
              refine ⟨10462773101462632180543553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975182067641754787029035 10462773101462632180543553)
              ·
                refine ⟨7847079826096974135407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10462773101462632180543553 7847079826096974135407665)
                ·
                  refine ⟨5885309869572730601555749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7847079826096974135407665 5885309869572730601555749)
                  ·
                    refine ⟨1103495600544886987791703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885309869572730601555749 1103495600544886987791703)
                    ·
                      rfl

theorem cell22_3223575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3223575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223575 prefixEnd_3223575 := by exact prefixLift 3223575
  have htrace : WordTrace (prefixWord ++ tailWord_3223575) baseStart_3223575 baseEnd_3223575 := by
    simpa [prefixWord, tailWord_3223575, baseEnd_3223575] using wordTrace_append hprefix tailTrace_3223575
  have hstable : (prefixWord ++ tailWord_3223575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223575).length < 2 ^ (prefixWord ++ tailWord_3223575).sum := by decide
  have hdescent : baseEnd_3223575 < baseStart_3223575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223594 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3223594 : Nat := 118140960795 + 3223594 * 2 ^ 59
def prefixEnd_3223594 : Nat := 4983230072969 + 3 ^ 40 * 3223594 * 2
def baseEnd_3223594 : Nat := 1103502104633177271566645

theorem tailTrace_3223594 : CollatzResearch.WordTrace tailWord_3223594 prefixEnd_3223594 1103502104633177271566645 := by
  unfold tailWord_3223594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393533070869239717275459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78382754855651305912734557 29393533070869239717275459)
  ·
    refine ⟨44090299606303859575913189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29393533070869239717275459 44090299606303859575913189)
    ·
      refine ⟨8266931176181973670483723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44090299606303859575913189 8266931176181973670483723)
      ·
        refine ⟨12400396764272960505725585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266931176181973670483723 12400396764272960505725585)
        ·
          refine ⟨9300297573204720379294189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12400396764272960505725585 9300297573204720379294189)
          ·
            refine ⟨3487611589951770142235321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9300297573204720379294189 3487611589951770142235321)
            ·
              refine ⟨2615708692463827606676491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487611589951770142235321 2615708692463827606676491)
              ·
                refine ⟨3923563038695741410014737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615708692463827606676491 3923563038695741410014737)
                ·
                  refine ⟨2942672279021806057511053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3923563038695741410014737 2942672279021806057511053)
                  ·
                    refine ⟨1103502104633177271566645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942672279021806057511053 1103502104633177271566645)
                    ·
                      rfl

theorem cell22_3223594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3223594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223594 prefixEnd_3223594 := by exact prefixLift 3223594
  have htrace : WordTrace (prefixWord ++ tailWord_3223594) baseStart_3223594 baseEnd_3223594 := by
    simpa [prefixWord, tailWord_3223594, baseEnd_3223594] using wordTrace_append hprefix tailTrace_3223594
  have hstable : (prefixWord ++ tailWord_3223594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223594).length < 2 ^ (prefixWord ++ tailWord_3223594).sum := by decide
  have hdescent : baseEnd_3223594 < baseStart_3223594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223648 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_3223648 : Nat := 118140960795 + 3223648 * 2 ^ 59
def prefixEnd_3223648 : Nat := 4983230072969 + 3 ^ 40 * 3223648 * 2
def baseEnd_3223648 : Nat := 1103520589936739130716479

theorem tailTrace_3223648 : CollatzResearch.WordTrace tailWord_3223648 prefixEnd_3223648 1103520589936739130716479 := by
  unfold tailWord_3223648
  simp only [CollatzResearch.WordTrace]
  refine ⟨58788050912640663045783799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78384067883520884061045065 58788050912640663045783799)
  ·
    refine ⟨88182076368960994568675699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58788050912640663045783799 88182076368960994568675699)
    ·
      refine ⟨132273114553441491853013549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88182076368960994568675699 132273114553441491853013549)
      ·
        refine ⟨49602417957540559444880081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132273114553441491853013549 49602417957540559444880081)
        ·
          refine ⟨37201813468155419583660061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49602417957540559444880081 37201813468155419583660061)
          ·
            refine ⟨13950680050558282343872523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37201813468155419583660061 13950680050558282343872523)
            ·
              refine ⟨20926020075837423515808785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950680050558282343872523 20926020075837423515808785)
              ·
                refine ⟨15694515056878067636856589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20926020075837423515808785 15694515056878067636856589)
                ·
                  refine ⟨5885443146329275363821221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15694515056878067636856589 5885443146329275363821221)
                  ·
                    refine ⟨1103520589936739130716479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885443146329275363821221 1103520589936739130716479)
                    ·
                      rfl

theorem cell22_3223648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_3223648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223648 prefixEnd_3223648 := by exact prefixLift 3223648
  have htrace : WordTrace (prefixWord ++ tailWord_3223648) baseStart_3223648 baseEnd_3223648 := by
    simpa [prefixWord, tailWord_3223648, baseEnd_3223648] using wordTrace_append hprefix tailTrace_3223648
  have hstable : (prefixWord ++ tailWord_3223648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223648).length < 2 ^ (prefixWord ++ tailWord_3223648).sum := by decide
  have hdescent : baseEnd_3223648 < baseStart_3223648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223663 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 6]
def baseStart_3223663 : Nat := 118140960795 + 3223663 * 2 ^ 59
def prefixEnd_3223663 : Nat := 4983230072969 + 3 ^ 40 * 3223663 * 2
def baseEnd_3223663 : Nat := 367841908247761363863811

theorem tailTrace_3223663 : CollatzResearch.WordTrace tailWord_3223663 prefixEnd_3223663 367841908247761363863811 := by
  unfold tailWord_3223663
  simp only [CollatzResearch.WordTrace]
  refine ⟨117576648920226983653363643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78384432613484655768909095 117576648920226983653363643)
  ·
    refine ⟨176364973380340475480045465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117576648920226983653363643 176364973380340475480045465)
    ·
      refine ⟨132273730035255356610034099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176364973380340475480045465 132273730035255356610034099)
      ·
        refine ⟨198410595052883034915051149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132273730035255356610034099 198410595052883034915051149)
        ·
          refine ⟨74403973144831138093144181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198410595052883034915051149 74403973144831138093144181)
          ·
            refine ⟨6975372482327919196232267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74403973144831138093144181 6975372482327919196232267)
            ·
              refine ⟨10463058723491878794348401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975372482327919196232267 10463058723491878794348401)
              ·
                refine ⟨7847294042618909095761301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10463058723491878794348401 7847294042618909095761301)
                ·
                  refine ⟨367841908247761363863811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7847294042618909095761301 367841908247761363863811)
                  ·
                    rfl

theorem cell22_3223663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_3223663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223663 prefixEnd_3223663 := by exact prefixLift 3223663
  have htrace : WordTrace (prefixWord ++ tailWord_3223663) baseStart_3223663 baseEnd_3223663 := by
    simpa [prefixWord, tailWord_3223663, baseEnd_3223663] using wordTrace_append hprefix tailTrace_3223663
  have hstable : (prefixWord ++ tailWord_3223663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223663).length < 2 ^ (prefixWord ++ tailWord_3223663).sum := by decide
  have hdescent : baseEnd_3223663 < baseStart_3223663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223708 : List Nat := [2, 2, 3, 2, 1, 1, 2, 9]
def baseStart_3223708 : Nat := 118140960795 + 3223708 * 2 ^ 59
def prefixEnd_3223708 : Nat := 4983230072969 + 3 ^ 40 * 3223708 * 2
def baseEnd_3223708 : Nat := 122615681018102108246255

theorem tailTrace_3223708 : CollatzResearch.WordTrace tailWord_3223708 prefixEnd_3223708 122615681018102108246255 := by
  unfold tailWord_3223708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58789145102531978169375889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78385526803375970892501185 58789145102531978169375889)
  ·
    refine ⟨44091858826898983627031917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58789145102531978169375889 44091858826898983627031917)
    ·
      refine ⟨16534447060087118860136969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44091858826898983627031917 16534447060087118860136969)
      ·
        refine ⟨12400835295065339145102727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16534447060087118860136969 12400835295065339145102727)
        ·
          refine ⟨18601252942598008717654091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12400835295065339145102727 18601252942598008717654091)
          ·
            refine ⟨27901879413897013076481137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18601252942598008717654091 27901879413897013076481137)
            ·
              refine ⟨20926409560422759807360853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27901879413897013076481137 20926409560422759807360853)
              ·
                refine ⟨122615681018102108246255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20926409560422759807360853 122615681018102108246255)
                ·
                  rfl

theorem cell22_3223708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_3223708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223708 prefixEnd_3223708 := by exact prefixLift 3223708
  have htrace : WordTrace (prefixWord ++ tailWord_3223708) baseStart_3223708 baseEnd_3223708 := by
    simpa [prefixWord, tailWord_3223708, baseEnd_3223708] using wordTrace_append hprefix tailTrace_3223708
  have hstable : (prefixWord ++ tailWord_3223708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223708).length < 2 ^ (prefixWord ++ tailWord_3223708).sum := by decide
  have hdescent : baseEnd_3223708 < baseStart_3223708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223725 : List Nat := [1, 5, 2, 1, 2, 2, 1, 8]
def baseStart_3223725 : Nat := 118140960795 + 3223725 * 2 ^ 59
def prefixEnd_3223725 : Nat := 4983230072969 + 3 ^ 40 * 3223725 * 2
def baseEnd_3223725 : Nat := 122616327623370732949027

theorem tailTrace_3223725 : CollatzResearch.WordTrace tailWord_3223725 prefixEnd_3223725 122616327623370732949027 := by
  unfold tailWord_3223725
  simp only [CollatzResearch.WordTrace]
  refine ⟨117578910246002368242120629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78385940164001578828080419 117578910246002368242120629)
  ·
    refine ⟨11023022835562722022698809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117578910246002368242120629 11023022835562722022698809)
    ·
      refine ⟨8267267126672041517024107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11023022835562722022698809 8267267126672041517024107)
      ·
        refine ⟨12400900690008062275536161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267267126672041517024107 12400900690008062275536161)
        ·
          refine ⟨9300675517506046706652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12400900690008062275536161 9300675517506046706652121)
          ·
            refine ⟨6975506638129535029989091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300675517506046706652121 6975506638129535029989091)
            ·
              refine ⟨10463259957194302544983637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975506638129535029989091 10463259957194302544983637)
              ·
                refine ⟨122616327623370732949027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10463259957194302544983637 122616327623370732949027)
                ·
                  rfl

theorem cell22_3223725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 8].length) (baseStart_3223725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223725 prefixEnd_3223725 := by exact prefixLift 3223725
  have htrace : WordTrace (prefixWord ++ tailWord_3223725) baseStart_3223725 baseEnd_3223725 := by
    simpa [prefixWord, tailWord_3223725, baseEnd_3223725] using wordTrace_append hprefix tailTrace_3223725
  have hstable : (prefixWord ++ tailWord_3223725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223725).length < 2 ^ (prefixWord ++ tailWord_3223725).sum := by decide
  have hdescent : baseEnd_3223725 < baseStart_3223725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223742 : List Nat := [4, 2, 1, 1, 5, 1, 8]
def baseStart_3223742 : Nat := 118140960795 + 3223742 * 2 ^ 59
def prefixEnd_3223742 : Nat := 4983230072969 + 3 ^ 40 * 3223742 * 2
def baseEnd_3223742 : Nat := 40872324742879785883933

theorem tailTrace_3223742 : CollatzResearch.WordTrace tailWord_3223742 prefixEnd_3223742 40872324742879785883933 := by
  unfold tailWord_3223742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697441285867597518186185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78386353524627186763659653 14697441285867597518186185)
  ·
    refine ⟨11023080964400698138639639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14697441285867597518186185 11023080964400698138639639)
    ·
      refine ⟨16534621446601047207959459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023080964400698138639639 16534621446601047207959459)
      ·
        refine ⟨24801932169901570811939189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534621446601047207959459 24801932169901570811939189)
        ·
          refine ⟨2325181140928272263619299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24801932169901570811939189 2325181140928272263619299)
          ·
            refine ⟨3487771711392408395428949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325181140928272263619299 3487771711392408395428949)
            ·
              refine ⟨40872324742879785883933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3487771711392408395428949 40872324742879785883933)
              ·
                rfl

theorem cell22_3223742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 8].length) (baseStart_3223742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223742 prefixEnd_3223742 := by exact prefixLift 3223742
  have htrace : WordTrace (prefixWord ++ tailWord_3223742) baseStart_3223742 baseEnd_3223742 := by
    simpa [prefixWord, tailWord_3223742, baseEnd_3223742] using wordTrace_append hprefix tailTrace_3223742
  have hstable : (prefixWord ++ tailWord_3223742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223742).length < 2 ^ (prefixWord ++ tailWord_3223742).sum := by decide
  have hdescent : baseEnd_3223742 < baseStart_3223742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223800 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3223800 : Nat := 118140960795 + 3223800 * 2 ^ 59
def prefixEnd_3223800 : Nat := 4983230072969 + 3 ^ 40 * 3223800 * 2
def baseEnd_3223800 : Nat := 1103572622643061400916013

theorem tailTrace_3223800 : CollatzResearch.WordTrace tailWord_3223800 prefixEnd_3223800 1103572622643061400916013 := by
  unfold tailWord_3223800
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790822860365328025550427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78387763813820437367400569 58790822860365328025550427)
  ·
    refine ⟨88186234290547992038325641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58790822860365328025550427 88186234290547992038325641)
    ·
      refine ⟨66139675717910994028744231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88186234290547992038325641 66139675717910994028744231)
      ·
        refine ⟨99209513576866491043116347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66139675717910994028744231 99209513576866491043116347)
        ·
          refine ⟨148814270365299736564674521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99209513576866491043116347 148814270365299736564674521)
          ·
            refine ⟨111610702773974802423505891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148814270365299736564674521 111610702773974802423505891)
            ·
              refine ⟨167416054160962203635258837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111610702773974802423505891 167416054160962203635258837)
              ·
                refine ⟨3923813769397551647701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167416054160962203635258837 3923813769397551647701379)
                ·
                  refine ⟨5885720654096327471552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923813769397551647701379 5885720654096327471552069)
                  ·
                    refine ⟨1103572622643061400916013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885720654096327471552069 1103572622643061400916013)
                    ·
                      rfl

theorem cell22_3223800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3223800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223800 prefixEnd_3223800 := by exact prefixLift 3223800
  have htrace : WordTrace (prefixWord ++ tailWord_3223800) baseStart_3223800 baseEnd_3223800 := by
    simpa [prefixWord, tailWord_3223800, baseEnd_3223800] using wordTrace_append hprefix tailTrace_3223800
  have hstable : (prefixWord ++ tailWord_3223800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223800).length < 2 ^ (prefixWord ++ tailWord_3223800).sum := by decide
  have hdescent : baseEnd_3223800 < baseStart_3223800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223890 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3223890 : Nat := 118140960795 + 3223890 * 2 ^ 59
def prefixEnd_3223890 : Nat := 4983230072969 + 3 ^ 40 * 3223890 * 2
def baseEnd_3223890 : Nat := 1103603431482331166165737

theorem tailTrace_3223890 : CollatzResearch.WordTrace tailWord_3223890 prefixEnd_3223890 1103603431482331166165737 := by
  unfold tailWord_3223890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396232072601150355469281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78389952193603067614584749 29396232072601150355469281)
  ·
    refine ⟨22047174054450862766601961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29396232072601150355469281 22047174054450862766601961)
    ·
      refine ⟨16535380540838147074951471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22047174054450862766601961 16535380540838147074951471)
      ·
        refine ⟨24803070811257220612427207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16535380540838147074951471 24803070811257220612427207)
        ·
          refine ⟨37204606216885830918640811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24803070811257220612427207 37204606216885830918640811)
          ·
            refine ⟨55806909325328746377961217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37204606216885830918640811 55806909325328746377961217)
            ·
              refine ⟨41855181993996559783470913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55806909325328746377961217 41855181993996559783470913)
              ·
                refine ⟨31391386495497419837603185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41855181993996559783470913 31391386495497419837603185)
                ·
                  refine ⟨23543539871623064878202389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31391386495497419837603185 23543539871623064878202389)
                  ·
                    refine ⟨1103603431482331166165737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23543539871623064878202389 1103603431482331166165737)
                    ·
                      rfl

theorem cell22_3223890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3223890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223890 prefixEnd_3223890 := by exact prefixLift 3223890
  have htrace : WordTrace (prefixWord ++ tailWord_3223890) baseStart_3223890 baseEnd_3223890 := by
    simpa [prefixWord, tailWord_3223890, baseEnd_3223890] using wordTrace_append hprefix tailTrace_3223890
  have hstable : (prefixWord ++ tailWord_3223890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223890).length < 2 ^ (prefixWord ++ tailWord_3223890).sum := by decide
  have hdescent : baseEnd_3223890 < baseStart_3223890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_3223935 : Nat := 118140960795 + 3223935 * 2 ^ 59
def prefixEnd_3223935 : Nat := 4983230072969 + 3 ^ 40 * 3223935 * 2
def baseEnd_3223935 : Nat := 1103618835901966048790599

theorem tailTrace_3223935 : CollatzResearch.WordTrace tailWord_3223935 prefixEnd_3223935 1103618835901966048790599 := by
  unfold tailWord_3223935
  simp only [CollatzResearch.WordTrace]
  refine ⟨117586569575241574107265259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78391046383494382738176839 117586569575241574107265259)
  ·
    refine ⟨176379854362862361160897889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117586569575241574107265259 176379854362862361160897889)
    ·
      refine ⟨132284890772146770870673417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176379854362862361160897889 132284890772146770870673417)
      ·
        refine ⟨99213668079110078153005063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132284890772146770870673417 99213668079110078153005063)
        ·
          refine ⟨148820502118665117229507595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99213668079110078153005063 148820502118665117229507595)
          ·
            refine ⟨223230753177997675844261393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148820502118665117229507595 223230753177997675844261393)
            ·
              refine ⟨167423064883498256883196045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223230753177997675844261393 167423064883498256883196045)
              ·
                refine ⟨62783649331311846331198517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167423064883498256883196045 62783649331311846331198517)
                ·
                  refine ⟨5885967124810485593549861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62783649331311846331198517 5885967124810485593549861)
                  ·
                    refine ⟨1103618835901966048790599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885967124810485593549861 1103618835901966048790599)
                    ·
                      rfl

theorem cell22_3223935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_3223935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223935 prefixEnd_3223935 := by exact prefixLift 3223935
  have htrace : WordTrace (prefixWord ++ tailWord_3223935) baseStart_3223935 baseEnd_3223935 := by
    simpa [prefixWord, tailWord_3223935, baseEnd_3223935] using wordTrace_append hprefix tailTrace_3223935
  have hstable : (prefixWord ++ tailWord_3223935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223935).length < 2 ^ (prefixWord ++ tailWord_3223935).sum := by decide
  have hdescent : baseEnd_3223935 < baseStart_3223935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223980 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3223980 : Nat := 118140960795 + 3223980 * 2 ^ 59
def prefixEnd_3223980 : Nat := 4983230072969 + 3 ^ 40 * 3223980 * 2
def baseEnd_3223980 : Nat := 1103634240321600931415461

theorem tailTrace_3223980 : CollatzResearch.WordTrace tailWord_3223980 prefixEnd_3223980 1103634240321600931415461 := by
  unfold tailWord_3223980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58794105430039273396326697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78392140573385697861768929 58794105430039273396326697)
  ·
    refine ⟨44095579072529455047245023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58794105430039273396326697 44095579072529455047245023)
    ·
      refine ⟨66143368608794182570867535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44095579072529455047245023 66143368608794182570867535)
      ·
        refine ⟨99215052913191273856301303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66143368608794182570867535 99215052913191273856301303)
        ·
          refine ⟨148822579369786910784451955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99215052913191273856301303 148822579369786910784451955)
          ·
            refine ⟨223233869054680366176677933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148822579369786910784451955 223233869054680366176677933)
            ·
              refine ⟨83712700895505137316254225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223233869054680366176677933 83712700895505137316254225)
              ·
                refine ⟨62784525671628852987190669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83712700895505137316254225 62784525671628852987190669)
                ·
                  refine ⟨23544197126860819870196501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62784525671628852987190669 23544197126860819870196501)
                  ·
                    refine ⟨1103634240321600931415461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23544197126860819870196501 1103634240321600931415461)
                    ·
                      rfl

theorem cell22_3223980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3223980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3223980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3223980 prefixEnd_3223980 := by exact prefixLift 3223980
  have htrace : WordTrace (prefixWord ++ tailWord_3223980) baseStart_3223980 baseEnd_3223980 := by
    simpa [prefixWord, tailWord_3223980, baseEnd_3223980] using wordTrace_append hprefix tailTrace_3223980
  have hstable : (prefixWord ++ tailWord_3223980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223980).length < 2 ^ (prefixWord ++ tailWord_3223980).sum := by decide
  have hdescent : baseEnd_3223980 < baseStart_3223980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224018 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_3224018 : Nat := 118140960795 + 3224018 * 2 ^ 59
def prefixEnd_3224018 : Nat := 4983230072969 + 3 ^ 40 * 3224018 * 2
def baseEnd_3224018 : Nat := 367882416166060499655115

theorem tailTrace_3224018 : CollatzResearch.WordTrace tailWord_3224018 prefixEnd_3224018 367882416166060499655115 := by
  unfold tailWord_3224018
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397399208485219820634177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78393064555960586188357805 29397399208485219820634177)
  ·
    refine ⟨22048049406363914865475633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29397399208485219820634177 22048049406363914865475633)
    ·
      refine ⟨16536037054772936149106725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22048049406363914865475633 16536037054772936149106725)
      ·
        refine ⟨3100506947769925527957511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16536037054772936149106725 3100506947769925527957511)
        ·
          refine ⟨4650760421654888291936267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100506947769925527957511 4650760421654888291936267)
          ·
            refine ⟨6976140632482332437904401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650760421654888291936267 6976140632482332437904401)
            ·
              refine ⟨5232105474361749328428301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976140632482332437904401 5232105474361749328428301)
              ·
                refine ⟨1962039552885655998160613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232105474361749328428301 1962039552885655998160613)
                ·
                  refine ⟨367882416166060499655115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962039552885655998160613 367882416166060499655115)
                  ·
                    rfl

theorem cell22_3224018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_3224018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224018 prefixEnd_3224018 := by exact prefixLift 3224018
  have htrace : WordTrace (prefixWord ++ tailWord_3224018) baseStart_3224018 baseEnd_3224018 := by
    simpa [prefixWord, tailWord_3224018, baseEnd_3224018] using wordTrace_append hprefix tailTrace_3224018
  have hstable : (prefixWord ++ tailWord_3224018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224018).length < 2 ^ (prefixWord ++ tailWord_3224018).sum := by decide
  have hdescent : baseEnd_3224018 < baseStart_3224018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224044 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_3224044 : Nat := 118140960795 + 3224044 * 2 ^ 59
def prefixEnd_3224044 : Nat := 4983230072969 + 3 ^ 40 * 3224044 * 2
def baseEnd_3224044 : Nat := 1103656148829526097815265

theorem tailTrace_3224044 : CollatzResearch.WordTrace tailWord_3224044 prefixEnd_3224044 1103656148829526097815265 := by
  unfold tailWord_3224044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58795272565923342861491593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78393696754564457148655457 58795272565923342861491593)
  ·
    refine ⟨44096454424442507146118695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58795272565923342861491593 44096454424442507146118695)
    ·
      refine ⟨66144681636663760719178043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44096454424442507146118695 66144681636663760719178043)
      ·
        refine ⟨99217022454995641078767065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66144681636663760719178043 99217022454995641078767065)
        ·
          refine ⟨74412766841246730809075299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99217022454995641078767065 74412766841246730809075299)
          ·
            refine ⟨111619150261870096213612949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74412766841246730809075299 111619150261870096213612949)
            ·
              refine ⟨5232147668525160760013107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111619150261870096213612949 5232147668525160760013107)
              ·
                refine ⟨7848221502787741140019661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232147668525160760013107 7848221502787741140019661)
                ·
                  refine ⟨2943083063545402927507373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848221502787741140019661 2943083063545402927507373)
                  ·
                    refine ⟨1103656148829526097815265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943083063545402927507373 1103656148829526097815265)
                    ·
                      rfl

theorem cell22_3224044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_3224044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224044 prefixEnd_3224044 := by exact prefixLift 3224044
  have htrace : WordTrace (prefixWord ++ tailWord_3224044) baseStart_3224044 baseEnd_3224044 := by
    simpa [prefixWord, tailWord_3224044, baseEnd_3224044] using wordTrace_append hprefix tailTrace_3224044
  have hstable : (prefixWord ++ tailWord_3224044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224044).length < 2 ^ (prefixWord ++ tailWord_3224044).sum := by decide
  have hdescent : baseEnd_3224044 < baseStart_3224044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224057 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 5]
def baseStart_3224057 : Nat := 118140960795 + 3224057 * 2 ^ 59
def prefixEnd_3224057 : Nat := 4983230072969 + 3 ^ 40 * 3224057 * 2
def baseEnd_3224057 : Nat := 367886866331732799080075

theorem tailTrace_3224057 : CollatzResearch.WordTrace tailWord_3224057 prefixEnd_3224057 367886866331732799080075 := by
  unfold tailWord_3224057
  simp only [CollatzResearch.WordTrace]
  refine ⟨117591019280799588943206425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78394012853866392628804283 117591019280799588943206425)
  ·
    refine ⟨88193264460599691707404819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117591019280799588943206425 88193264460599691707404819)
    ·
      refine ⟨132289896690899537561107229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88193264460599691707404819 132289896690899537561107229)
      ·
        refine ⟨49608711259087326585415211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132289896690899537561107229 49608711259087326585415211)
        ·
          refine ⟨74413066888630989878122817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49608711259087326585415211 74413066888630989878122817)
          ·
            refine ⟨55809800166473242408592113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74413066888630989878122817 55809800166473242408592113)
            ·
              refine ⟨41857350124854931806444085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55809800166473242408592113 41857350124854931806444085)
              ·
                refine ⟨3924126574205149856854133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41857350124854931806444085 3924126574205149856854133)
                ·
                  refine ⟨367886866331732799080075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924126574205149856854133 367886866331732799080075)
                  ·
                    rfl

theorem cell22_3224057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_3224057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224057 prefixEnd_3224057 := by exact prefixLift 3224057
  have htrace : WordTrace (prefixWord ++ tailWord_3224057) baseStart_3224057 baseEnd_3224057 := by
    simpa [prefixWord, tailWord_3224057, baseEnd_3224057] using wordTrace_append hprefix tailTrace_3224057
  have hstable : (prefixWord ++ tailWord_3224057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224057).length < 2 ^ (prefixWord ++ tailWord_3224057).sum := by decide
  have hdescent : baseEnd_3224057 < baseStart_3224057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224078 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3224078 : Nat := 118140960795 + 3224078 * 2 ^ 59
def prefixEnd_3224078 : Nat := 4983230072969 + 3 ^ 40 * 3224078 * 2
def baseEnd_3224078 : Nat := 1103667787724361342465161

theorem tailTrace_3224078 : CollatzResearch.WordTrace tailWord_3224078 prefixEnd_3224078 1103667787724361342465161 := by
  unfold tailWord_3224078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14698973151715438691215111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78394523475815673019813925 14698973151715438691215111)
  ·
    refine ⟨22048459727573158036822667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14698973151715438691215111 22048459727573158036822667)
    ·
      refine ⟨33072689591359737055234001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22048459727573158036822667 33072689591359737055234001)
      ·
        refine ⟨24804517193519802791425501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33072689591359737055234001 24804517193519802791425501)
        ·
          refine ⟨9301693947569926046784563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24804517193519802791425501 9301693947569926046784563)
          ·
            refine ⟨13952540921354889070176845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9301693947569926046784563 13952540921354889070176845)
            ·
              refine ⟨5232202845508083401316317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13952540921354889070176845 5232202845508083401316317)
              ·
                refine ⟨1962076067065531275493619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232202845508083401316317 1962076067065531275493619)
                ·
                  refine ⟨2943114100598296913240429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962076067065531275493619 2943114100598296913240429)
                  ·
                    refine ⟨1103667787724361342465161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943114100598296913240429 1103667787724361342465161)
                    ·
                      rfl

theorem cell22_3224078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3224078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224078 prefixEnd_3224078 := by exact prefixLift 3224078
  have htrace : WordTrace (prefixWord ++ tailWord_3224078) baseStart_3224078 baseEnd_3224078 := by
    simpa [prefixWord, tailWord_3224078, baseEnd_3224078] using wordTrace_append hprefix tailTrace_3224078
  have hstable : (prefixWord ++ tailWord_3224078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224078).length < 2 ^ (prefixWord ++ tailWord_3224078).sum := by decide
  have hdescent : baseEnd_3224078 < baseStart_3224078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224149 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3224149 : Nat := 118140960795 + 3224149 * 2 ^ 59
def prefixEnd_3224149 : Nat := 4983230072969 + 3 ^ 40 * 3224149 * 2
def baseEnd_3224149 : Nat := 1103692092475340823939943

theorem tailTrace_3224149 : CollatzResearch.WordTrace tailWord_3224149 prefixEnd_3224149 1103692092475340823939943 := by
  unfold tailWord_3224149
  simp only [CollatzResearch.WordTrace]
  refine ⟨117594374796466288655555501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78396249864310859103703667 117594374796466288655555501)
  ·
    refine ⟨44097890548674858245833313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117594374796466288655555501 44097890548674858245833313)
    ·
      refine ⟨33073417911506143684374985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44097890548674858245833313 33073417911506143684374985)
      ·
        refine ⟨24805063433629607763281239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33073417911506143684374985 24805063433629607763281239)
        ·
          refine ⟨37207595150444411644921859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24805063433629607763281239 37207595150444411644921859)
          ·
            refine ⟨55811392725666617467382789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37207595150444411644921859 55811392725666617467382789)
            ·
              refine ⟨10464636136062490775134273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55811392725666617467382789 10464636136062490775134273)
              ·
                refine ⟨7848477102046868081350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10464636136062490775134273 7848477102046868081350705)
                ·
                  refine ⟨5886357826535151061013029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848477102046868081350705 5886357826535151061013029)
                  ·
                    refine ⟨1103692092475340823939943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886357826535151061013029 1103692092475340823939943)
                    ·
                      rfl

theorem cell22_3224149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3224149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224149 prefixEnd_3224149 := by exact prefixLift 3224149
  have htrace : WordTrace (prefixWord ++ tailWord_3224149) baseStart_3224149 baseEnd_3224149 := by
    simpa [prefixWord, tailWord_3224149, baseEnd_3224149] using wordTrace_append hprefix tailTrace_3224149
  have hstable : (prefixWord ++ tailWord_3224149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224149).length < 2 ^ (prefixWord ++ tailWord_3224149).sum := by decide
  have hdescent : baseEnd_3224149 < baseStart_3224149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224151 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 2, 3]
def baseStart_3224151 : Nat := 118140960795 + 3224151 * 2 ^ 59
def prefixEnd_3224151 : Nat := 4983230072969 + 3 ^ 40 * 3224151 * 2
def baseEnd_3224151 : Nat := 1103692777116213485389937

theorem tailTrace_3224151 : CollatzResearch.WordTrace tailWord_3224151 prefixEnd_3224151 1103692777116213485389937 := by
  unfold tailWord_3224151
  simp only [CollatzResearch.WordTrace]
  refine ⟨117594447742459042997128307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78396298494972695331418871 117594447742459042997128307)
  ·
    refine ⟨176391671613688564495692461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117594447742459042997128307 176391671613688564495692461)
    ·
      refine ⟨66146876855133211685884673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176391671613688564495692461 66146876855133211685884673)
      ·
        refine ⟨49610157641349908764413505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66146876855133211685884673 49610157641349908764413505)
        ·
          refine ⟨37207618231012431573310129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49610157641349908764413505 37207618231012431573310129)
          ·
            refine ⟨27905713673259323679982597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37207618231012431573310129 27905713673259323679982597)
            ·
              refine ⟨5232321313736123189996737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27905713673259323679982597 5232321313736123189996737)
              ·
                refine ⟨3924240985302092392497553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232321313736123189996737 3924240985302092392497553)
                ·
                  refine ⟨2943180738976569294373165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924240985302092392497553 2943180738976569294373165)
                  ·
                    refine ⟨1103692777116213485389937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943180738976569294373165 1103692777116213485389937)
                    ·
                      rfl

theorem cell22_3224151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_3224151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224151 prefixEnd_3224151 := by exact prefixLift 3224151
  have htrace : WordTrace (prefixWord ++ tailWord_3224151) baseStart_3224151 baseEnd_3224151 := by
    simpa [prefixWord, tailWord_3224151, baseEnd_3224151] using wordTrace_append hprefix tailTrace_3224151
  have hstable : (prefixWord ++ tailWord_3224151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224151).length < 2 ^ (prefixWord ++ tailWord_3224151).sum := by decide
  have hdescent : baseEnd_3224151 < baseStart_3224151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_3224207 : Nat := 118140960795 + 3224207 * 2 ^ 59
def prefixEnd_3224207 : Nat := 4983230072969 + 3 ^ 40 * 3224207 * 2
def baseEnd_3224207 : Nat := 1103711947060648005989765

theorem tailTrace_3224207 : CollatzResearch.WordTrace tailWord_3224207 prefixEnd_3224207 1103711947060648005989765 := by
  unfold tailWord_3224207
  simp only [CollatzResearch.WordTrace]
  refine ⟨117596490230256164561166875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78397660153504109707444583 117596490230256164561166875)
  ·
    refine ⟨176394735345384246841750313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117596490230256164561166875 176394735345384246841750313)
    ·
      refine ⟨132296051509038185131312735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176394735345384246841750313 132296051509038185131312735)
      ·
        refine ⟨198444077263557277696969103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132296051509038185131312735 198444077263557277696969103)
        ·
          refine ⟨297666115895335916545453655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198444077263557277696969103 297666115895335916545453655)
          ·
            refine ⟨446499173843003874818180483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297666115895335916545453655 446499173843003874818180483)
            ·
              refine ⟨669748760764505812227270725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446499173843003874818180483 669748760764505812227270725)
              ·
                refine ⟨125577892643344839792613261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669748760764505812227270725 125577892643344839792613261)
                ·
                  refine ⟨47091709741254314922229973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125577892643344839792613261 47091709741254314922229973)
                  ·
                    refine ⟨1103711947060648005989765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47091709741254314922229973 1103711947060648005989765)
                    ·
                      rfl

theorem cell22_3224207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_3224207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224207 prefixEnd_3224207 := by exact prefixLift 3224207
  have htrace : WordTrace (prefixWord ++ tailWord_3224207) baseStart_3224207 baseEnd_3224207 := by
    simpa [prefixWord, tailWord_3224207, baseEnd_3224207] using wordTrace_append hprefix tailTrace_3224207
  have hstable : (prefixWord ++ tailWord_3224207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224207).length < 2 ^ (prefixWord ++ tailWord_3224207).sum := by decide
  have hdescent : baseEnd_3224207 < baseStart_3224207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224247 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 1, 3]
def baseStart_3224247 : Nat := 118140960795 + 3224247 * 2 ^ 59
def prefixEnd_3224247 : Nat := 4983230072969 + 3 ^ 40 * 3224247 * 2
def baseEnd_3224247 : Nat := 1103725639878101234989643

theorem tailTrace_3224247 : CollatzResearch.WordTrace tailWord_3224247 prefixEnd_3224247 1103725639878101234989643 := by
  unfold tailWord_3224247
  simp only [CollatzResearch.WordTrace]
  refine ⟨117597949150111251392622995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78398632766740834261748663 117597949150111251392622995)
  ·
    refine ⟨176396923725166877088934493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117597949150111251392622995 176396923725166877088934493)
    ·
      refine ⟨66148846396937578908350435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176396923725166877088934493 66148846396937578908350435)
      ·
        refine ⟨99223269595406368362525653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66148846396937578908350435 99223269595406368362525653)
        ·
          refine ⟨2325545381142336758496695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99223269595406368362525653 2325545381142336758496695)
          ·
            refine ⟨3488318071713505137745043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325545381142336758496695 3488318071713505137745043)
            ·
              refine ⟨5232477107570257706617565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488318071713505137745043 5232477107570257706617565)
              ·
                refine ⟨1962178915338846639981587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232477107570257706617565 1962178915338846639981587)
                ·
                  refine ⟨2943268373008269959972381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962178915338846639981587 2943268373008269959972381)
                  ·
                    refine ⟨1103725639878101234989643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943268373008269959972381 1103725639878101234989643)
                    ·
                      rfl

theorem cell22_3224247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_3224247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224247 prefixEnd_3224247 := by exact prefixLift 3224247
  have htrace : WordTrace (prefixWord ++ tailWord_3224247) baseStart_3224247 baseEnd_3224247 := by
    simpa [prefixWord, tailWord_3224247, baseEnd_3224247] using wordTrace_append hprefix tailTrace_3224247
  have hstable : (prefixWord ++ tailWord_3224247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224247).length < 2 ^ (prefixWord ++ tailWord_3224247).sum := by decide
  have hdescent : baseEnd_3224247 < baseStart_3224247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224256 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_3224256 : Nat := 118140960795 + 3224256 * 2 ^ 59
def prefixEnd_3224256 : Nat := 4983230072969 + 3 ^ 40 * 3224256 * 2
def baseEnd_3224256 : Nat := 1103728720762028211514615

theorem tailTrace_3224256 : CollatzResearch.WordTrace tailWord_3224256 prefixEnd_3224256 1103728720762028211514615 := by
  unfold tailWord_3224256
  simp only [CollatzResearch.WordTrace]
  refine ⟨58799138703539322964850311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78398851604719097286467081 58799138703539322964850311)
  ·
    refine ⟨88198708055308984447275467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58799138703539322964850311 88198708055308984447275467)
    ·
      refine ⟨132298062082963476670913201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88198708055308984447275467 132298062082963476670913201)
      ·
        refine ⟨99223546562222607503184901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132298062082963476670913201 99223546562222607503184901)
        ·
          refine ⟨18604414980416738906847169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99223546562222607503184901 18604414980416738906847169)
          ·
            refine ⟨13953311235312554180135377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18604414980416738906847169 13953311235312554180135377)
            ·
              refine ⟨10464983426484415635101533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13953311235312554180135377 10464983426484415635101533)
              ·
                refine ⟨3924368784931655863163075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464983426484415635101533 3924368784931655863163075)
                ·
                  refine ⟨5886553177397483794744613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924368784931655863163075 5886553177397483794744613)
                  ·
                    refine ⟨1103728720762028211514615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886553177397483794744613 1103728720762028211514615)
                    ·
                      rfl

theorem cell22_3224256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_3224256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224256 prefixEnd_3224256 := by exact prefixLift 3224256
  have htrace : WordTrace (prefixWord ++ tailWord_3224256) baseStart_3224256 baseEnd_3224256 := by
    simpa [prefixWord, tailWord_3224256, baseEnd_3224256] using wordTrace_append hprefix tailTrace_3224256
  have hstable : (prefixWord ++ tailWord_3224256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224256).length < 2 ^ (prefixWord ++ tailWord_3224256).sum := by decide
  have hdescent : baseEnd_3224256 < baseStart_3224256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224277 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 5]
def baseStart_3224277 : Nat := 118140960795 + 3224277 * 2 ^ 59
def prefixEnd_3224277 : Nat := 4983230072969 + 3 ^ 40 * 3224277 * 2
def baseEnd_3224277 : Nat := 367911969830397052246517

theorem tailTrace_3224277 : CollatzResearch.WordTrace tailWord_3224277 prefixEnd_3224277 367911969830397052246517 := by
  unfold tailWord_3224277
  simp only [CollatzResearch.WordTrace]
  refine ⟨117599043340002566516215085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78399362226668377677476723 117599043340002566516215085)
  ·
    refine ⟨44099641252500962443580657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117599043340002566516215085 44099641252500962443580657)
    ·
      refine ⟨33074730939375721832685493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44099641252500962443580657 33074730939375721832685493)
      ·
        refine ⟨3100756025566473921814265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33074730939375721832685493 3100756025566473921814265)
        ·
          refine ⟨2325567019174855441360699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100756025566473921814265 2325567019174855441360699)
          ·
            refine ⟨3488350528762283162041049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325567019174855441360699 3488350528762283162041049)
            ·
              refine ⟨2616262896571712371530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488350528762283162041049 2616262896571712371530787)
              ·
                refine ⟨3924394344857568557296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616262896571712371530787 3924394344857568557296181)
                ·
                  refine ⟨367911969830397052246517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924394344857568557296181 367911969830397052246517)
                  ·
                    rfl

theorem cell22_3224277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_3224277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224277 prefixEnd_3224277 := by exact prefixLift 3224277
  have htrace : WordTrace (prefixWord ++ tailWord_3224277) baseStart_3224277 baseEnd_3224277 := by
    simpa [prefixWord, tailWord_3224277, baseEnd_3224277] using wordTrace_append hprefix tailTrace_3224277
  have hstable : (prefixWord ++ tailWord_3224277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224277).length < 2 ^ (prefixWord ++ tailWord_3224277).sum := by decide
  have hdescent : baseEnd_3224277 < baseStart_3224277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224318 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3224318 : Nat := 118140960795 + 3224318 * 2 ^ 59
def prefixEnd_3224318 : Nat := 4983230072969 + 3 ^ 40 * 3224318 * 2
def baseEnd_3224318 : Nat := 1103749944629080716464425

theorem tailTrace_3224318 : CollatzResearch.WordTrace tailWord_3224318 prefixEnd_3224318 1103749944629080716464425 := by
  unfold tailWord_3224318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700067341606753814807201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78400359155236020345638405 14700067341606753814807201)
  ·
    refine ⟨11025050506205065361105401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14700067341606753814807201 11025050506205065361105401)
    ·
      refine ⟨8268787879653799020829051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11025050506205065361105401 8268787879653799020829051)
      ·
        refine ⟨12403181819480698531243577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268787879653799020829051 12403181819480698531243577)
        ·
          refine ⟨9302386364610523898432683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12403181819480698531243577 9302386364610523898432683)
          ·
            refine ⟨13953579546915785847649025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9302386364610523898432683 13953579546915785847649025)
            ·
              refine ⟨10465184660186839385736769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13953579546915785847649025 10465184660186839385736769)
              ·
                refine ⟨7848888495140129539302577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465184660186839385736769 7848888495140129539302577)
                ·
                  refine ⟨5886666371355097154476933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848888495140129539302577 5886666371355097154476933)
                  ·
                    refine ⟨1103749944629080716464425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886666371355097154476933 1103749944629080716464425)
                    ·
                      rfl

theorem cell22_3224318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3224318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224318 prefixEnd_3224318 := by exact prefixLift 3224318
  have htrace : WordTrace (prefixWord ++ tailWord_3224318) baseStart_3224318 baseEnd_3224318 := by
    simpa [prefixWord, tailWord_3224318, baseEnd_3224318] using wordTrace_append hprefix tailTrace_3224318
  have hstable : (prefixWord ++ tailWord_3224318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224318).length < 2 ^ (prefixWord ++ tailWord_3224318).sum := by decide
  have hdescent : baseEnd_3224318 < baseStart_3224318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224322 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3224322 : Nat := 118140960795 + 3224322 * 2 ^ 59
def prefixEnd_3224322 : Nat := 4983230072969 + 3 ^ 40 * 3224322 * 2
def baseEnd_3224322 : Nat := 367917104636942013121471

theorem tailTrace_3224322 : CollatzResearch.WordTrace tailWord_3224322 prefixEnd_3224322 367917104636942013121471 := by
  unfold tailWord_3224322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29400171156209884800400805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78400456416559692801068813 29400171156209884800400805)
  ·
    refine ⟨5512532091789353400075151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29400171156209884800400805 5512532091789353400075151)
    ·
      refine ⟨8268798137684030100112727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512532091789353400075151 8268798137684030100112727)
      ·
        refine ⟨12403197206526045150169091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268798137684030100112727 12403197206526045150169091)
        ·
          refine ⟨18604795809789067725253637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403197206526045150169091 18604795809789067725253637)
          ·
            refine ⟨3488399214335450198485057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18604795809789067725253637 3488399214335450198485057)
            ·
              refine ⟨2616299410751587648863793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488399214335450198485057 2616299410751587648863793)
              ·
                refine ⟨1962224558063690736647845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616299410751587648863793 1962224558063690736647845)
                ·
                  refine ⟨367917104636942013121471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962224558063690736647845 367917104636942013121471)
                  ·
                    rfl

theorem cell22_3224322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3224322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224322 prefixEnd_3224322 := by exact prefixLift 3224322
  have htrace : WordTrace (prefixWord ++ tailWord_3224322) baseStart_3224322 baseEnd_3224322 := by
    simpa [prefixWord, tailWord_3224322, baseEnd_3224322] using wordTrace_append hprefix tailTrace_3224322
  have hstable : (prefixWord ++ tailWord_3224322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224322).length < 2 ^ (prefixWord ++ tailWord_3224322).sum := by decide
  have hdescent : baseEnd_3224322 < baseStart_3224322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224329 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3224329 : Nat := 118140960795 + 3224329 * 2 ^ 59
def prefixEnd_3224329 : Nat := 4983230072969 + 3 ^ 40 * 3224329 * 2
def baseEnd_3224329 : Nat := 1103753710153880354439391

theorem tailTrace_3224329 : CollatzResearch.WordTrace tailWord_3224329 prefixEnd_3224329 1103753710153880354439391 := by
  unfold tailWord_3224329
  simp only [CollatzResearch.WordTrace]
  refine ⟨117600939935814179397108041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78400626623876119598072027 117600939935814179397108041)
  ·
    refine ⟨88200704951860634547831031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117600939935814179397108041 88200704951860634547831031)
    ·
      refine ⟨132301057427790951821746547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88200704951860634547831031 132301057427790951821746547)
      ·
        refine ⟨198451586141686427732619821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132301057427790951821746547 198451586141686427732619821)
        ·
          refine ⟨74419344803132410399732433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198451586141686427732619821 74419344803132410399732433)
          ·
            refine ⟨55814508602349307799799325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74419344803132410399732433 55814508602349307799799325)
            ·
              refine ⟨20930440725880990424924747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55814508602349307799799325 20930440725880990424924747)
              ·
                refine ⟨31395661088821485637387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20930440725880990424924747 31395661088821485637387121)
                ·
                  refine ⟨23546745816616114228040341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31395661088821485637387121 23546745816616114228040341)
                  ·
                    refine ⟨1103753710153880354439391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23546745816616114228040341 1103753710153880354439391)
                    ·
                      rfl

theorem cell22_3224329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3224329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224329 prefixEnd_3224329 := by exact prefixLift 3224329
  have htrace : WordTrace (prefixWord ++ tailWord_3224329) baseStart_3224329 baseEnd_3224329 := by
    simpa [prefixWord, tailWord_3224329, baseEnd_3224329] using wordTrace_append hprefix tailTrace_3224329
  have hstable : (prefixWord ++ tailWord_3224329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224329).length < 2 ^ (prefixWord ++ tailWord_3224329).sum := by decide
  have hdescent : baseEnd_3224329 < baseStart_3224329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224331 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 3, 3]
def baseStart_3224331 : Nat := 118140960795 + 3224331 * 2 ^ 59
def prefixEnd_3224331 : Nat := 4983230072969 + 3 ^ 40 * 3224331 * 2
def baseEnd_3224331 : Nat := 1103754394794753015889385

theorem tailTrace_3224331 : CollatzResearch.WordTrace tailWord_3224331 prefixEnd_3224331 1103754394794753015889385 := by
  unfold tailWord_3224331
  simp only [CollatzResearch.WordTrace]
  refine ⟨117601012881806933738680847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78400675254537955825787231 117601012881806933738680847)
  ·
    refine ⟨176401519322710400608021271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117601012881806933738680847 176401519322710400608021271)
    ·
      refine ⟨264602278984065600912031907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176401519322710400608021271 264602278984065600912031907)
      ·
        refine ⟨396903418476098401368047861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264602278984065600912031907 396903418476098401368047861)
        ·
          refine ⟨37209695482134225128254487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 396903418476098401368047861 37209695482134225128254487)
          ·
            refine ⟨55814543223201337692381731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37209695482134225128254487 55814543223201337692381731)
            ·
              refine ⟨83721814834802006538572597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55814543223201337692381731 83721814834802006538572597)
              ·
                refine ⟨7848920140762688112991181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83721814834802006538572597 7848920140762688112991181)
                ·
                  refine ⟨2943345052786008042371693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848920140762688112991181 2943345052786008042371693)
                  ·
                    refine ⟨1103754394794753015889385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943345052786008042371693 1103754394794753015889385)
                    ·
                      rfl

theorem cell22_3224331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].length) (baseStart_3224331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224331 prefixEnd_3224331 := by exact prefixLift 3224331
  have htrace : WordTrace (prefixWord ++ tailWord_3224331) baseStart_3224331 baseEnd_3224331 := by
    simpa [prefixWord, tailWord_3224331, baseEnd_3224331] using wordTrace_append hprefix tailTrace_3224331
  have hstable : (prefixWord ++ tailWord_3224331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224331).length < 2 ^ (prefixWord ++ tailWord_3224331).sum := by decide
  have hdescent : baseEnd_3224331 < baseStart_3224331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224344 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_3224344 : Nat := 118140960795 + 3224344 * 2 ^ 59
def prefixEnd_3224344 : Nat := 4983230072969 + 3 ^ 40 * 3224344 * 2
def baseEnd_3224344 : Nat := 367919614986808438438115

theorem tailTrace_3224344 : CollatzResearch.WordTrace tailWord_3224344 prefixEnd_3224344 367919614986808438438115 := by
  unfold tailWord_3224344
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800743515379918479452043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78400991353839891305936057 58800743515379918479452043)
  ·
    refine ⟨88201115273069877719178065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58800743515379918479452043 88201115273069877719178065)
    ·
      refine ⟨66150836454802408289383549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88201115273069877719178065 66150836454802408289383549)
      ·
        refine ⟨24806563670550903108518831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66150836454802408289383549 24806563670550903108518831)
        ·
          refine ⟨37209845505826354662778247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24806563670550903108518831 37209845505826354662778247)
          ·
            refine ⟨55814768258739531994167371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37209845505826354662778247 55814768258739531994167371)
            ·
              refine ⟨83722152388109297991251057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55814768258739531994167371 83722152388109297991251057)
              ·
                refine ⟨62791614291081973493438293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83722152388109297991251057 62791614291081973493438293)
                ·
                  refine ⟨367919614986808438438115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62791614291081973493438293 367919614986808438438115)
                  ·
                    rfl

theorem cell22_3224344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_3224344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224344 prefixEnd_3224344 := by exact prefixLift 3224344
  have htrace : WordTrace (prefixWord ++ tailWord_3224344) baseStart_3224344 baseEnd_3224344 := by
    simpa [prefixWord, tailWord_3224344, baseEnd_3224344] using wordTrace_append hprefix tailTrace_3224344
  have hstable : (prefixWord ++ tailWord_3224344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224344).length < 2 ^ (prefixWord ++ tailWord_3224344).sum := by decide
  have hdescent : baseEnd_3224344 < baseStart_3224344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224348 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3224348 : Nat := 118140960795 + 3224348 * 2 ^ 59
def prefixEnd_3224348 : Nat := 4983230072969 + 3 ^ 40 * 3224348 * 2
def baseEnd_3224348 : Nat := 1103760214242170638214333

theorem tailTrace_3224348 : CollatzResearch.WordTrace tailWord_3224348 prefixEnd_3224348 1103760214242170638214333 := by
  unfold tailWord_3224348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800816461372672821024849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78401088615163563761366465 58800816461372672821024849)
  ·
    refine ⟨44100612346029504615768637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58800816461372672821024849 44100612346029504615768637)
    ·
      refine ⟨16537729629761064230913239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44100612346029504615768637 16537729629761064230913239)
      ·
        refine ⟨24806594444641596346369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16537729629761064230913239 24806594444641596346369859)
        ·
          refine ⟨37209891666962394519554789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24806594444641596346369859 37209891666962394519554789)
          ·
            refine ⟨6976854687555448972416523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37209891666962394519554789 6976854687555448972416523)
            ·
              refine ⟨10465282031333173458624785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976854687555448972416523 10465282031333173458624785)
              ·
                refine ⟨7848961523499880093968589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465282031333173458624785 7848961523499880093968589)
                ·
                  refine ⟨2943360571312455035238221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848961523499880093968589 2943360571312455035238221)
                  ·
                    refine ⟨1103760214242170638214333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943360571312455035238221 1103760214242170638214333)
                    ·
                      rfl

theorem cell22_3224348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3224348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224348 prefixEnd_3224348 := by exact prefixLift 3224348
  have htrace : WordTrace (prefixWord ++ tailWord_3224348) baseStart_3224348 baseEnd_3224348 := by
    simpa [prefixWord, tailWord_3224348, baseEnd_3224348] using wordTrace_append hprefix tailTrace_3224348
  have hstable : (prefixWord ++ tailWord_3224348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224348).length < 2 ^ (prefixWord ++ tailWord_3224348).sum := by decide
  have hdescent : baseEnd_3224348 < baseStart_3224348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224421 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3224421 : Nat := 118140960795 + 3224421 * 2 ^ 59
def prefixEnd_3224421 : Nat := 4983230072969 + 3 ^ 40 * 3224421 * 2
def baseEnd_3224421 : Nat := 1103785203634022781139109

theorem tailTrace_3224421 : CollatzResearch.WordTrace tailWord_3224421 prefixEnd_3224421 1103785203634022781139109 := by
  unfold tailWord_3224421
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604295451480879109457117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78402863634320586072971411 117604295451480879109457117)
  ·
    refine ⟨44101610794305329666046419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117604295451480879109457117 44101610794305329666046419)
    ·
      refine ⟨66152416191457994499069629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44101610794305329666046419 66152416191457994499069629)
      ·
        refine ⟨24807156071796747937151111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66152416191457994499069629 24807156071796747937151111)
        ·
          refine ⟨37210734107695121905726667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24807156071796747937151111 37210734107695121905726667)
          ·
            refine ⟨55816101161542682858590001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37210734107695121905726667 55816101161542682858590001)
            ·
              refine ⟨41862075871157012143942501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55816101161542682858590001 41862075871157012143942501)
              ·
                refine ⟨7849139225841939776989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41862075871157012143942501 7849139225841939776989219)
                ·
                  refine ⟨11773708838762909665483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7849139225841939776989219 11773708838762909665483829)
                  ·
                    refine ⟨1103785203634022781139109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11773708838762909665483829 1103785203634022781139109)
                    ·
                      rfl

theorem cell22_3224421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3224421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224421 prefixEnd_3224421 := by exact prefixLift 3224421
  have htrace : WordTrace (prefixWord ++ tailWord_3224421) baseStart_3224421 baseEnd_3224421 := by
    simpa [prefixWord, tailWord_3224421, baseEnd_3224421] using wordTrace_append hprefix tailTrace_3224421
  have hstable : (prefixWord ++ tailWord_3224421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224421).length < 2 ^ (prefixWord ++ tailWord_3224421).sum := by decide
  have hdescent : baseEnd_3224421 < baseStart_3224421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224451 : List Nat := [1, 1, 1, 3, 4, 1, 4, 7]
def baseStart_3224451 : Nat := 118140960795 + 3224451 * 2 ^ 59
def prefixEnd_3224451 : Nat := 4983230072969 + 3 ^ 40 * 3224451 * 2
def baseEnd_3224451 : Nat := 122643941471901411432113

theorem tailTrace_3224451 : CollatzResearch.WordTrace tailWord_3224451 prefixEnd_3224451 122643941471901411432113 := by
  unfold tailWord_3224451
  simp only [CollatzResearch.WordTrace]
  refine ⟨117605389641372194233049207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403593094248129488699471 117605389641372194233049207)
  ·
    refine ⟨176408084462058291349573811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117605389641372194233049207 176408084462058291349573811)
    ·
      refine ⟨264612126693087437024360717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176408084462058291349573811 264612126693087437024360717)
      ·
        refine ⟨99229547509907788884135269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264612126693087437024360717 99229547509907788884135269)
        ·
          refine ⟨18605540158107710415775363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99229547509907788884135269 18605540158107710415775363)
          ·
            refine ⟨27908310237161565623663045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18605540158107710415775363 27908310237161565623663045)
            ·
              refine ⟨5232808169467793554436821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27908310237161565623663045 5232808169467793554436821)
              ·
                refine ⟨122643941471901411432113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5232808169467793554436821 122643941471901411432113)
                ·
                  rfl

theorem cell22_3224451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 7].length) (baseStart_3224451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224451 prefixEnd_3224451 := by exact prefixLift 3224451
  have htrace : WordTrace (prefixWord ++ tailWord_3224451) baseStart_3224451 baseEnd_3224451 := by
    simpa [prefixWord, tailWord_3224451, baseEnd_3224451] using wordTrace_append hprefix tailTrace_3224451
  have hstable : (prefixWord ++ tailWord_3224451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224451).length < 2 ^ (prefixWord ++ tailWord_3224451).sum := by decide
  have hdescent : baseEnd_3224451 < baseStart_3224451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224455 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3224455 : Nat := 118140960795 + 3224455 * 2 ^ 59
def prefixEnd_3224455 : Nat := 4983230072969 + 3 ^ 40 * 3224455 * 2
def baseEnd_3224455 : Nat := 1103796842528858025789005

theorem tailTrace_3224455 : CollatzResearch.WordTrace tailWord_3224455 prefixEnd_3224455 1103796842528858025789005 := by
  unfold tailWord_3224455
  simp only [CollatzResearch.WordTrace]
  refine ⟨117605535533357702916194819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403690355571801944129879 117605535533357702916194819)
  ·
    refine ⟨176408303300036554374292229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117605535533357702916194819 176408303300036554374292229)
    ·
      refine ⟨33076556868756853945179793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176408303300036554374292229 33076556868756853945179793)
      ·
        refine ⟨24807417651567640458884845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33076556868756853945179793 24807417651567640458884845)
        ·
          refine ⟨9302781619337865172081817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24807417651567640458884845 9302781619337865172081817)
          ·
            refine ⟨6977086214503398879061363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9302781619337865172081817 6977086214503398879061363)
            ·
              refine ⟨10465629321755098318592045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6977086214503398879061363 10465629321755098318592045)
              ·
                refine ⟨3924610995658161869472017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10465629321755098318592045 3924610995658161869472017)
                ·
                  refine ⟨2943458246743621402104013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924610995658161869472017 2943458246743621402104013)
                  ·
                    refine ⟨1103796842528858025789005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943458246743621402104013 1103796842528858025789005)
                    ·
                      rfl

theorem cell22_3224455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3224455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224455 prefixEnd_3224455 := by exact prefixLift 3224455
  have htrace : WordTrace (prefixWord ++ tailWord_3224455) baseStart_3224455 baseEnd_3224455 := by
    simpa [prefixWord, tailWord_3224455, baseEnd_3224455] using wordTrace_append hprefix tailTrace_3224455
  have hstable : (prefixWord ++ tailWord_3224455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224455).length < 2 ^ (prefixWord ++ tailWord_3224455).sum := by decide
  have hdescent : baseEnd_3224455 < baseStart_3224455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224534 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3224534 : Nat := 118140960795 + 3224534 * 2 ^ 59
def prefixEnd_3224534 : Nat := 4983230072969 + 3 ^ 40 * 3224534 * 2
def baseEnd_3224534 : Nat := 1103823885843328153063763

theorem tailTrace_3224534 : CollatzResearch.WordTrace tailWord_3224534 prefixEnd_3224534 1103823885843328153063763 := by
  unfold tailWord_3224534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350526056254468713020041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78405611266714332938880437 7350526056254468713020041)
  ·
    refine ⟨5512894542190851534765031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7350526056254468713020041 5512894542190851534765031)
    ·
      refine ⟨8269341813286277302147547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512894542190851534765031 8269341813286277302147547)
      ·
        refine ⟨12404012719929415953221321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8269341813286277302147547 12404012719929415953221321)
        ·
          refine ⟨9303009539947061964915991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12404012719929415953221321 9303009539947061964915991)
          ·
            refine ⟨13954514309920592947373987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303009539947061964915991 13954514309920592947373987)
            ·
              refine ⟨20931771464880889421060981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954514309920592947373987 20931771464880889421060981)
              ·
                refine ⟨1962353574832583383224467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20931771464880889421060981 1962353574832583383224467)
                ·
                  refine ⟨2943530362248875074836701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962353574832583383224467 2943530362248875074836701)
                  ·
                    refine ⟨1103823885843328153063763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943530362248875074836701 1103823885843328153063763)
                    ·
                      rfl

theorem cell22_3224534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3224534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224534 prefixEnd_3224534 := by exact prefixLift 3224534
  have htrace : WordTrace (prefixWord ++ tailWord_3224534) baseStart_3224534 baseEnd_3224534 := by
    simpa [prefixWord, tailWord_3224534, baseEnd_3224534] using wordTrace_append hprefix tailTrace_3224534
  have hstable : (prefixWord ++ tailWord_3224534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224534).length < 2 ^ (prefixWord ++ tailWord_3224534).sum := by decide
  have hdescent : baseEnd_3224534 < baseStart_3224534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224556 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3224556 : Nat := 118140960795 + 3224556 * 2 ^ 59
def prefixEnd_3224556 : Nat := 4983230072969 + 3 ^ 40 * 3224556 * 2
def baseEnd_3224556 : Nat := 1103831416892927429013695

theorem tailTrace_3224556 : CollatzResearch.WordTrace tailWord_3224556 prefixEnd_3224556 1103831416892927429013695 := by
  unfold tailWord_3224556
  simp only [CollatzResearch.WordTrace]
  refine ⟨58804609652995898582810761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78406146203994531443747681 58804609652995898582810761)
  ·
    refine ⟨44103457239746923937108071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58804609652995898582810761 44103457239746923937108071)
    ·
      refine ⟨66155185859620385905662107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44103457239746923937108071 66155185859620385905662107)
      ·
        refine ⟨99232778789430578858493161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66155185859620385905662107 99232778789430578858493161)
        ·
          refine ⟨74424584092072934143869871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99232778789430578858493161 74424584092072934143869871)
          ·
            refine ⟨111636876138109401215804807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74424584092072934143869871 111636876138109401215804807)
            ·
              refine ⟨167455314207164101823707211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111636876138109401215804807 167455314207164101823707211)
              ·
                refine ⟨251182971310746152735560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167455314207164101823707211 251182971310746152735560817)
                ·
                  refine ⟨188387228483059614551670613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251182971310746152735560817 188387228483059614551670613)
                  ·
                    refine ⟨1103831416892927429013695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188387228483059614551670613 1103831416892927429013695)
                    ·
                      rfl

theorem cell22_3224556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3224556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224556 prefixEnd_3224556 := by exact prefixLift 3224556
  have htrace : WordTrace (prefixWord ++ tailWord_3224556) baseStart_3224556 baseEnd_3224556 := by
    simpa [prefixWord, tailWord_3224556, baseEnd_3224556] using wordTrace_append hprefix tailTrace_3224556
  have hstable : (prefixWord ++ tailWord_3224556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224556).length < 2 ^ (prefixWord ++ tailWord_3224556).sum := by decide
  have hdescent : baseEnd_3224556 < baseStart_3224556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224588 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3224588 : Nat := 118140960795 + 3224588 * 2 ^ 59
def prefixEnd_3224588 : Nat := 4983230072969 + 3 ^ 40 * 3224588 * 2
def baseEnd_3224588 : Nat := 1103842371146890012213597

theorem tailTrace_3224588 : CollatzResearch.WordTrace tailWord_3224588 prefixEnd_3224588 1103842371146890012213597 := by
  unfold tailWord_3224588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58805193220937933315393209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78406924294583911087190945 58805193220937933315393209)
  ·
    refine ⟨44103894915703449986544907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58805193220937933315393209 44103894915703449986544907)
    ·
      refine ⟨66155842373555174979817361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44103894915703449986544907 66155842373555174979817361)
      ·
        refine ⟨49616881780166381234863021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66155842373555174979817361 49616881780166381234863021)
        ·
          refine ⟨18606330667562392963073633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49616881780166381234863021 18606330667562392963073633)
          ·
            refine ⟨13954748000671794722305225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18606330667562392963073633 13954748000671794722305225)
            ·
              refine ⟨10466061000503846041728919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13954748000671794722305225 10466061000503846041728919)
              ·
                refine ⟨15699091500755769062593379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10466061000503846041728919 15699091500755769062593379)
                ·
                  refine ⟨23548637251133653593890069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15699091500755769062593379 23548637251133653593890069)
                  ·
                    refine ⟨1103842371146890012213597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23548637251133653593890069 1103842371146890012213597)
                    ·
                      rfl

theorem cell22_3224588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3224588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224588 prefixEnd_3224588 := by exact prefixLift 3224588
  have htrace : WordTrace (prefixWord ++ tailWord_3224588) baseStart_3224588 baseEnd_3224588 := by
    simpa [prefixWord, tailWord_3224588, baseEnd_3224588] using wordTrace_append hprefix tailTrace_3224588
  have hstable : (prefixWord ++ tailWord_3224588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224588).length < 2 ^ (prefixWord ++ tailWord_3224588).sum := by decide
  have hdescent : baseEnd_3224588 < baseStart_3224588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224590 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3224590 : Nat := 118140960795 + 3224590 * 2 ^ 59
def prefixEnd_3224590 : Nat := 4983230072969 + 3 ^ 40 * 3224590 * 2
def baseEnd_3224590 : Nat := 1103843055787762673663591

theorem tailTrace_3224590 : CollatzResearch.WordTrace tailWord_3224590 prefixEnd_3224590 1103843055787762673663591 := by
  unfold tailWord_3224590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701307423483577621544903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78406972925245747314906149 14701307423483577621544903)
  ·
    refine ⟨22051961135225366432317355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14701307423483577621544903 22051961135225366432317355)
    ·
      refine ⟨33077941702838049648476033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22051961135225366432317355 33077941702838049648476033)
      ·
        refine ⟨24808456277128537236357025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33077941702838049648476033 24808456277128537236357025)
        ·
          refine ⟨18606342207846402927267769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24808456277128537236357025 18606342207846402927267769)
          ·
            refine ⟨13954756655884802195450827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18606342207846402927267769 13954756655884802195450827)
            ·
              refine ⟨20932134983827203293176241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954756655884802195450827 20932134983827203293176241)
              ·
                refine ⟨15699101237870402469882181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20932134983827203293176241 15699101237870402469882181)
                ·
                  refine ⟨2943581482100700463102909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15699101237870402469882181 2943581482100700463102909)
                  ·
                    refine ⟨1103843055787762673663591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943581482100700463102909 1103843055787762673663591)
                    ·
                      rfl

theorem cell22_3224590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3224590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224590 prefixEnd_3224590 := by exact prefixLift 3224590
  have htrace : WordTrace (prefixWord ++ tailWord_3224590) baseStart_3224590 baseEnd_3224590 := by
    simpa [prefixWord, tailWord_3224590, baseEnd_3224590] using wordTrace_append hprefix tailTrace_3224590
  have hstable : (prefixWord ++ tailWord_3224590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224590).length < 2 ^ (prefixWord ++ tailWord_3224590).sum := by decide
  have hdescent : baseEnd_3224590 < baseStart_3224590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224652 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_3224652 : Nat := 118140960795 + 3224652 * 2 ^ 59
def prefixEnd_3224652 : Nat := 4983230072969 + 3 ^ 40 * 3224652 * 2
def baseEnd_3224652 : Nat := 1103864279654815178613401

theorem tailTrace_3224652 : CollatzResearch.WordTrace tailWord_3224652 prefixEnd_3224652 1103864279654815178613401 := by
  unfold tailWord_3224652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58806360356822002780558105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78408480475762670374077473 58806360356822002780558105)
  ·
    refine ⟨44104770267616502085418579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58806360356822002780558105 44104770267616502085418579)
    ·
      refine ⟨66157155401424753128127869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44104770267616502085418579 66157155401424753128127869)
      ·
        refine ⟨24808933275534282423047951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66157155401424753128127869 24808933275534282423047951)
        ·
          refine ⟨37213399913301423634571927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24808933275534282423047951 37213399913301423634571927)
          ·
            refine ⟨55820099869952135451857891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37213399913301423634571927 55820099869952135451857891)
            ·
              refine ⟨83730149804928203177786837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55820099869952135451857891 83730149804928203177786837)
              ·
                refine ⟨1962425386053004761979379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83730149804928203177786837 1962425386053004761979379)
                ·
                  refine ⟨2943638079079507142969069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962425386053004761979379 2943638079079507142969069)
                  ·
                    refine ⟨1103864279654815178613401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943638079079507142969069 1103864279654815178613401)
                    ·
                      rfl

theorem cell22_3224652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_3224652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224652 prefixEnd_3224652 := by exact prefixLift 3224652
  have htrace : WordTrace (prefixWord ++ tailWord_3224652) baseStart_3224652 baseEnd_3224652 := by
    simpa [prefixWord, tailWord_3224652, baseEnd_3224652] using wordTrace_append hprefix tailTrace_3224652
  have hstable : (prefixWord ++ tailWord_3224652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224652).length < 2 ^ (prefixWord ++ tailWord_3224652).sum := by decide
  have hdescent : baseEnd_3224652 < baseStart_3224652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224663 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3224663 : Nat := 118140960795 + 3224663 * 2 ^ 59
def prefixEnd_3224663 : Nat := 4983230072969 + 3 ^ 40 * 3224663 * 2
def baseEnd_3224663 : Nat := 1103868045179614816588367

theorem tailTrace_3224663 : CollatzResearch.WordTrace tailWord_3224663 prefixEnd_3224663 1103868045179614816588367 := by
  unfold tailWord_3224663
  simp only [CollatzResearch.WordTrace]
  refine ⟨117613121916604154439766643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78408747944402769626511095 117613121916604154439766643)
  ·
    refine ⟨176419682874906231659649965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117613121916604154439766643 176419682874906231659649965)
    ·
      refine ⟨66157381078089836872368737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176419682874906231659649965 66157381078089836872368737)
      ·
        refine ⟨49618035808567377654276553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66157381078089836872368737 49618035808567377654276553)
        ·
          refine ⟨37213526856425533240707415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49618035808567377654276553 37213526856425533240707415)
          ·
            refine ⟨55820290284638299861061123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37213526856425533240707415 55820290284638299861061123)
            ·
              refine ⟨83730435426957449791591685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55820290284638299861061123 83730435426957449791591685)
              ·
                refine ⟨15699456642554521835923441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83730435426957449791591685 15699456642554521835923441)
                ·
                  refine ⟨11774592481915891376942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15699456642554521835923441 11774592481915891376942581)
                  ·
                    refine ⟨1103868045179614816588367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11774592481915891376942581 1103868045179614816588367)
                    ·
                      rfl

theorem cell22_3224663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3224663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224663 prefixEnd_3224663 := by exact prefixLift 3224663
  have htrace : WordTrace (prefixWord ++ tailWord_3224663) baseStart_3224663 baseEnd_3224663 := by
    simpa [prefixWord, tailWord_3224663, baseEnd_3224663] using wordTrace_append hprefix tailTrace_3224663
  have hstable : (prefixWord ++ tailWord_3224663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224663).length < 2 ^ (prefixWord ++ tailWord_3224663).sum := by decide
  have hdescent : baseEnd_3224663 < baseStart_3224663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224695 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3224695 : Nat := 118140960795 + 3224695 * 2 ^ 59
def prefixEnd_3224695 : Nat := 4983230072969 + 3 ^ 40 * 3224695 * 2
def baseEnd_3224695 : Nat := 1103878999433577399788269

theorem tailTrace_3224695 : CollatzResearch.WordTrace tailWord_3224695 prefixEnd_3224695 1103878999433577399788269 := by
  unfold tailWord_3224695
  simp only [CollatzResearch.WordTrace]
  refine ⟨117614289052488223904931539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78409526034992149269954359 117614289052488223904931539)
  ·
    refine ⟨176421433578732335857397309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117614289052488223904931539 176421433578732335857397309)
    ·
      refine ⟨66158037592024625946523991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176421433578732335857397309 66158037592024625946523991)
      ·
        refine ⟨99237056388036938919785987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66158037592024625946523991 99237056388036938919785987)
        ·
          refine ⟨148855584582055408379678981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99237056388036938919785987 148855584582055408379678981)
          ·
            refine ⟨27910422109135389071189809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148855584582055408379678981 27910422109135389071189809)
            ·
              refine ⟨20932816581851541803392357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27910422109135389071189809 20932816581851541803392357)
              ·
                refine ⟨3924903109097164088136067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20932816581851541803392357 3924903109097164088136067)
                ·
                  refine ⟨5887354663645746132204101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924903109097164088136067 5887354663645746132204101)
                  ·
                    refine ⟨1103878999433577399788269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887354663645746132204101 1103878999433577399788269)
                    ·
                      rfl

theorem cell22_3224695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3224695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224695 prefixEnd_3224695 := by exact prefixLift 3224695
  have htrace : WordTrace (prefixWord ++ tailWord_3224695) baseStart_3224695 baseEnd_3224695 := by
    simpa [prefixWord, tailWord_3224695, baseEnd_3224695] using wordTrace_append hprefix tailTrace_3224695
  have hstable : (prefixWord ++ tailWord_3224695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224695).length < 2 ^ (prefixWord ++ tailWord_3224695).sum := by decide
  have hdescent : baseEnd_3224695 < baseStart_3224695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224727 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 4]
def baseStart_3224727 : Nat := 118140960795 + 3224727 * 2 ^ 59
def prefixEnd_3224727 : Nat := 4983230072969 + 3 ^ 40 * 3224727 * 2
def baseEnd_3224727 : Nat := 367963317895846660996057

theorem tailTrace_3224727 : CollatzResearch.WordTrace tailWord_3224727 prefixEnd_3224727 367963317895846660996057 := by
  unfold tailWord_3224727
  simp only [CollatzResearch.WordTrace]
  refine ⟨117615456188372293370096435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78410304125581528913397623 117615456188372293370096435)
  ·
    refine ⟨176423184282558440055144653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117615456188372293370096435 176423184282558440055144653)
    ·
      refine ⟨66158694105959415020679245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176423184282558440055144653 66158694105959415020679245)
      ·
        refine ⟨24809510289734780632754717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66158694105959415020679245 24809510289734780632754717)
        ·
          refine ⟨9303566358650542737283019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24809510289734780632754717 9303566358650542737283019)
          ·
            refine ⟨13955349537975814105924529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303566358650542737283019 13955349537975814105924529)
            ·
              refine ⟨10466512153481860579443397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13955349537975814105924529 10466512153481860579443397)
              ·
                refine ⟨1962471028777848858645637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10466512153481860579443397 1962471028777848858645637)
                ·
                  refine ⟨367963317895846660996057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962471028777848858645637 367963317895846660996057)
                  ·
                    rfl

theorem cell22_3224727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 4].length) (baseStart_3224727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224727 prefixEnd_3224727 := by exact prefixLift 3224727
  have htrace : WordTrace (prefixWord ++ tailWord_3224727) baseStart_3224727 baseEnd_3224727 := by
    simpa [prefixWord, tailWord_3224727, baseEnd_3224727] using wordTrace_append hprefix tailTrace_3224727
  have hstable : (prefixWord ++ tailWord_3224727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224727).length < 2 ^ (prefixWord ++ tailWord_3224727).sum := by decide
  have hdescent : baseEnd_3224727 < baseStart_3224727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224740 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3224740 : Nat := 118140960795 + 3224740 * 2 ^ 59
def prefixEnd_3224740 : Nat := 4983230072969 + 3 ^ 40 * 3224740 * 2
def baseEnd_3224740 : Nat := 1103894403853212282413131

theorem tailTrace_3224740 : CollatzResearch.WordTrace tailWord_3224740 prefixEnd_3224740 1103894403853212282413131 := by
  unfold tailWord_3224740
  simp only [CollatzResearch.WordTrace]
  refine ⟨58807965168662598295159837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78410620224883464393546449 58807965168662598295159837)
  ·
    refine ⟨22052986938248474360684939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58807965168662598295159837 22052986938248474360684939)
    ·
      refine ⟨33079480407372711541027409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22052986938248474360684939 33079480407372711541027409)
      ·
        refine ⟨24809610305529533655770557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33079480407372711541027409 24809610305529533655770557)
        ·
          refine ⟨9303603864573575120913959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24809610305529533655770557 9303603864573575120913959)
          ·
            refine ⟨13955405796860362681370939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303603864573575120913959 13955405796860362681370939)
            ·
              refine ⟨20933108695290544022056409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955405796860362681370939 20933108695290544022056409)
              ·
                refine ⟨15699831521467908016542307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20933108695290544022056409 15699831521467908016542307)
                ·
                  refine ⟨23549747282201862024813461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15699831521467908016542307 23549747282201862024813461)
                  ·
                    refine ⟨1103894403853212282413131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23549747282201862024813461 1103894403853212282413131)
                    ·
                      rfl

theorem cell22_3224740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3224740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224740 prefixEnd_3224740 := by exact prefixLift 3224740
  have htrace : WordTrace (prefixWord ++ tailWord_3224740) baseStart_3224740 baseEnd_3224740 := by
    simpa [prefixWord, tailWord_3224740, baseEnd_3224740] using wordTrace_append hprefix tailTrace_3224740
  have hstable : (prefixWord ++ tailWord_3224740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224740).length < 2 ^ (prefixWord ++ tailWord_3224740).sum := by decide
  have hdescent : baseEnd_3224740 < baseStart_3224740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224755 : List Nat := [1, 1, 1, 2, 3, 2, 6, 6]
def baseStart_3224755 : Nat := 118140960795 + 3224755 * 2 ^ 59
def prefixEnd_3224755 : Nat := 4983230072969 + 3 ^ 40 * 3224755 * 2
def baseEnd_3224755 : Nat := 122655504295528582587565

theorem tailTrace_3224755 : CollatzResearch.WordTrace tailWord_3224755 prefixEnd_3224755 122655504295528582587565 := by
  unfold tailWord_3224755
  simp only [CollatzResearch.WordTrace]
  refine ⟨117616477432270854152115719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78410984954847236101410479 117616477432270854152115719)
  ·
    refine ⟨176424716148406281228173579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117616477432270854152115719 176424716148406281228173579)
    ·
      refine ⟨264637074222609421842260369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176424716148406281228173579 264637074222609421842260369)
      ·
        refine ⟨198477805666957066381695277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264637074222609421842260369 198477805666957066381695277)
        ·
          refine ⟨74429177125108899893135729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198477805666957066381695277 74429177125108899893135729)
          ·
            refine ⟨55821882843831674919851797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74429177125108899893135729 55821882843831674919851797)
            ·
              refine ⟨2616650758304609761868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55821882843831674919851797 2616650758304609761868053)
              ·
                refine ⟨122655504295528582587565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2616650758304609761868053 122655504295528582587565)
                ·
                  rfl

theorem cell22_3224755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 6].length) (baseStart_3224755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224755 prefixEnd_3224755 := by exact prefixLift 3224755
  have htrace : WordTrace (prefixWord ++ tailWord_3224755) baseStart_3224755 baseEnd_3224755 := by
    simpa [prefixWord, tailWord_3224755, baseEnd_3224755] using wordTrace_append hprefix tailTrace_3224755
  have hstable : (prefixWord ++ tailWord_3224755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224755).length < 2 ^ (prefixWord ++ tailWord_3224755).sum := by decide
  have hdescent : baseEnd_3224755 < baseStart_3224755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224772 : List Nat := [2, 3, 3, 1, 3, 2, 8]
def baseStart_3224772 : Nat := 118140960795 + 3224772 * 2 ^ 59
def prefixEnd_3224772 : Nat := 4983230072969 + 3 ^ 40 * 3224772 * 2
def baseEnd_3224772 : Nat := 40885383633599069096779

theorem tailTrace_3224772 : CollatzResearch.WordTrace tailWord_3224772 prefixEnd_3224772 40885383633599069096779 := by
  unfold tailWord_3224772
  simp only [CollatzResearch.WordTrace]
  refine ⟨58808548736604633027742285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78411398315472844036989713 58808548736604633027742285)
  ·
    refine ⟨22053205776226737385403357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58808548736604633027742285 22053205776226737385403357)
    ·
      refine ⟨8269952166085026519526259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22053205776226737385403357 8269952166085026519526259)
      ·
        refine ⟨12404928249127539779289389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8269952166085026519526259 12404928249127539779289389)
        ·
          refine ⟨4651848093422827417233521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12404928249127539779289389 4651848093422827417233521)
          ·
            refine ⟨3488886070067120562925141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651848093422827417233521 3488886070067120562925141)
            ·
              refine ⟨40885383633599069096779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3488886070067120562925141 40885383633599069096779)
              ·
                rfl

theorem cell22_3224772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 8].length) (baseStart_3224772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224772 prefixEnd_3224772 := by exact prefixLift 3224772
  have htrace : WordTrace (prefixWord ++ tailWord_3224772) baseStart_3224772 baseEnd_3224772 := by
    simpa [prefixWord, tailWord_3224772, baseEnd_3224772] using wordTrace_append hprefix tailTrace_3224772
  have hstable : (prefixWord ++ tailWord_3224772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224772).length < 2 ^ (prefixWord ++ tailWord_3224772).sum := by decide
  have hdescent : baseEnd_3224772 < baseStart_3224772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224875 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_3224875 : Nat := 118140960795 + 3224875 * 2 ^ 59
def prefixEnd_3224875 : Nat := 4983230072969 + 3 ^ 40 * 3224875 * 2
def baseEnd_3224875 : Nat := 1103940617112116930287717

theorem tailTrace_3224875 : CollatzResearch.WordTrace tailWord_3224875 prefixEnd_3224875 1103940617112116930287717 := by
  unfold tailWord_3224875
  simp only [CollatzResearch.WordTrace]
  refine ⟨117620854191836114646484079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78413902794557409764322719 117620854191836114646484079)
  ·
    refine ⟨176431281287754171969726119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117620854191836114646484079 176431281287754171969726119)
    ·
      refine ⟨264646921931631257954589179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176431281287754171969726119 264646921931631257954589179)
      ·
        refine ⟨396970382897446886931883769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264646921931631257954589179 396970382897446886931883769)
        ·
          refine ⟨297727787173085165198912827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396970382897446886931883769 297727787173085165198912827)
          ·
            refine ⟨446591680759627747798369241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297727787173085165198912827 446591680759627747798369241)
            ·
              refine ⟨334943760569720810848776931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446591680759627747798369241 334943760569720810848776931)
              ·
                refine ⟨502415640854581216273165397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334943760569720810848776931 502415640854581216273165397)
                ·
                  refine ⟨5887683291264623628201157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 502415640854581216273165397 5887683291264623628201157)
                  ·
                    refine ⟨1103940617112116930287717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887683291264623628201157 1103940617112116930287717)
                    ·
                      rfl

theorem cell22_3224875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_3224875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224875 prefixEnd_3224875 := by exact prefixLift 3224875
  have htrace : WordTrace (prefixWord ++ tailWord_3224875) baseStart_3224875 baseEnd_3224875 := by
    simpa [prefixWord, tailWord_3224875, baseEnd_3224875] using wordTrace_append hprefix tailTrace_3224875
  have hstable : (prefixWord ++ tailWord_3224875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224875).length < 2 ^ (prefixWord ++ tailWord_3224875).sum := by decide
  have hdescent : baseEnd_3224875 < baseStart_3224875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224881 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_3224881 : Nat := 118140960795 + 3224881 * 2 ^ 59
def prefixEnd_3224881 : Nat := 4983230072969 + 3 ^ 40 * 3224881 * 2
def baseEnd_3224881 : Nat := 1103942671034734914637699

theorem tailTrace_3224881 : CollatzResearch.WordTrace tailWord_3224881 prefixEnd_3224881 1103942671034734914637699 := by
  unfold tailWord_3224881
  simp only [CollatzResearch.WordTrace]
  refine ⟨117621073029814377671202497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78414048686542918447468331 117621073029814377671202497)
  ·
    refine ⟨88215804772360783253401873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117621073029814377671202497 88215804772360783253401873)
    ·
      refine ⟨66161853579270587440051405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88215804772360783253401873 66161853579270587440051405)
      ·
        refine ⟨24810695092226470290019277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66161853579270587440051405 24810695092226470290019277)
        ·
          refine ⟨9304010659584926358757229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24810695092226470290019277 9304010659584926358757229)
          ·
            refine ⟨3489003997344347384533961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9304010659584926358757229 3489003997344347384533961)
            ·
              refine ⟨2616752998008260538400471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3489003997344347384533961 2616752998008260538400471)
              ·
                refine ⟨3925129497012390807600707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616752998008260538400471 3925129497012390807600707)
                ·
                  refine ⟨5887694245518586211401061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925129497012390807600707 5887694245518586211401061)
                  ·
                    refine ⟨1103942671034734914637699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887694245518586211401061 1103942671034734914637699)
                    ·
                      rfl

theorem cell22_3224881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_3224881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224881 prefixEnd_3224881 := by exact prefixLift 3224881
  have htrace : WordTrace (prefixWord ++ tailWord_3224881) baseStart_3224881 baseEnd_3224881 := by
    simpa [prefixWord, tailWord_3224881, baseEnd_3224881] using wordTrace_append hprefix tailTrace_3224881
  have hstable : (prefixWord ++ tailWord_3224881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224881).length < 2 ^ (prefixWord ++ tailWord_3224881).sum := by decide
  have hdescent : baseEnd_3224881 < baseStart_3224881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224890 : List Nat := [3, 1, 1, 1, 4, 1, 11]
def baseStart_3224890 : Nat := 118140960795 + 3224890 * 2 ^ 59
def prefixEnd_3224890 : Nat := 4983230072969 + 3 ^ 40 * 3224890 * 2
def baseEnd_3224890 : Nat := 40886879700691181154173

theorem tailTrace_3224890 : CollatzResearch.WordTrace tailWord_3224890 prefixEnd_3224890 40886879700691181154173 := by
  unfold tailWord_3224890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405350321695443052070031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78414267524521181472186749 29405350321695443052070031)
  ·
    refine ⟨44108025482543164578105047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29405350321695443052070031 44108025482543164578105047)
    ·
      refine ⟨66162038223814746867157571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44108025482543164578105047 66162038223814746867157571)
      ·
        refine ⟨99243057335722120300736357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66162038223814746867157571 99243057335722120300736357)
        ·
          refine ⟨18608073250447897556388067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99243057335722120300736357 18608073250447897556388067)
          ·
            refine ⟨27912109875671846334582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18608073250447897556388067 27912109875671846334582101)
            ·
              refine ⟨40886879700691181154173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27912109875671846334582101 40886879700691181154173)
              ·
                rfl

theorem cell22_3224890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 11].length) (baseStart_3224890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224890 prefixEnd_3224890 := by exact prefixLift 3224890
  have htrace : WordTrace (prefixWord ++ tailWord_3224890) baseStart_3224890 baseEnd_3224890 := by
    simpa [prefixWord, tailWord_3224890, baseEnd_3224890] using wordTrace_append hprefix tailTrace_3224890
  have hstable : (prefixWord ++ tailWord_3224890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224890).length < 2 ^ (prefixWord ++ tailWord_3224890).sum := by decide
  have hdescent : baseEnd_3224890 < baseStart_3224890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224894 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3224894 : Nat := 118140960795 + 3224894 * 2 ^ 59
def prefixEnd_3224894 : Nat := 4983230072969 + 3 ^ 40 * 3224894 * 2
def baseEnd_3224894 : Nat := 1103947121200407214062659

theorem tailTrace_3224894 : CollatzResearch.WordTrace tailWord_3224894 prefixEnd_3224894 1103947121200407214062659 := by
  unfold tailWord_3224894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702693397345910111428217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78414364785844853927617157 14702693397345910111428217)
  ·
    refine ⟨11027020048009432583571163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14702693397345910111428217 11027020048009432583571163)
    ·
      refine ⟨16540530072014148875356745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027020048009432583571163 16540530072014148875356745)
      ·
        refine ⟨12405397554010611656517559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16540530072014148875356745 12405397554010611656517559)
        ·
          refine ⟨18608096331015917484776339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12405397554010611656517559 18608096331015917484776339)
          ·
            refine ⟨27912144496523876227164509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18608096331015917484776339 27912144496523876227164509)
            ·
              refine ⟨10467054186196453585186691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27912144496523876227164509 10467054186196453585186691)
              ·
                refine ⟨15700581279294680377780037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467054186196453585186691 15700581279294680377780037)
                ·
                  refine ⟨2943858989867752570833757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15700581279294680377780037 2943858989867752570833757)
                  ·
                    refine ⟨1103947121200407214062659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943858989867752570833757 1103947121200407214062659)
                    ·
                      rfl

theorem cell22_3224894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3224894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224894 prefixEnd_3224894 := by exact prefixLift 3224894
  have htrace : WordTrace (prefixWord ++ tailWord_3224894) baseStart_3224894 baseEnd_3224894 := by
    simpa [prefixWord, tailWord_3224894, baseEnd_3224894] using wordTrace_append hprefix tailTrace_3224894
  have hstable : (prefixWord ++ tailWord_3224894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224894).length < 2 ^ (prefixWord ++ tailWord_3224894).sum := by decide
  have hdescent : baseEnd_3224894 < baseStart_3224894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224969 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 5]
def baseStart_3224969 : Nat := 118140960795 + 3224969 * 2 ^ 59
def prefixEnd_3224969 : Nat := 4983230072969 + 3 ^ 40 * 3224969 * 2
def baseEnd_3224969 : Nat := 367990931744377339479143

theorem tailTrace_3224969 : CollatzResearch.WordTrace tailWord_3224969 prefixEnd_3224969 367990931744377339479143 := by
  unfold tailWord_3224969
  simp only [CollatzResearch.WordTrace]
  refine ⟨117624282653495568700405961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78416188435663712466937307 117624282653495568700405961)
  ·
    refine ⟨88218211990121676525304471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117624282653495568700405961 88218211990121676525304471)
    ·
      refine ⟨132327317985182514787956707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88218211990121676525304471 132327317985182514787956707)
      ·
        refine ⟨198490976977773772181935061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132327317985182514787956707 198490976977773772181935061)
        ·
          refine ⟨4652132272916572785514103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 198490976977773772181935061 4652132272916572785514103)
          ·
            refine ⟨6978198409374859178271155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652132272916572785514103 6978198409374859178271155)
            ·
              refine ⟨10467297614062288767406733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978198409374859178271155 10467297614062288767406733)
              ·
                refine ⟨3925236605273358287777525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10467297614062288767406733 3925236605273358287777525)
                ·
                  refine ⟨367990931744377339479143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3925236605273358287777525 367990931744377339479143)
                  ·
                    rfl

theorem cell22_3224969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_3224969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3224969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3224969 prefixEnd_3224969 := by exact prefixLift 3224969
  have htrace : WordTrace (prefixWord ++ tailWord_3224969) baseStart_3224969 baseEnd_3224969 := by
    simpa [prefixWord, tailWord_3224969, baseEnd_3224969] using wordTrace_append hprefix tailTrace_3224969
  have hstable : (prefixWord ++ tailWord_3224969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224969).length < 2 ^ (prefixWord ++ tailWord_3224969).sum := by decide
  have hdescent : baseEnd_3224969 < baseStart_3224969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225027 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_3225027 : Nat := 118140960795 + 3225027 * 2 ^ 59
def prefixEnd_3225027 : Nat := 4983230072969 + 3 ^ 40 * 3225027 * 2
def baseEnd_3225027 : Nat := 1103992649818439200487251

theorem tailTrace_3225027 : CollatzResearch.WordTrace tailWord_3225027 prefixEnd_3225027 1103992649818439200487251 := by
  unfold tailWord_3225027
  simp only [CollatzResearch.WordTrace]
  refine ⟨117626398087285444606017335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78417598724856963070678223 117626398087285444606017335)
  ·
    refine ⟨176439597130928166909026003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117626398087285444606017335 176439597130928166909026003)
    ·
      refine ⟨264659395696392250363539005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176439597130928166909026003 264659395696392250363539005)
      ·
        refine ⟨99247273386147093886327127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264659395696392250363539005 99247273386147093886327127)
        ·
          refine ⟨148870910079220640829490691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99247273386147093886327127 148870910079220640829490691)
          ·
            refine ⟨223306365118830961244236037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148870910079220640829490691 223306365118830961244236037)
            ·
              refine ⟨41869943459780805233294257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223306365118830961244236037 41869943459780805233294257)
              ·
                refine ⟨31402457594835603924970693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41869943459780805233294257 31402457594835603924970693)
                ·
                  refine ⟨5887960799031675735932005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31402457594835603924970693 5887960799031675735932005)
                  ·
                    refine ⟨1103992649818439200487251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887960799031675735932005 1103992649818439200487251)
                    ·
                      rfl

theorem cell22_3225027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_3225027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225027 prefixEnd_3225027 := by exact prefixLift 3225027
  have htrace : WordTrace (prefixWord ++ tailWord_3225027) baseStart_3225027 baseEnd_3225027 := by
    simpa [prefixWord, tailWord_3225027, baseEnd_3225027] using wordTrace_append hprefix tailTrace_3225027
  have hstable : (prefixWord ++ tailWord_3225027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225027).length < 2 ^ (prefixWord ++ tailWord_3225027).sum := by decide
  have hdescent : baseEnd_3225027 < baseStart_3225027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225046 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3225046 : Nat := 118140960795 + 3225046 * 2 ^ 59
def prefixEnd_3225046 : Nat := 4983230072969 + 3 ^ 40 * 3225046 * 2
def baseEnd_3225046 : Nat := 1103999153906729484262193

theorem tailTrace_3225046 : CollatzResearch.WordTrace tailWord_3225046 prefixEnd_3225046 1103999153906729484262193 := by
  unfold tailWord_3225046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351693192138538178184937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78418060716144407233972661 7351693192138538178184937)
  ·
    refine ⟨5513769894103903633638703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7351693192138538178184937 5513769894103903633638703)
    ·
      refine ⟨8270654841155855450458055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5513769894103903633638703 8270654841155855450458055)
      ·
        refine ⟨12405982261733783175687083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270654841155855450458055 12405982261733783175687083)
        ·
          refine ⟨18608973392600674763530625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12405982261733783175687083 18608973392600674763530625)
          ·
            refine ⟨13956730044450506072647969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18608973392600674763530625 13956730044450506072647969)
            ·
              refine ⟨10467547533337879554485977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13956730044450506072647969 10467547533337879554485977)
              ·
                refine ⟨7850660650003409665864483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467547533337879554485977 7850660650003409665864483)
                ·
                  refine ⟨11775990975005114498796725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850660650003409665864483 11775990975005114498796725)
                  ·
                    refine ⟨1103999153906729484262193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11775990975005114498796725 1103999153906729484262193)
                    ·
                      rfl

theorem cell22_3225046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3225046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225046 prefixEnd_3225046 := by exact prefixLift 3225046
  have htrace : WordTrace (prefixWord ++ tailWord_3225046) baseStart_3225046 baseEnd_3225046 := by
    simpa [prefixWord, tailWord_3225046, baseEnd_3225046] using wordTrace_append hprefix tailTrace_3225046
  have hstable : (prefixWord ++ tailWord_3225046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225046).length < 2 ^ (prefixWord ++ tailWord_3225046).sum := by decide
  have hdescent : baseEnd_3225046 < baseStart_3225046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225063 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3225063 : Nat := 118140960795 + 3225063 * 2 ^ 59
def prefixEnd_3225063 : Nat := 4983230072969 + 3 ^ 40 * 3225063 * 2
def baseEnd_3225063 : Nat := 1104004973354147106587141

theorem tailTrace_3225063 : CollatzResearch.WordTrace tailWord_3225063 prefixEnd_3225063 1104004973354147106587141 := by
  unfold tailWord_3225063
  simp only [CollatzResearch.WordTrace]
  refine ⟨117627711115155022754327843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78418474076770015169551895 117627711115155022754327843)
  ·
    refine ⟨176441566672732534131491765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117627711115155022754327843 176441566672732534131491765)
    ·
      refine ⟨16541396875568675074827353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176441566672732534131491765 16541396875568675074827353)
      ·
        refine ⟨12406047656676506306120515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541396875568675074827353 12406047656676506306120515)
        ·
          refine ⟨18609071485014759459180773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406047656676506306120515 18609071485014759459180773)
          ·
            refine ⟨3489200903440267398596395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18609071485014759459180773 3489200903440267398596395)
            ·
              refine ⟨5233801355160401097894593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489200903440267398596395 5233801355160401097894593)
              ·
                refine ⟨3925351016370300823420945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233801355160401097894593 3925351016370300823420945)
                ·
                  refine ⟨2944013262277725617565709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925351016370300823420945 2944013262277725617565709)
                  ·
                    refine ⟨1104004973354147106587141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944013262277725617565709 1104004973354147106587141)
                    ·
                      rfl

theorem cell22_3225063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3225063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225063 prefixEnd_3225063 := by exact prefixLift 3225063
  have htrace : WordTrace (prefixWord ++ tailWord_3225063) baseStart_3225063 baseEnd_3225063 := by
    simpa [prefixWord, tailWord_3225063, baseEnd_3225063] using wordTrace_append hprefix tailTrace_3225063
  have hstable : (prefixWord ++ tailWord_3225063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225063).length < 2 ^ (prefixWord ++ tailWord_3225063).sum := by decide
  have hdescent : baseEnd_3225063 < baseStart_3225063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225147 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_3225147 : Nat := 118140960795 + 3225147 * 2 ^ 59
def prefixEnd_3225147 : Nat := 4983230072969 + 3 ^ 40 * 3225147 * 2
def baseEnd_3225147 : Nat := 1104033728270798887486883

theorem tailTrace_3225147 : CollatzResearch.WordTrace tailWord_3225147 prefixEnd_3225147 1104033728270798887486883 := by
  unfold tailWord_3225147
  simp only [CollatzResearch.WordTrace]
  refine ⟨117630774846850705100385695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78420516564567136733590463 117630774846850705100385695)
  ·
    refine ⟨176446162270276057650578543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117630774846850705100385695 176446162270276057650578543)
    ·
      refine ⟨264669243405414086475867815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176446162270276057650578543 264669243405414086475867815)
      ·
        refine ⟨397003865108121129713801723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264669243405414086475867815 397003865108121129713801723)
        ·
          refine ⟨595505797662181694570702585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397003865108121129713801723 595505797662181694570702585)
          ·
            refine ⟨446629348246636270928026939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595505797662181694570702585 446629348246636270928026939)
            ·
              refine ⟨669944022369954406392040409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446629348246636270928026939 669944022369954406392040409)
              ·
                refine ⟨502458016777465804794030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669944022369954406392040409 502458016777465804794030307)
                ·
                  refine ⟨753687025166198707191045461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502458016777465804794030307 753687025166198707191045461)
                  ·
                    refine ⟨1104033728270798887486883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 753687025166198707191045461 1104033728270798887486883)
                    ·
                      rfl

theorem cell22_3225147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_3225147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225147 prefixEnd_3225147 := by exact prefixLift 3225147
  have htrace : WordTrace (prefixWord ++ tailWord_3225147) baseStart_3225147 baseEnd_3225147 := by
    simpa [prefixWord, tailWord_3225147, baseEnd_3225147] using wordTrace_append hprefix tailTrace_3225147
  have hstable : (prefixWord ++ tailWord_3225147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225147).length < 2 ^ (prefixWord ++ tailWord_3225147).sum := by decide
  have hdescent : baseEnd_3225147 < baseStart_3225147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225151 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 1, 4]
def baseStart_3225151 : Nat := 118140960795 + 3225151 * 2 ^ 59
def prefixEnd_3225151 : Nat := 4983230072969 + 3 ^ 40 * 3225151 * 2
def baseEnd_3225151 : Nat := 1104035097552544210386871

theorem tailTrace_3225151 : CollatzResearch.WordTrace tailWord_3225151 prefixEnd_3225151 1104035097552544210386871 := by
  unfold tailWord_3225151
  simp only [CollatzResearch.WordTrace]
  refine ⟨117630920738836213783531307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78420613825890809189020871 117630920738836213783531307)
  ·
    refine ⟨176446381108254320675296961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117630920738836213783531307 176446381108254320675296961)
    ·
      refine ⟨132334785831190740506472721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176446381108254320675296961 132334785831190740506472721)
      ·
        refine ⟨99251089373393055379854541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132334785831190740506472721 99251089373393055379854541)
        ·
          refine ⟨37219158515022395767445453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99251089373393055379854541 37219158515022395767445453)
          ·
            refine ⟨13957184443133398412792045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37219158515022395767445453 13957184443133398412792045)
            ·
              refine ⟨5233944166175024404797017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13957184443133398412792045 5233944166175024404797017)
              ·
                refine ⟨3925458124631268303597763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233944166175024404797017 3925458124631268303597763)
                ·
                  refine ⟨5888187186946902455396645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925458124631268303597763 5888187186946902455396645)
                  ·
                    refine ⟨1104035097552544210386871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888187186946902455396645 1104035097552544210386871)
                    ·
                      rfl

theorem cell22_3225151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_3225151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225151 prefixEnd_3225151 := by exact prefixLift 3225151
  have htrace : WordTrace (prefixWord ++ tailWord_3225151) baseStart_3225151 baseEnd_3225151 := by
    simpa [prefixWord, tailWord_3225151, baseEnd_3225151] using wordTrace_append hprefix tailTrace_3225151
  have hstable : (prefixWord ++ tailWord_3225151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225151).length < 2 ^ (prefixWord ++ tailWord_3225151).sum := by decide
  have hdescent : baseEnd_3225151 < baseStart_3225151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225164 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_3225164 : Nat := 118140960795 + 3225164 * 2 ^ 59
def prefixEnd_3225164 : Nat := 4983230072969 + 3 ^ 40 * 3225164 * 2
def baseEnd_3225164 : Nat := 1104039547718216509811831

theorem tailTrace_3225164 : CollatzResearch.WordTrace tailWord_3225164 prefixEnd_3225164 1104039547718216509811831 := by
  unfold tailWord_3225164
  simp only [CollatzResearch.WordTrace]
  refine ⟨58815697443894558501877273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78420929925192744669169697 58815697443894558501877273)
  ·
    refine ⟨44111773082920918876407955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58815697443894558501877273 44111773082920918876407955)
    ·
      refine ⟨66167659624381378314611933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44111773082920918876407955 66167659624381378314611933)
      ·
        refine ⟨24812872359143016867979475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66167659624381378314611933 24812872359143016867979475)
        ·
          refine ⟨37219308538714525301969213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24812872359143016867979475 37219308538714525301969213)
          ·
            refine ⟨13957240702017946988238455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37219308538714525301969213 13957240702017946988238455)
            ·
              refine ⟨20935861053026920482357683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957240702017946988238455 20935861053026920482357683)
              ·
                refine ⟨31403791579540380723536525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20935861053026920482357683 31403791579540380723536525)
                ·
                  refine ⟨11776421842327642771326197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31403791579540380723536525 11776421842327642771326197)
                  ·
                    refine ⟨1104039547718216509811831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11776421842327642771326197 1104039547718216509811831)
                    ·
                      rfl

theorem cell22_3225164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_3225164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225164 prefixEnd_3225164 := by exact prefixLift 3225164
  have htrace : WordTrace (prefixWord ++ tailWord_3225164) baseStart_3225164 baseEnd_3225164 := by
    simpa [prefixWord, tailWord_3225164, baseEnd_3225164] using wordTrace_append hprefix tailTrace_3225164
  have hstable : (prefixWord ++ tailWord_3225164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225164).length < 2 ^ (prefixWord ++ tailWord_3225164).sum := by decide
  have hdescent : baseEnd_3225164 < baseStart_3225164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225166 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3225166 : Nat := 118140960795 + 3225166 * 2 ^ 59
def prefixEnd_3225166 : Nat := 4983230072969 + 3 ^ 40 * 3225166 * 2
def baseEnd_3225166 : Nat := 368013410786363057087275

theorem tailTrace_3225166 : CollatzResearch.WordTrace tailWord_3225166 prefixEnd_3225166 368013410786363057087275 := by
  unfold tailWord_3225166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703933479222733918165919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78420978555854580896884901 14703933479222733918165919)
  ·
    refine ⟨22055900218834100877248879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14703933479222733918165919 22055900218834100877248879)
    ·
      refine ⟨33083850328251151315873319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22055900218834100877248879 33083850328251151315873319)
      ·
        refine ⟨49625775492376726973809979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33083850328251151315873319 49625775492376726973809979)
        ·
          refine ⟨74438663238565090460714969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49625775492376726973809979 74438663238565090460714969)
          ·
            refine ⟨55828997428923817845536227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74438663238565090460714969 55828997428923817845536227)
            ·
              refine ⟨83743496143385726768304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55828997428923817845536227 83743496143385726768304341)
              ·
                refine ⟨1962738190860602971132133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83743496143385726768304341 1962738190860602971132133)
                ·
                  refine ⟨368013410786363057087275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962738190860602971132133 368013410786363057087275)
                  ·
                    rfl

theorem cell22_3225166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3225166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225166 prefixEnd_3225166 := by exact prefixLift 3225166
  have htrace : WordTrace (prefixWord ++ tailWord_3225166) baseStart_3225166 baseEnd_3225166 := by
    simpa [prefixWord, tailWord_3225166, baseEnd_3225166] using wordTrace_append hprefix tailTrace_3225166
  have hstable : (prefixWord ++ tailWord_3225166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225166).length < 2 ^ (prefixWord ++ tailWord_3225166).sum := by decide
  have hdescent : baseEnd_3225166 < baseStart_3225166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225198 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3225198 : Nat := 118140960795 + 3225198 * 2 ^ 59
def prefixEnd_3225198 : Nat := 4983230072969 + 3 ^ 40 * 3225198 * 2
def baseEnd_3225198 : Nat := 1104051186613051754461727

theorem tailTrace_3225198 : CollatzResearch.WordTrace tailWord_3225198 prefixEnd_3225198 1104051186613051754461727 := by
  unfold tailWord_3225198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704079371208242601311531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78421756646443960540328165 14704079371208242601311531)
  ·
    refine ⟨22056119056812363901967297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14704079371208242601311531 22056119056812363901967297)
    ·
      refine ⟨16542089292609272926475473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22056119056812363901967297 16542089292609272926475473)
      ·
        refine ⟨12406566969456954694856605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16542089292609272926475473 12406566969456954694856605)
        ·
          refine ⟨4652462613546358010571227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12406566969456954694856605 4652462613546358010571227)
          ·
            refine ⟨6978693920319537015856841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652462613546358010571227 6978693920319537015856841)
            ·
              refine ⟨5234020440239652761892631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6978693920319537015856841 5234020440239652761892631)
              ·
                refine ⟨7851030660359479142838947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234020440239652761892631 7851030660359479142838947)
                ·
                  refine ⟨11776545990539218714258421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851030660359479142838947 11776545990539218714258421)
                  ·
                    refine ⟨1104051186613051754461727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11776545990539218714258421 1104051186613051754461727)
                    ·
                      rfl

theorem cell22_3225198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3225198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225198 prefixEnd_3225198 := by exact prefixLift 3225198
  have htrace : WordTrace (prefixWord ++ tailWord_3225198) baseStart_3225198 baseEnd_3225198 := by
    simpa [prefixWord, tailWord_3225198, baseEnd_3225198] using wordTrace_append hprefix tailTrace_3225198
  have hstable : (prefixWord ++ tailWord_3225198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225198).length < 2 ^ (prefixWord ++ tailWord_3225198).sum := by decide
  have hdescent : baseEnd_3225198 < baseStart_3225198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225213 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_3225213 : Nat := 118140960795 + 3225213 * 2 ^ 59
def prefixEnd_3225213 : Nat := 4983230072969 + 3 ^ 40 * 3225213 * 2
def baseEnd_3225213 : Nat := 1104056321419596715336681

theorem tailTrace_3225213 : CollatzResearch.WordTrace tailWord_3225213 prefixEnd_3225213 1104056321419596715336681 := by
  unfold tailWord_3225213
  simp only [CollatzResearch.WordTrace]
  refine ⟨117633182064611598372288293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78422121376407732248192195 117633182064611598372288293)
  ·
    refine ⟨22056221637114674694804055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117633182064611598372288293 22056221637114674694804055)
    ·
      refine ⟨33084332455672012042206083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22056221637114674694804055 33084332455672012042206083)
      ·
        refine ⟨49626498683508018063309125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33084332455672012042206083 49626498683508018063309125)
        ·
          refine ⟨9304968503157753386870461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49626498683508018063309125 9304968503157753386870461)
          ·
            refine ⟨3489363188684157520076423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9304968503157753386870461 3489363188684157520076423)
            ·
              refine ⟨5234044783026236280114635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489363188684157520076423 5234044783026236280114635)
              ·
                refine ⟨7851067174539354420171953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234044783026236280114635 7851067174539354420171953)
                ·
                  refine ⟨5888300380904515815128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851067174539354420171953 5888300380904515815128965)
                  ·
                    refine ⟨1104056321419596715336681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888300380904515815128965 1104056321419596715336681)
                    ·
                      rfl

theorem cell22_3225213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_3225213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225213 prefixEnd_3225213 := by exact prefixLift 3225213
  have htrace : WordTrace (prefixWord ++ tailWord_3225213) baseStart_3225213 baseEnd_3225213 := by
    simpa [prefixWord, tailWord_3225213, baseEnd_3225213] using wordTrace_append hprefix tailTrace_3225213
  have hstable : (prefixWord ++ tailWord_3225213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225213).length < 2 ^ (prefixWord ++ tailWord_3225213).sum := by decide
  have hdescent : baseEnd_3225213 < baseStart_3225213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225262 : List Nat := [4, 1, 4, 1, 3, 1, 2, 6]
def baseStart_3225262 : Nat := 118140960795 + 3225262 * 2 ^ 59
def prefixEnd_3225262 : Nat := 4983230072969 + 3 ^ 40 * 3225262 * 2
def baseEnd_3225262 : Nat := 122674788346775213429059

theorem tailTrace_3225262 : CollatzResearch.WordTrace tailWord_3225262 prefixEnd_3225262 122674788346775213429059 := by
  unfold tailWord_3225262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704371155179259967602755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78423312827622719827214693 14704371155179259967602755)
  ·
    refine ⟨22056556732768889951404133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14704371155179259967602755 22056556732768889951404133)
    ·
      refine ⟨4135604387394166865888275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22056556732768889951404133 4135604387394166865888275)
      ·
        refine ⟨6203406581091250298832413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135604387394166865888275 6203406581091250298832413)
        ·
          refine ⟨2326277467909218862062155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6203406581091250298832413 2326277467909218862062155)
          ·
            refine ⟨3489416201863828293093233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326277467909218862062155 3489416201863828293093233)
            ·
              refine ⟨2617062151397871219819925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3489416201863828293093233 2617062151397871219819925)
              ·
                refine ⟨122674788346775213429059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2617062151397871219819925 122674788346775213429059)
                ·
                  rfl

theorem cell22_3225262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_3225262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225262 prefixEnd_3225262 := by exact prefixLift 3225262
  have htrace : WordTrace (prefixWord ++ tailWord_3225262) baseStart_3225262 baseEnd_3225262 := by
    simpa [prefixWord, tailWord_3225262, baseEnd_3225262] using wordTrace_append hprefix tailTrace_3225262
  have hstable : (prefixWord ++ tailWord_3225262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225262).length < 2 ^ (prefixWord ++ tailWord_3225262).sum := by decide
  have hdescent : baseEnd_3225262 < baseStart_3225262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225316 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3225316 : Nat := 118140960795 + 3225316 * 2 ^ 59
def prefixEnd_3225316 : Nat := 4983230072969 + 3 ^ 40 * 3225316 * 2
def baseEnd_3225316 : Nat := 1104091580424538780011365

theorem tailTrace_3225316 : CollatzResearch.WordTrace tailWord_3225316 prefixEnd_3225316 1104091580424538780011365 := by
  unfold tailWord_3225316
  simp only [CollatzResearch.WordTrace]
  refine ⟨58818469391619223481643901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78424625855492297975525201 58818469391619223481643901)
  ·
    refine ⟨22056926021857208805616463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58818469391619223481643901 22056926021857208805616463)
    ·
      refine ⟨33085389032785813208424695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22056926021857208805616463 33085389032785813208424695)
      ·
        refine ⟨49628083549178719812637043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33085389032785813208424695 49628083549178719812637043)
        ·
          refine ⟨74442125323768079718955565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49628083549178719812637043 74442125323768079718955565)
          ·
            refine ⟨27915796996413029894608337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74442125323768079718955565 27915796996413029894608337)
            ·
              refine ⟨20936847747309772420956253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27915796996413029894608337 20936847747309772420956253)
              ·
                refine ⟨7851317905241164657858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20936847747309772420956253 7851317905241164657858595)
                ·
                  refine ⟨11776976857861746986787893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851317905241164657858595 11776976857861746986787893)
                  ·
                    refine ⟨1104091580424538780011365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11776976857861746986787893 1104091580424538780011365)
                    ·
                      rfl

theorem cell22_3225316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3225316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225316 prefixEnd_3225316 := by exact prefixLift 3225316
  have htrace : WordTrace (prefixWord ++ tailWord_3225316) baseStart_3225316 baseEnd_3225316 := by
    simpa [prefixWord, tailWord_3225316, baseEnd_3225316] using wordTrace_append hprefix tailTrace_3225316
  have hstable : (prefixWord ++ tailWord_3225316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225316).length < 2 ^ (prefixWord ++ tailWord_3225316).sum := by decide
  have hdescent : baseEnd_3225316 < baseStart_3225316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225320 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3225320 : Nat := 118140960795 + 3225320 * 2 ^ 59
def prefixEnd_3225320 : Nat := 4983230072969 + 3 ^ 40 * 3225320 * 2
def baseEnd_3225320 : Nat := 1104092949706284102911353

theorem tailTrace_3225320 : CollatzResearch.WordTrace tailWord_3225320 prefixEnd_3225320 1104092949706284102911353 := by
  unfold tailWord_3225320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58818542337611977823216707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78424723116815970430955609 58818542337611977823216707)
  ·
    refine ⟨88227813506417966734825061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58818542337611977823216707 88227813506417966734825061)
    ·
      refine ⟨16542715032453368762779699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88227813506417966734825061 16542715032453368762779699)
      ·
        refine ⟨24814072548680053144169549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16542715032453368762779699 24814072548680053144169549)
        ·
          refine ⟨9305277205755019929063581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24814072548680053144169549 9305277205755019929063581)
          ·
            refine ⟨3489478952158132473398843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9305277205755019929063581 3489478952158132473398843)
            ·
              refine ⟨5234218428237198710098265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489478952158132473398843 5234218428237198710098265)
              ·
                refine ⟨3925663821177899032573699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234218428237198710098265 3925663821177899032573699)
                ·
                  refine ⟨5888495731766848548860549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925663821177899032573699 5888495731766848548860549)
                  ·
                    refine ⟨1104092949706284102911353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888495731766848548860549 1104092949706284102911353)
                    ·
                      rfl

theorem cell22_3225320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3225320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225320 prefixEnd_3225320 := by exact prefixLift 3225320
  have htrace : WordTrace (prefixWord ++ tailWord_3225320) baseStart_3225320 baseEnd_3225320 := by
    simpa [prefixWord, tailWord_3225320, baseEnd_3225320] using wordTrace_append hprefix tailTrace_3225320
  have hstable : (prefixWord ++ tailWord_3225320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225320).length < 2 ^ (prefixWord ++ tailWord_3225320).sum := by decide
  have hdescent : baseEnd_3225320 < baseStart_3225320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225331 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_3225331 : Nat := 118140960795 + 3225331 * 2 ^ 59
def prefixEnd_3225331 : Nat := 4983230072969 + 3 ^ 40 * 3225331 * 2
def baseEnd_3225331 : Nat := 1104096715231083740886319

theorem tailTrace_3225331 : CollatzResearch.WordTrace tailWord_3225331 prefixEnd_3225331 1104096715231083740886319 := by
  unfold tailWord_3225331
  simp only [CollatzResearch.WordTrace]
  refine ⟨117637485878184104525083847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78424990585456069683389231 117637485878184104525083847)
  ·
    refine ⟨176456228817276156787625771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117637485878184104525083847 176456228817276156787625771)
    ·
      refine ⟨264684343225914235181438657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176456228817276156787625771 264684343225914235181438657)
      ·
        refine ⟨198513257419435676386078993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264684343225914235181438657 198513257419435676386078993)
        ·
          refine ⟨148884943064576757289559245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198513257419435676386078993 148884943064576757289559245)
          ·
            refine ⟨55831853649216283983584717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148884943064576757289559245 55831853649216283983584717)
            ·
              refine ⟨20936945118456106493844269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55831853649216283983584717 20936945118456106493844269)
              ·
                refine ⟨7851354419421039935191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20936945118456106493844269 7851354419421039935191601)
                ·
                  refine ⟨5888515814565779951393701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851354419421039935191601 5888515814565779951393701)
                  ·
                    refine ⟨1104096715231083740886319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888515814565779951393701 1104096715231083740886319)
                    ·
                      rfl

theorem cell22_3225331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_3225331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225331 prefixEnd_3225331 := by exact prefixLift 3225331
  have htrace : WordTrace (prefixWord ++ tailWord_3225331) baseStart_3225331 baseEnd_3225331 := by
    simpa [prefixWord, tailWord_3225331, baseEnd_3225331] using wordTrace_append hprefix tailTrace_3225331
  have hstable : (prefixWord ++ tailWord_3225331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225331).length < 2 ^ (prefixWord ++ tailWord_3225331).sum := by decide
  have hdescent : baseEnd_3225331 < baseStart_3225331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225348 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3225348 : Nat := 118140960795 + 3225348 * 2 ^ 59
def prefixEnd_3225348 : Nat := 4983230072969 + 3 ^ 40 * 3225348 * 2
def baseEnd_3225348 : Nat := 1104102534678501363211267

theorem tailTrace_3225348 : CollatzResearch.WordTrace tailWord_3225348 prefixEnd_3225348 1104102534678501363211267 := by
  unfold tailWord_3225348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58819052959561258214226349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78425403946081677618968465 58819052959561258214226349)
  ·
    refine ⟨22057144859835471830334881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58819052959561258214226349 22057144859835471830334881)
    ·
      refine ⟨16542858644876603872751161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22057144859835471830334881 16542858644876603872751161)
      ·
        refine ⟨12407143983657452904563371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16542858644876603872751161 12407143983657452904563371)
        ·
          refine ⟨18610715975486179356845057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12407143983657452904563371 18610715975486179356845057)
          ·
            refine ⟨13958036981614634517633793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18610715975486179356845057 13958036981614634517633793)
            ·
              refine ⟨10468527736210975888225345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958036981614634517633793 10468527736210975888225345)
              ·
                refine ⟨7851395802158231916169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10468527736210975888225345 7851395802158231916169009)
                ·
                  refine ⟨5888546851618673937126757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851395802158231916169009 5888546851618673937126757)
                  ·
                    refine ⟨1104102534678501363211267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888546851618673937126757 1104102534678501363211267)
                    ·
                      rfl

theorem cell22_3225348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3225348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225348 prefixEnd_3225348 := by exact prefixLift 3225348
  have htrace : WordTrace (prefixWord ++ tailWord_3225348) baseStart_3225348 baseEnd_3225348 := by
    simpa [prefixWord, tailWord_3225348, baseEnd_3225348] using wordTrace_append hprefix tailTrace_3225348
  have hstable : (prefixWord ++ tailWord_3225348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225348).length < 2 ^ (prefixWord ++ tailWord_3225348).sum := by decide
  have hdescent : baseEnd_3225348 < baseStart_3225348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225376 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_3225376 : Nat := 118140960795 + 3225376 * 2 ^ 59
def prefixEnd_3225376 : Nat := 4983230072969 + 3 ^ 40 * 3225376 * 2
def baseEnd_3225376 : Nat := 1104112119650718623511181

theorem tailTrace_3225376 : CollatzResearch.WordTrace tailWord_3225376 prefixEnd_3225376 1104112119650718623511181 := by
  unfold tailWord_3225376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58819563581510538605235991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78426084775347384806981321 58819563581510538605235991)
  ·
    refine ⟨88229345372265807907853987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58819563581510538605235991 88229345372265807907853987)
    ·
      refine ⟨132344018058398711861780981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88229345372265807907853987 132344018058398711861780981)
      ·
        refine ⟨12407251692974879237041967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132344018058398711861780981 12407251692974879237041967)
        ·
          refine ⟨18610877539462318855562951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12407251692974879237041967 18610877539462318855562951)
          ·
            refine ⟨27916316309193478283344427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18610877539462318855562951 27916316309193478283344427)
            ·
              refine ⟨41874474463790217425016641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27916316309193478283344427 41874474463790217425016641)
              ·
                refine ⟨31405855847842663068762481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41874474463790217425016641 31405855847842663068762481)
                ·
                  refine ⟨23554391885881997301571861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31405855847842663068762481 23554391885881997301571861)
                  ·
                    refine ⟨1104112119650718623511181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23554391885881997301571861 1104112119650718623511181)
                    ·
                      rfl

theorem cell22_3225376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_3225376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225376 prefixEnd_3225376 := by exact prefixLift 3225376
  have htrace : WordTrace (prefixWord ++ tailWord_3225376) baseStart_3225376 baseEnd_3225376 := by
    simpa [prefixWord, tailWord_3225376, baseEnd_3225376] using wordTrace_append hprefix tailTrace_3225376
  have hstable : (prefixWord ++ tailWord_3225376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225376).length < 2 ^ (prefixWord ++ tailWord_3225376).sum := by decide
  have hdescent : baseEnd_3225376 < baseStart_3225376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225425 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 5]
def baseStart_3225425 : Nat := 118140960795 + 3225425 * 2 ^ 59
def prefixEnd_3225425 : Nat := 4983230072969 + 3 ^ 40 * 3225425 * 2
def baseEnd_3225425 : Nat := 368042964450699609678677

theorem tailTrace_3225425 : CollatzResearch.WordTrace tailWord_3225425 prefixEnd_3225425 368042964450699609678677 := by
  unfold tailWord_3225425
  simp only [CollatzResearch.WordTrace]
  refine ⟨117640914339843558579005729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78427276226562372386003819 117640914339843558579005729)
  ·
    refine ⟨88230685754882668934254297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117640914339843558579005729 88230685754882668934254297)
    ·
      refine ⟨66173014316162001700690723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88230685754882668934254297 66173014316162001700690723)
      ·
        refine ⟨99259521474243002551036085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66173014316162001700690723 99259521474243002551036085)
        ·
          refine ⟨9305580138210281489159633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99259521474243002551036085 9305580138210281489159633)
          ·
            refine ⟨6979185103657711116869725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9305580138210281489159633 6979185103657711116869725)
            ·
              refine ⟨2617194413871641668826147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6979185103657711116869725 2617194413871641668826147)
              ·
                refine ⟨3925791620807462503239221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617194413871641668826147 3925791620807462503239221)
                ·
                  refine ⟨368042964450699609678677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3925791620807462503239221 368042964450699609678677)
                  ·
                    rfl

theorem cell22_3225425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_3225425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225425 prefixEnd_3225425 := by exact prefixLift 3225425
  have htrace : WordTrace (prefixWord ++ tailWord_3225425) baseStart_3225425 baseEnd_3225425 := by
    simpa [prefixWord, tailWord_3225425, baseEnd_3225425] using wordTrace_append hprefix tailTrace_3225425
  have hstable : (prefixWord ++ tailWord_3225425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225425).length < 2 ^ (prefixWord ++ tailWord_3225425).sum := by decide
  have hdescent : baseEnd_3225425 < baseStart_3225425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225451 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_3225451 : Nat := 118140960795 + 3225451 * 2 ^ 59
def prefixEnd_3225451 : Nat := 4983230072969 + 3 ^ 40 * 3225451 * 2
def baseEnd_3225451 : Nat := 1104137793683443427885951

theorem tailTrace_3225451 : CollatzResearch.WordTrace tailWord_3225451 prefixEnd_3225451 1104137793683443427885951 := by
  unfold tailWord_3225451
  simp only [CollatzResearch.WordTrace]
  refine ⟨117641862637749365019452207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78427908425166243346301471 117641862637749365019452207)
  ·
    refine ⟨176462793956624047529178311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117641862637749365019452207 176462793956624047529178311)
    ·
      refine ⟨264694190934936071293767467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176462793956624047529178311 264694190934936071293767467)
      ·
        refine ⟨397041286402404106940651201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264694190934936071293767467 397041286402404106940651201)
        ·
          refine ⟨297780964801803080205488401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397041286402404106940651201 297780964801803080205488401)
          ·
            refine ⟨223335723601352310154116301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297780964801803080205488401 223335723601352310154116301)
            ·
              refine ⟨83750896350507116307793613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223335723601352310154116301 83750896350507116307793613)
              ·
                refine ⟨31406586131440168615422605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83750896350507116307793613 31406586131440168615422605)
                ·
                  refine ⟨11777469799290063230783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31406586131440168615422605 11777469799290063230783477)
                  ·
                    refine ⟨1104137793683443427885951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11777469799290063230783477 1104137793683443427885951)
                    ·
                      rfl

theorem cell22_3225451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_3225451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225451 prefixEnd_3225451 := by exact prefixLift 3225451
  have htrace : WordTrace (prefixWord ++ tailWord_3225451) baseStart_3225451 baseEnd_3225451 := by
    simpa [prefixWord, tailWord_3225451, baseEnd_3225451] using wordTrace_append hprefix tailTrace_3225451
  have hstable : (prefixWord ++ tailWord_3225451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225451).length < 2 ^ (prefixWord ++ tailWord_3225451).sum := by decide
  have hdescent : baseEnd_3225451 < baseStart_3225451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225498 : List Nat := [3, 1, 1, 4, 2, 1, 2, 8]
def baseStart_3225498 : Nat := 118140960795 + 3225498 * 2 ^ 59
def prefixEnd_3225498 : Nat := 4983230072969 + 3 ^ 40 * 3225498 * 2
def baseEnd_3225498 : Nat := 122683764749327885773423

theorem tailTrace_3225498 : CollatzResearch.WordTrace tailWord_3225498 prefixEnd_3225498 122683764749327885773423 := by
  unfold tailWord_3225498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29410894217144773011603287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78429051245719394697608765 29410894217144773011603287)
  ·
    refine ⟨44116341325717159517404931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29410894217144773011603287 44116341325717159517404931)
    ·
      refine ⟨66174511988575739276107397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44116341325717159517404931 66174511988575739276107397)
      ·
        refine ⟨12407720997857951114270137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66174511988575739276107397 12407720997857951114270137)
        ·
          refine ⟨9305790748393463335702603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12407720997857951114270137 9305790748393463335702603)
          ·
            refine ⟨13958686122590195003553905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305790748393463335702603 13958686122590195003553905)
            ·
              refine ⟨10469014591942646252665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958686122590195003553905 10469014591942646252665429)
              ·
                refine ⟨122683764749327885773423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10469014591942646252665429 122683764749327885773423)
                ·
                  rfl

theorem cell22_3225498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_3225498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225498 prefixEnd_3225498 := by exact prefixLift 3225498
  have htrace : WordTrace (prefixWord ++ tailWord_3225498) baseStart_3225498 baseEnd_3225498 := by
    simpa [prefixWord, tailWord_3225498, baseEnd_3225498] using wordTrace_append hprefix tailTrace_3225498
  have hstable : (prefixWord ++ tailWord_3225498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225498).length < 2 ^ (prefixWord ++ tailWord_3225498).sum := by decide
  have hdescent : baseEnd_3225498 < baseStart_3225498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225500 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3225500 : Nat := 118140960795 + 3225500 * 2 ^ 59
def prefixEnd_3225500 : Nat := 4983230072969 + 3 ^ 40 * 3225500 * 2
def baseEnd_3225500 : Nat := 1104154567384823633410801

theorem tailTrace_3225500 : CollatzResearch.WordTrace tailWord_3225500 prefixEnd_3225500 1104154567384823633410801 := by
  unfold tailWord_3225500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58821824907285923193992977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78429099876381230925323969 58821824907285923193992977)
  ·
    refine ⟨44116368680464442395494733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58821824907285923193992977 44116368680464442395494733)
    ·
      refine ⟨16543638255174165898310525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44116368680464442395494733 16543638255174165898310525)
      ·
        refine ⟨6203864345690312211866447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16543638255174165898310525 6203864345690312211866447)
        ·
          refine ⟨9305796518535468317799671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203864345690312211866447 9305796518535468317799671)
          ·
            refine ⟨13958694777803202476699507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305796518535468317799671 13958694777803202476699507)
            ·
              refine ⟨20938042166704803715049261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958694777803202476699507 20938042166704803715049261)
              ·
                refine ⟨7851765812514301393143473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20938042166704803715049261 7851765812514301393143473)
                ·
                  refine ⟨5888824359385726044857605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851765812514301393143473 5888824359385726044857605)
                  ·
                    refine ⟨1104154567384823633410801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888824359385726044857605 1104154567384823633410801)
                    ·
                      rfl

theorem cell22_3225500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3225500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225500 prefixEnd_3225500 := by exact prefixLift 3225500
  have htrace : WordTrace (prefixWord ++ tailWord_3225500) baseStart_3225500 baseEnd_3225500 := by
    simpa [prefixWord, tailWord_3225500, baseEnd_3225500] using wordTrace_append hprefix tailTrace_3225500
  have hstable : (prefixWord ++ tailWord_3225500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225500).length < 2 ^ (prefixWord ++ tailWord_3225500).sum := by decide
  have hdescent : baseEnd_3225500 < baseStart_3225500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225513 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_3225513 : Nat := 118140960795 + 3225513 * 2 ^ 59
def prefixEnd_3225513 : Nat := 4983230072969 + 3 ^ 40 * 3225513 * 2
def baseEnd_3225513 : Nat := 1104159017550495932835761

theorem tailTrace_3225513 : CollatzResearch.WordTrace tailWord_3225513 prefixEnd_3225513 1104159017550495932835761 := by
  unfold tailWord_3225513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117644123963524749608209193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78429415975683166405472795 117644123963524749608209193)
  ·
    refine ⟨88233092972643562206156895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117644123963524749608209193 88233092972643562206156895)
    ·
      refine ⟨132349639458965343309235343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88233092972643562206156895 132349639458965343309235343)
      ·
        refine ⟨198524459188448014963853015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132349639458965343309235343 198524459188448014963853015)
        ·
          refine ⟨297786688782672022445779523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198524459188448014963853015 297786688782672022445779523)
          ·
            refine ⟨446680033174008033668669285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297786688782672022445779523 446680033174008033668669285)
            ·
              refine ⟨83752506220126506312875491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446680033174008033668669285 83752506220126506312875491)
              ·
                refine ⟨125628759330189759469313237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83752506220126506312875491 125628759330189759469313237)
                ·
                  refine ⟨2944424046801322487562029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125628759330189759469313237 2944424046801322487562029)
                  ·
                    refine ⟨1104159017550495932835761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944424046801322487562029 1104159017550495932835761)
                    ·
                      rfl

theorem cell22_3225513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_3225513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225513 prefixEnd_3225513 := by exact prefixLift 3225513
  have htrace : WordTrace (prefixWord ++ tailWord_3225513) baseStart_3225513 baseEnd_3225513 := by
    simpa [prefixWord, tailWord_3225513, baseEnd_3225513] using wordTrace_append hprefix tailTrace_3225513
  have hstable : (prefixWord ++ tailWord_3225513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225513).length < 2 ^ (prefixWord ++ tailWord_3225513).sum := by decide
  have hdescent : baseEnd_3225513 < baseStart_3225513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225532 : List Nat := [2, 2, 2, 5, 1, 2, 1, 7]
def baseStart_3225532 : Nat := 118140960795 + 3225532 * 2 ^ 59
def prefixEnd_3225532 : Nat := 4983230072969 + 3 ^ 40 * 3225532 * 2
def baseEnd_3225532 : Nat := 122685057959865135178967

theorem tailTrace_3225532 : CollatzResearch.WordTrace tailWord_3225532 prefixEnd_3225532 122685057959865135178967 := by
  unfold tailWord_3225532
  simp only [CollatzResearch.WordTrace]
  refine ⟨58822408475227957926575425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78429877966970610568767233 58822408475227957926575425)
  ·
    refine ⟨44116806356420968444931569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58822408475227957926575425 44116806356420968444931569)
    ·
      refine ⟨33087604767315726333698677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44116806356420968444931569 33087604767315726333698677)
      ·
        refine ⟨3101962946935849343784251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33087604767315726333698677 3101962946935849343784251)
        ·
          refine ⟨4652944420403774015676377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101962946935849343784251 4652944420403774015676377)
          ·
            refine ⟨3489708315302830511757283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652944420403774015676377 3489708315302830511757283)
            ·
              refine ⟨5234562472954245767635925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489708315302830511757283 5234562472954245767635925)
              ·
                refine ⟨122685057959865135178967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5234562472954245767635925 122685057959865135178967)
                ·
                  rfl

theorem cell22_3225532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_3225532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225532 prefixEnd_3225532 := by exact prefixLift 3225532
  have htrace : WordTrace (prefixWord ++ tailWord_3225532) baseStart_3225532 baseEnd_3225532 := by
    simpa [prefixWord, tailWord_3225532, baseEnd_3225532] using wordTrace_append hprefix tailTrace_3225532
  have hstable : (prefixWord ++ tailWord_3225532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225532).length < 2 ^ (prefixWord ++ tailWord_3225532).sum := by decide
  have hdescent : baseEnd_3225532 < baseStart_3225532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225607 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3225607 : Nat := 118140960795 + 3225607 * 2 ^ 59
def prefixEnd_3225607 : Nat := 4983230072969 + 3 ^ 40 * 3225607 * 2
def baseEnd_3225607 : Nat := 1104191195671511020985473

theorem tailTrace_3225607 : CollatzResearch.WordTrace tailWord_3225607 prefixEnd_3225607 1104191195671511020985473 := by
  unfold tailWord_3225607
  simp only [CollatzResearch.WordTrace]
  refine ⟨117647552425184203662131075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78431701616789469108087383 117647552425184203662131075)
  ·
    refine ⟨176471328637776305493196613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117647552425184203662131075 176471328637776305493196613)
    ·
      refine ⟨33088374119583057279974365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176471328637776305493196613 33088374119583057279974365)
      ·
        refine ⟨12408140294843646479990387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33088374119583057279974365 12408140294843646479990387)
        ·
          refine ⟨18612210442265469719985581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408140294843646479990387 18612210442265469719985581)
          ·
            refine ⟨6979578915849551144994593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18612210442265469719985581 6979578915849551144994593)
            ·
              refine ⟨5234684186887163358745945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979578915849551144994593 5234684186887163358745945)
              ·
                refine ⟨3926013140165372519059459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234684186887163358745945 3926013140165372519059459)
                ·
                  refine ⟨5889019710248058778589189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926013140165372519059459 5889019710248058778589189)
                  ·
                    refine ⟨1104191195671511020985473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889019710248058778589189 1104191195671511020985473)
                    ·
                      rfl

theorem cell22_3225607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3225607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225607 prefixEnd_3225607 := by exact prefixLift 3225607
  have htrace : WordTrace (prefixWord ++ tailWord_3225607) baseStart_3225607 baseEnd_3225607 := by
    simpa [prefixWord, tailWord_3225607, baseEnd_3225607] using wordTrace_append hprefix tailTrace_3225607
  have hstable : (prefixWord ++ tailWord_3225607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225607).length < 2 ^ (prefixWord ++ tailWord_3225607).sum := by decide
  have hdescent : baseEnd_3225607 < baseStart_3225607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225635 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_3225635 : Nat := 118140960795 + 3225635 * 2 ^ 59
def prefixEnd_3225635 : Nat := 4983230072969 + 3 ^ 40 * 3225635 * 2
def baseEnd_3225635 : Nat := 1104200780643728281285387

theorem tailTrace_3225635 : CollatzResearch.WordTrace tailWord_3225635 prefixEnd_3225635 1104200780643728281285387 := by
  unfold tailWord_3225635
  simp only [CollatzResearch.WordTrace]
  refine ⟨117648573669082764444150359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78432382446055176296100239 117648573669082764444150359)
  ·
    refine ⟨176472860503624146666225539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117648573669082764444150359 176472860503624146666225539)
    ·
      refine ⟨264709290755436219999338309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176472860503624146666225539 264709290755436219999338309)
      ·
        refine ⟨49632992016644291249875933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264709290755436219999338309 49632992016644291249875933)
        ·
          refine ⟨18612372006241609218703475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49632992016644291249875933 18612372006241609218703475)
          ·
            refine ⟨27918558009362413828055213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18612372006241609218703475 27918558009362413828055213)
            ·
              refine ⟨10469459253510905185520705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27918558009362413828055213 10469459253510905185520705)
              ·
                refine ⟨7852094440133178889140529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10469459253510905185520705 7852094440133178889140529)
                ·
                  refine ⟨5889070830099884166855397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852094440133178889140529 5889070830099884166855397)
                  ·
                    refine ⟨1104200780643728281285387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889070830099884166855397 1104200780643728281285387)
                    ·
                      rfl

theorem cell22_3225635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_3225635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225635 prefixEnd_3225635 := by exact prefixLift 3225635
  have htrace : WordTrace (prefixWord ++ tailWord_3225635) baseStart_3225635 baseEnd_3225635 := by
    simpa [prefixWord, tailWord_3225635, baseEnd_3225635] using wordTrace_append hprefix tailTrace_3225635
  have hstable : (prefixWord ++ tailWord_3225635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225635).length < 2 ^ (prefixWord ++ tailWord_3225635).sum := by decide
  have hdescent : baseEnd_3225635 < baseStart_3225635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225639 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 6]
def baseStart_3225639 : Nat := 118140960795 + 3225639 * 2 ^ 59
def prefixEnd_3225639 : Nat := 4983230072969 + 3 ^ 40 * 3225639 * 2
def baseEnd_3225639 : Nat := 368067383308491201395125

theorem tailTrace_3225639 : CollatzResearch.WordTrace tailWord_3225639 prefixEnd_3225639 368067383308491201395125 := by
  unfold tailWord_3225639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117648719561068273127295971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78432479707378848751530647 117648719561068273127295971)
  ·
    refine ⟨176473079341602409690943957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117648719561068273127295971 176473079341602409690943957)
    ·
      refine ⟨4136087797068806477131499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 176473079341602409690943957 4136087797068806477131499)
      ·
        refine ⟨6204131695603209715697249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136087797068806477131499 6204131695603209715697249)
        ·
          refine ⟨4653098771702407286772937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204131695603209715697249 4653098771702407286772937)
          ·
            refine ⟨3489824078776805465079703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653098771702407286772937 3489824078776805465079703)
            ·
              refine ⟨5234736118165208197619555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489824078776805465079703 5234736118165208197619555)
              ·
                refine ⟨7852104177247812296429333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234736118165208197619555 7852104177247812296429333)
                ·
                  refine ⟨368067383308491201395125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7852104177247812296429333 368067383308491201395125)
                  ·
                    rfl

theorem cell22_3225639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].length) (baseStart_3225639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225639 prefixEnd_3225639 := by exact prefixLift 3225639
  have htrace : WordTrace (prefixWord ++ tailWord_3225639) baseStart_3225639 baseEnd_3225639 := by
    simpa [prefixWord, tailWord_3225639, baseEnd_3225639] using wordTrace_append hprefix tailTrace_3225639
  have hstable : (prefixWord ++ tailWord_3225639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225639).length < 2 ^ (prefixWord ++ tailWord_3225639).sum := by decide
  have hdescent : baseEnd_3225639 < baseStart_3225639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225650 : List Nat := [3, 2, 1, 1, 2, 4, 2, 7]
def baseStart_3225650 : Nat := 118140960795 + 3225650 * 2 ^ 59
def prefixEnd_3225650 : Nat := 4983230072969 + 3 ^ 40 * 3225650 * 2
def baseEnd_3225650 : Nat := 122689546161141471351149

theorem tailTrace_3225650 : CollatzResearch.WordTrace tailWord_3225650 prefixEnd_3225650 122689546161141471351149 := by
  unfold tailWord_3225650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29412280191007105501486601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78432747176018948003964269 29412280191007105501486601)
  ·
    refine ⟨22059210143255329126114951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29412280191007105501486601 22059210143255329126114951)
    ·
      refine ⟨33088815214882993689172427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22059210143255329126114951 33088815214882993689172427)
      ·
        refine ⟨49633222822324490533758641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33088815214882993689172427 49633222822324490533758641)
        ·
          refine ⟨37224917116743367900318981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49633222822324490533758641 37224917116743367900318981)
          ·
            refine ⟨6979671959389381481309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37224917116743367900318981 6979671959389381481309809)
            ·
              refine ⟨5234753969542036110982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979671959389381481309809 5234753969542036110982357)
              ·
                refine ⟨122689546161141471351149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5234753969542036110982357 122689546161141471351149)
                ·
                  rfl

theorem cell22_3225650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_3225650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225650 prefixEnd_3225650 := by exact prefixLift 3225650
  have htrace : WordTrace (prefixWord ++ tailWord_3225650) baseStart_3225650 baseEnd_3225650 := by
    simpa [prefixWord, tailWord_3225650, baseEnd_3225650] using wordTrace_append hprefix tailTrace_3225650
  have hstable : (prefixWord ++ tailWord_3225650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225650).length < 2 ^ (prefixWord ++ tailWord_3225650).sum := by decide
  have hdescent : baseEnd_3225650 < baseStart_3225650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225654 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3225654 : Nat := 118140960795 + 3225654 * 2 ^ 59
def prefixEnd_3225654 : Nat := 4983230072969 + 3 ^ 40 * 3225654 * 2
def baseEnd_3225654 : Nat := 1104207284732018565060329

theorem tailTrace_3225654 : CollatzResearch.WordTrace tailWord_3225654 prefixEnd_3225654 1104207284732018565060329 := by
  unfold tailWord_3225654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353079166000870668068251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78432844437342620459394677 7353079166000870668068251)
  ·
    refine ⟨11029618749001306002102377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7353079166000870668068251 11029618749001306002102377)
    ·
      refine ⟨8272214061750979501576783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029618749001306002102377 8272214061750979501576783)
      ·
        refine ⟨12408321092626469252365175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272214061750979501576783 12408321092626469252365175)
        ·
          refine ⟨18612481638939703878547763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408321092626469252365175 18612481638939703878547763)
          ·
            refine ⟨27918722458409555817821645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18612481638939703878547763 27918722458409555817821645)
            ·
              refine ⟨10469520921903583431683117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27918722458409555817821645 10469520921903583431683117)
              ·
                refine ⟨3926070345713843786881169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10469520921903583431683117 3926070345713843786881169)
                ·
                  refine ⟨2944552759285382840160877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926070345713843786881169 2944552759285382840160877)
                  ·
                    refine ⟨1104207284732018565060329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944552759285382840160877 1104207284732018565060329)
                    ·
                      rfl

theorem cell22_3225654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3225654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225654 prefixEnd_3225654 := by exact prefixLift 3225654
  have htrace : WordTrace (prefixWord ++ tailWord_3225654) baseStart_3225654 baseEnd_3225654 := by
    simpa [prefixWord, tailWord_3225654, baseEnd_3225654] using wordTrace_append hprefix tailTrace_3225654
  have hstable : (prefixWord ++ tailWord_3225654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225654).length < 2 ^ (prefixWord ++ tailWord_3225654).sum := by decide
  have hdescent : baseEnd_3225654 < baseStart_3225654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225757 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 6]
def baseStart_3225757 : Nat := 118140960795 + 3225757 * 2 ^ 59
def prefixEnd_3225757 : Nat := 4983230072969 + 3 ^ 40 * 3225757 * 2
def baseEnd_3225757 : Nat := 368080847912320209911671

theorem tailTrace_3225757 : CollatzResearch.WordTrace tailWord_3225757 prefixEnd_3225757 368080847912320209911671 := by
  unfold tailWord_3225757
  simp only [CollatzResearch.WordTrace]
  refine ⟨117653023374640779280091525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78435348916427186186727683 117653023374640779280091525)
  ·
    refine ⟨22059941882745146115017161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117653023374640779280091525 22059941882745146115017161)
    ·
      refine ⟨16544956412058859586262871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22059941882745146115017161 16544956412058859586262871)
      ·
        refine ⟨24817434618088289379394307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16544956412058859586262871 24817434618088289379394307)
        ·
          refine ⟨37226151927132434069091461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24817434618088289379394307 37226151927132434069091461)
          ·
            refine ⟨6979903486337331387954649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37226151927132434069091461 6979903486337331387954649)
            ·
              refine ⟨5234927614752998540965987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979903486337331387954649 5234927614752998540965987)
              ·
                refine ⟨7852391422129497811448981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234927614752998540965987 7852391422129497811448981)
                ·
                  refine ⟨368080847912320209911671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7852391422129497811448981 368080847912320209911671)
                  ·
                    rfl

theorem cell22_3225757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_3225757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225757 prefixEnd_3225757 := by exact prefixLift 3225757
  have htrace : WordTrace (prefixWord ++ tailWord_3225757) baseStart_3225757 baseEnd_3225757 := by
    simpa [prefixWord, tailWord_3225757, baseEnd_3225757] using wordTrace_append hprefix tailTrace_3225757
  have hstable : (prefixWord ++ tailWord_3225757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225757).length < 2 ^ (prefixWord ++ tailWord_3225757).sum := by decide
  have hdescent : baseEnd_3225757 < baseStart_3225757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225785 : List Nat := [1, 2, 1, 4, 1, 2, 3, 8]
def baseStart_3225785 : Nat := 118140960795 + 3225785 * 2 ^ 59
def prefixEnd_3225785 : Nat := 4983230072969 + 3 ^ 40 * 3225785 * 2
def baseEnd_3225785 : Nat := 122694680967686432226103

theorem tailTrace_3225785 : CollatzResearch.WordTrace tailWord_3225785 prefixEnd_3225785 122694680967686432226103 := by
  unfold tailWord_3225785
  simp only [CollatzResearch.WordTrace]
  refine ⟨117654044618539340062110809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78436029745692893374740539 117654044618539340062110809)
  ·
    refine ⟨88240533463904505046583107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117654044618539340062110809 88240533463904505046583107)
    ·
      refine ⟨132360800195856757569874661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88240533463904505046583107 132360800195856757569874661)
      ·
        refine ⟨24817650036723142044351499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132360800195856757569874661 24817650036723142044351499)
        ·
          refine ⟨37226475055084713066527249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24817650036723142044351499 37226475055084713066527249)
          ·
            refine ⟨27919856291313534799895437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37226475055084713066527249 27919856291313534799895437)
            ·
              refine ⟨10469946109242575549960789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27919856291313534799895437 10469946109242575549960789)
              ·
                refine ⟨122694680967686432226103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10469946109242575549960789 122694680967686432226103)
                ·
                  rfl

theorem cell22_3225785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 8].length) (baseStart_3225785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225785 prefixEnd_3225785 := by exact prefixLift 3225785
  have htrace : WordTrace (prefixWord ++ tailWord_3225785) baseStart_3225785 baseEnd_3225785 := by
    simpa [prefixWord, tailWord_3225785, baseEnd_3225785] using wordTrace_append hprefix tailTrace_3225785
  have hstable : (prefixWord ++ tailWord_3225785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225785).length < 2 ^ (prefixWord ++ tailWord_3225785).sum := by decide
  have hdescent : baseEnd_3225785 < baseStart_3225785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225815 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3225815 : Nat := 118140960795 + 3225815 * 2 ^ 59
def prefixEnd_3225815 : Nat := 4983230072969 + 3 ^ 40 * 3225815 * 2
def baseEnd_3225815 : Nat := 1104262398322267811784835

theorem tailTrace_3225815 : CollatzResearch.WordTrace tailWord_3225815 prefixEnd_3225815 1104262398322267811784835 := by
  unfold tailWord_3225815
  simp only [CollatzResearch.WordTrace]
  refine ⟨117655138808430655185702899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78436759205620436790468599 117655138808430655185702899)
  ·
    refine ⟨176482708212645982778554349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117655138808430655185702899 176482708212645982778554349)
    ·
      refine ⟨66181015579742243541957881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176482708212645982778554349 66181015579742243541957881)
      ·
        refine ⟨49635761684806682656468411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66181015579742243541957881 49635761684806682656468411)
        ·
          refine ⟨74453642527210023984702617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49635761684806682656468411 74453642527210023984702617)
          ·
            refine ⟨55840231895407517988526963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74453642527210023984702617 55840231895407517988526963)
            ·
              refine ⟨83760347843111276982790445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55840231895407517988526963 83760347843111276982790445)
              ·
                refine ⟨31410130441166728868546417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83760347843111276982790445 31410130441166728868546417)
                ·
                  refine ⟨23557597830875046651409813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31410130441166728868546417 23557597830875046651409813)
                  ·
                    refine ⟨1104262398322267811784835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23557597830875046651409813 1104262398322267811784835)
                    ·
                      rfl

theorem cell22_3225815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3225815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225815 prefixEnd_3225815 := by exact prefixLift 3225815
  have htrace : WordTrace (prefixWord ++ tailWord_3225815) baseStart_3225815 baseEnd_3225815 := by
    simpa [prefixWord, tailWord_3225815, baseEnd_3225815] using wordTrace_append hprefix tailTrace_3225815
  have hstable : (prefixWord ++ tailWord_3225815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225815).length < 2 ^ (prefixWord ++ tailWord_3225815).sum := by decide
  have hdescent : baseEnd_3225815 < baseStart_3225815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225864 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_3225864 : Nat := 118140960795 + 3225864 * 2 ^ 59
def prefixEnd_3225864 : Nat := 4983230072969 + 3 ^ 40 * 3225864 * 2
def baseEnd_3225864 : Nat := 368093057341216005769895

theorem tailTrace_3225864 : CollatzResearch.WordTrace tailWord_3225864 prefixEnd_3225864 368093057341216005769895 := by
  unfold tailWord_3225864
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828462992626568277118323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78437950656835424369491097 58828462992626568277118323)
  ·
    refine ⟨88242694488939852415677485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58828462992626568277118323 88242694488939852415677485)
    ·
      refine ⟨33091010433352444655879057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88242694488939852415677485 33091010433352444655879057)
      ·
        refine ⟨24818257825014333491909293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33091010433352444655879057 24818257825014333491909293)
        ·
          refine ⟨9306846684380375059465985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24818257825014333491909293 9306846684380375059465985)
          ·
            refine ⟨6980135013285281294599489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306846684380375059465985 6980135013285281294599489)
            ·
              refine ⟨5235101259963960970949617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980135013285281294599489 5235101259963960970949617)
              ·
                refine ⟨3926325944972970728212213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5235101259963960970949617 3926325944972970728212213)
                ·
                  refine ⟨368093057341216005769895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3926325944972970728212213 368093057341216005769895)
                  ·
                    rfl

theorem cell22_3225864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_3225864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225864 prefixEnd_3225864 := by exact prefixLift 3225864
  have htrace : WordTrace (prefixWord ++ tailWord_3225864) baseStart_3225864 baseEnd_3225864 := by
    simpa [prefixWord, tailWord_3225864, baseEnd_3225864] using wordTrace_append hprefix tailTrace_3225864
  have hstable : (prefixWord ++ tailWord_3225864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225864).length < 2 ^ (prefixWord ++ tailWord_3225864).sum := by decide
  have hdescent : baseEnd_3225864 < baseStart_3225864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225875 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 10]
def baseStart_3225875 : Nat := 118140960795 + 3225875 * 2 ^ 59
def prefixEnd_3225875 : Nat := 4983230072969 + 3 ^ 40 * 3225875 * 2
def baseEnd_3225875 : Nat := 368094312516149218428217

theorem tailTrace_3225875 : CollatzResearch.WordTrace tailWord_3225875 prefixEnd_3225875 368094312516149218428217 := by
  unfold tailWord_3225875
  simp only [CollatzResearch.WordTrace]
  refine ⟨117657327188213285432887079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78438218125475523621924719 117657327188213285432887079)
  ·
    refine ⟨176485990782319928149330619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117657327188213285432887079 176485990782319928149330619)
    ·
      refine ⟨264728986173479892223995929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176485990782319928149330619 264728986173479892223995929)
      ·
        refine ⟨198546739630109919167996947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264728986173479892223995929 198546739630109919167996947)
        ·
          refine ⟨297820109445164878751995421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198546739630109919167996947 297820109445164878751995421)
          ·
            refine ⟨111682541041936829531998283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297820109445164878751995421 111682541041936829531998283)
            ·
              refine ⟨167523811562905244297997425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111682541041936829531998283 167523811562905244297997425)
              ·
                refine ⟨125642858672178933223498069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167523811562905244297997425 125642858672178933223498069)
                ·
                  refine ⟨368094312516149218428217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125642858672178933223498069 368094312516149218428217)
                  ·
                    rfl

theorem cell22_3225875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_3225875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225875 prefixEnd_3225875 := by exact prefixLift 3225875
  have htrace : WordTrace (prefixWord ++ tailWord_3225875) baseStart_3225875 baseEnd_3225875 := by
    simpa [prefixWord, tailWord_3225875, baseEnd_3225875] using wordTrace_append hprefix tailTrace_3225875
  have hstable : (prefixWord ++ tailWord_3225875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225875).length < 2 ^ (prefixWord ++ tailWord_3225875).sum := by decide
  have hdescent : baseEnd_3225875 < baseStart_3225875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225877 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3225877 : Nat := 118140960795 + 3225877 * 2 ^ 59
def prefixEnd_3225877 : Nat := 4983230072969 + 3 ^ 40 * 3225877 * 2
def baseEnd_3225877 : Nat := 1104283622189320316734645

theorem tailTrace_3225877 : CollatzResearch.WordTrace tailWord_3225877 prefixEnd_3225877 1104283622189320316734645 := by
  unfold tailWord_3225877
  simp only [CollatzResearch.WordTrace]
  refine ⟨117657400134206039774459885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78438266756137359849639923 117657400134206039774459885)
  ·
    refine ⟨44121525050327264915422457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117657400134206039774459885 44121525050327264915422457)
    ·
      refine ⟨33091143787745448686566843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44121525050327264915422457 33091143787745448686566843)
      ·
        refine ⟨49636715681618173029850265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33091143787745448686566843 49636715681618173029850265)
        ·
          refine ⟨37227536761213629772387699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49636715681618173029850265 37227536761213629772387699)
          ·
            refine ⟨55841305141820444658581549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37227536761213629772387699 55841305141820444658581549)
            ·
              refine ⟨20940489428182666746968081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55841305141820444658581549 20940489428182666746968081)
              ·
                refine ⟨15705367071137000060226061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20940489428182666746968081 15705367071137000060226061)
                ·
                  refine ⟨5889512651676375022584773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15705367071137000060226061 5889512651676375022584773)
                  ·
                    refine ⟨1104283622189320316734645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889512651676375022584773 1104283622189320316734645)
                    ·
                      rfl

theorem cell22_3225877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3225877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225877 prefixEnd_3225877 := by exact prefixLift 3225877
  have htrace : WordTrace (prefixWord ++ tailWord_3225877) baseStart_3225877 baseEnd_3225877 := by
    simpa [prefixWord, tailWord_3225877, baseEnd_3225877] using wordTrace_append hprefix tailTrace_3225877
  have hstable : (prefixWord ++ tailWord_3225877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225877).length < 2 ^ (prefixWord ++ tailWord_3225877).sum := by decide
  have hdescent : baseEnd_3225877 < baseStart_3225877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225892 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3225892 : Nat := 118140960795 + 3225892 * 2 ^ 59
def prefixEnd_3225892 : Nat := 4983230072969 + 3 ^ 40 * 3225892 * 2
def baseEnd_3225892 : Nat := 368096252331955092536533

theorem tailTrace_3225892 : CollatzResearch.WordTrace tailWord_3225892 prefixEnd_3225892 368096252331955092536533 := by
  unfold tailWord_3225892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828973614575848668127965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78438631486101131557503953 58828973614575848668127965)
  ·
    refine ⟨22060865105465943250547987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58828973614575848668127965 22060865105465943250547987)
    ·
      refine ⟨33091297658198914875821981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060865105465943250547987 33091297658198914875821981)
      ·
        refine ⟨12409236621824593078433243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33091297658198914875821981 12409236621824593078433243)
        ·
          refine ⟨18613854932736889617649865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409236621824593078433243 18613854932736889617649865)
          ·
            refine ⟨13960391199552667213237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18613854932736889617649865 13960391199552667213237399)
            ·
              refine ⟨20940586799329000819856099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13960391199552667213237399 20940586799329000819856099)
              ·
                refine ⟨31410880198993501229784149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20940586799329000819856099 31410880198993501229784149)
                ·
                  refine ⟨368096252331955092536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31410880198993501229784149 368096252331955092536533)
                  ·
                    rfl

theorem cell22_3225892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3225892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225892 prefixEnd_3225892 := by exact prefixLift 3225892
  have htrace : WordTrace (prefixWord ++ tailWord_3225892) baseStart_3225892 baseEnd_3225892 := by
    simpa [prefixWord, tailWord_3225892, baseEnd_3225892] using wordTrace_append hprefix tailTrace_3225892
  have hstable : (prefixWord ++ tailWord_3225892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225892).length < 2 ^ (prefixWord ++ tailWord_3225892).sum := by decide
  have hdescent : baseEnd_3225892 < baseStart_3225892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225907 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_3225907 : Nat := 118140960795 + 3225907 * 2 ^ 59
def prefixEnd_3225907 : Nat := 4983230072969 + 3 ^ 40 * 3225907 * 2
def baseEnd_3225907 : Nat := 1104293891802410238484553

theorem tailTrace_3225907 : CollatzResearch.WordTrace tailWord_3225907 prefixEnd_3225907 1104293891802410238484553 := by
  unfold tailWord_3225907
  simp only [CollatzResearch.WordTrace]
  refine ⟨117658494324097354898051975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78438996216064903265367983 117658494324097354898051975)
  ·
    refine ⟨176487741486146032347077963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117658494324097354898051975 176487741486146032347077963)
    ·
      refine ⟨264731612229219048520616945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176487741486146032347077963 264731612229219048520616945)
      ·
        refine ⟨198548709171914286390462709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264731612229219048520616945 198548709171914286390462709)
        ·
          refine ⟨18613941484866964349105879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198548709171914286390462709 18613941484866964349105879)
          ·
            refine ⟨27920912227300446523658819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18613941484866964349105879 27920912227300446523658819)
            ·
              refine ⟨41881368340950669785488229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27920912227300446523658819 41881368340950669785488229)
              ·
                refine ⟨7852756563928250584779043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41881368340950669785488229 7852756563928250584779043)
                ·
                  refine ⟨11779134845892375877168565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852756563928250584779043 11779134845892375877168565)
                  ·
                    refine ⟨1104293891802410238484553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11779134845892375877168565 1104293891802410238484553)
                    ·
                      rfl

theorem cell22_3225907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_3225907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225907 prefixEnd_3225907 := by exact prefixLift 3225907
  have htrace : WordTrace (prefixWord ++ tailWord_3225907) baseStart_3225907 baseEnd_3225907 := by
    simpa [prefixWord, tailWord_3225907, baseEnd_3225907] using wordTrace_append hprefix tailTrace_3225907
  have hstable : (prefixWord ++ tailWord_3225907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225907).length < 2 ^ (prefixWord ++ tailWord_3225907).sum := by decide
  have hdescent : baseEnd_3225907 < baseStart_3225907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225941 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3225941 : Nat := 118140960795 + 3225941 * 2 ^ 59
def prefixEnd_3225941 : Nat := 4983230072969 + 3 ^ 40 * 3225941 * 2
def baseEnd_3225941 : Nat := 1104305530697245483134449

theorem tailTrace_3225941 : CollatzResearch.WordTrace tailWord_3225941 prefixEnd_3225941 1104305530697245483134449 := by
  unfold tailWord_3225941
  simp only [CollatzResearch.WordTrace]
  refine ⟨117659734405974178704789677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78439822937316119136526451 117659734405974178704789677)
  ·
    refine ⟨44122400402240317014296129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117659734405974178704789677 44122400402240317014296129)
    ·
      refine ⟨33091800301680237760722097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44122400402240317014296129 33091800301680237760722097)
      ·
        refine ⟨24818850226260178320541573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33091800301680237760722097 24818850226260178320541573)
        ·
          refine ⟨4653534417423783435101545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24818850226260178320541573 4653534417423783435101545)
          ·
            refine ⟨3490150813067837576326159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653534417423783435101545 3490150813067837576326159)
            ·
              refine ⟨5235226219601756364489239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490150813067837576326159 5235226219601756364489239)
              ·
                refine ⟨7852839329402634546733859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235226219601756364489239 7852839329402634546733859)
                ·
                  refine ⟨11779258994103951820100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852839329402634546733859 11779258994103951820100789)
                  ·
                    refine ⟨1104305530697245483134449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11779258994103951820100789 1104305530697245483134449)
                    ·
                      rfl

theorem cell22_3225941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3225941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225941 prefixEnd_3225941 := by exact prefixLift 3225941
  have htrace : WordTrace (prefixWord ++ tailWord_3225941) baseStart_3225941 baseEnd_3225941 := by
    simpa [prefixWord, tailWord_3225941, baseEnd_3225941] using wordTrace_append hprefix tailTrace_3225941
  have hstable : (prefixWord ++ tailWord_3225941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225941).length < 2 ^ (prefixWord ++ tailWord_3225941).sum := by decide
  have hdescent : baseEnd_3225941 < baseStart_3225941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225954 : List Nat := [3, 3, 2, 1, 1, 3, 1, 8]
def baseStart_3225954 : Nat := 118140960795 + 3225954 * 2 ^ 59
def prefixEnd_3225954 : Nat := 4983230072969 + 3 ^ 40 * 3225954 * 2
def baseEnd_3225954 : Nat := 122701108984768642506601

theorem tailTrace_3225954 : CollatzResearch.WordTrace tailWord_3225954 prefixEnd_3225954 122701108984768642506601 := by
  unfold tailWord_3225954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29415052138731770481253229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78440139036618054616675277 29415052138731770481253229)
  ·
    refine ⟨11030644552024413930469961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29415052138731770481253229 11030644552024413930469961)
    ·
      refine ⟨8272983414018310447852471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11030644552024413930469961 8272983414018310447852471)
      ·
        refine ⟨12409475121027465671778707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272983414018310447852471 12409475121027465671778707)
        ·
          refine ⟨18614212681541198507668061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409475121027465671778707 18614212681541198507668061)
          ·
            refine ⟨6980329755577949440375523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18614212681541198507668061 6980329755577949440375523)
            ·
              refine ⟨10470494633366924160563285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980329755577949440375523 10470494633366924160563285)
              ·
                refine ⟨122701108984768642506601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10470494633366924160563285 122701108984768642506601)
                ·
                  rfl

theorem cell22_3225954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_3225954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3225954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3225954 prefixEnd_3225954 := by exact prefixLift 3225954
  have htrace : WordTrace (prefixWord ++ tailWord_3225954) baseStart_3225954 baseEnd_3225954 := by
    simpa [prefixWord, tailWord_3225954, baseEnd_3225954] using wordTrace_append hprefix tailTrace_3225954
  have hstable : (prefixWord ++ tailWord_3225954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225954).length < 2 ^ (prefixWord ++ tailWord_3225954).sum := by decide
  have hdescent : baseEnd_3225954 < baseStart_3225954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226037 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3226037 : Nat := 118140960795 + 3226037 * 2 ^ 59
def prefixEnd_3226037 : Nat := 4983230072969 + 3 ^ 40 * 3226037 * 2
def baseEnd_3226037 : Nat := 1104338393459133232734155

theorem tailTrace_3226037 : CollatzResearch.WordTrace tailWord_3226037 prefixEnd_3226037 1104338393459133232734155 := by
  unfold tailWord_3226037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117663235813626387100284365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78442157209084258066856243 117663235813626387100284365)
  ·
    refine ⟨44123713430109895162606637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117663235813626387100284365 44123713430109895162606637)
    ·
      refine ⟨16546392536291210685977489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44123713430109895162606637 16546392536291210685977489)
      ·
        refine ⟨12409794402218408014483117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16546392536291210685977489 12409794402218408014483117)
        ·
          refine ⟨4653672900831903005431169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12409794402218408014483117 4653672900831903005431169)
          ·
            refine ⟨3490254675623927254073377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653672900831903005431169 3490254675623927254073377)
            ·
              refine ⟨2617691006717945440555033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3490254675623927254073377 2617691006717945440555033)
              ·
                refine ⟨1963268255038459080416275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2617691006717945440555033 1963268255038459080416275)
                ·
                  refine ⟨2944902382557688620624413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963268255038459080416275 2944902382557688620624413)
                  ·
                    refine ⟨1104338393459133232734155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944902382557688620624413 1104338393459133232734155)
                    ·
                      rfl

theorem cell22_3226037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3226037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226037 prefixEnd_3226037 := by exact prefixLift 3226037
  have htrace : WordTrace (prefixWord ++ tailWord_3226037) baseStart_3226037 baseEnd_3226037 := by
    simpa [prefixWord, tailWord_3226037, baseEnd_3226037] using wordTrace_append hprefix tailTrace_3226037
  have hstable : (prefixWord ++ tailWord_3226037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226037).length < 2 ^ (prefixWord ++ tailWord_3226037).sum := by decide
  have hdescent : baseEnd_3226037 < baseStart_3226037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226059 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 6, 3]
def baseStart_3226059 : Nat := 118140960795 + 3226059 * 2 ^ 59
def prefixEnd_3226059 : Nat := 4983230072969 + 3 ^ 40 * 3226059 * 2
def baseEnd_3226059 : Nat := 1104345924508732508684087

theorem tailTrace_3226059 : CollatzResearch.WordTrace tailWord_3226059 prefixEnd_3226059 1104345924508732508684087 := by
  unfold tailWord_3226059
  simp only [CollatzResearch.WordTrace]
  refine ⟨117664038219546684857585231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78442692146364456571723487 117664038219546684857585231)
  ·
    refine ⟨176496057329320027286377847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117664038219546684857585231 176496057329320027286377847)
    ·
      refine ⟨264744085993980040929566771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176496057329320027286377847 264744085993980040929566771)
      ·
        refine ⟨397116128990970061394350157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264744085993980040929566771 397116128990970061394350157)
        ·
          refine ⟨148918548371613773022881309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397116128990970061394350157 148918548371613773022881309)
          ·
            refine ⟨55844455639355164883580491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148918548371613773022881309 55844455639355164883580491)
            ·
              refine ⟨83766683459032747325370737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55844455639355164883580491 83766683459032747325370737)
              ·
                refine ⟨62825012594274560494028053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83766683459032747325370737 62825012594274560494028053)
                ·
                  refine ⟨2944922465356620023157565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62825012594274560494028053 2944922465356620023157565)
                  ·
                    refine ⟨1104345924508732508684087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944922465356620023157565 1104345924508732508684087)
                    ·
                      rfl

theorem cell22_3226059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].length) (baseStart_3226059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226059 prefixEnd_3226059 := by exact prefixLift 3226059
  have htrace : WordTrace (prefixWord ++ tailWord_3226059) baseStart_3226059 baseEnd_3226059 := by
    simpa [prefixWord, tailWord_3226059, baseEnd_3226059] using wordTrace_append hprefix tailTrace_3226059
  have hstable : (prefixWord ++ tailWord_3226059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226059).length < 2 ^ (prefixWord ++ tailWord_3226059).sum := by decide
  have hdescent : baseEnd_3226059 < baseStart_3226059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226074 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_3226074 : Nat := 118140960795 + 3226074 * 2 ^ 59
def prefixEnd_3226074 : Nat := 4983230072969 + 3 ^ 40 * 3226074 * 2
def baseEnd_3226074 : Nat := 1104351059315277469559041

theorem tailTrace_3226074 : CollatzResearch.WordTrace tailWord_3226074 prefixEnd_3226074 1104351059315277469559041 := by
  unfold tailWord_3226074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416146328623085604845319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78443056876328228279587517 29416146328623085604845319)
  ·
    refine ⟨44124219492934628407267979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29416146328623085604845319 44124219492934628407267979)
    ·
      refine ⟨66186329239401942610901969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44124219492934628407267979 66186329239401942610901969)
      ·
        refine ⟨49639746929551456958176477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66186329239401942610901969 49639746929551456958176477)
        ·
          refine ⟨18614905098581796359316179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49639746929551456958176477 18614905098581796359316179)
          ·
            refine ⟨27922357647872694538974269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18614905098581796359316179 27922357647872694538974269)
            ·
              refine ⟨10470884117952260452115351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27922357647872694538974269 10470884117952260452115351)
              ·
                refine ⟨15706326176928390678173027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470884117952260452115351 15706326176928390678173027)
                ·
                  refine ⟨23559489265392586017259541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15706326176928390678173027 23559489265392586017259541)
                  ·
                    refine ⟨1104351059315277469559041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23559489265392586017259541 1104351059315277469559041)
                    ·
                      rfl

theorem cell22_3226074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_3226074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226074 prefixEnd_3226074 := by exact prefixLift 3226074
  have htrace : WordTrace (prefixWord ++ tailWord_3226074) baseStart_3226074 baseEnd_3226074 := by
    simpa [prefixWord, tailWord_3226074, baseEnd_3226074] using wordTrace_append hprefix tailTrace_3226074
  have hstable : (prefixWord ++ tailWord_3226074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226074).length < 2 ^ (prefixWord ++ tailWord_3226074).sum := by decide
  have hdescent : baseEnd_3226074 < baseStart_3226074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226093 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3226093 : Nat := 118140960795 + 3226093 * 2 ^ 59
def prefixEnd_3226093 : Nat := 4983230072969 + 3 ^ 40 * 3226093 * 2
def baseEnd_3226093 : Nat := 1104357563403567753333983

theorem tailTrace_3226093 : CollatzResearch.WordTrace tailWord_3226093 prefixEnd_3226093 1104357563403567753333983 := by
  unfold tailWord_3226093
  simp only [CollatzResearch.WordTrace]
  refine ⟨117665278301423508664322933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78443518867615672442881955 117665278301423508664322933)
  ·
    refine ⟨11031119840758453937280275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117665278301423508664322933 11031119840758453937280275)
    ·
      refine ⟨16546679761137680905920413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031119840758453937280275 16546679761137680905920413)
      ·
        refine ⟨6205004910426630339720155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16546679761137680905920413 6205004910426630339720155)
        ·
          refine ⟨9307507365639945509580233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205004910426630339720155 9307507365639945509580233)
          ·
            refine ⟨6980630524229959132185175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307507365639945509580233 6980630524229959132185175)
            ·
              refine ⟨10470945786344938698277763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980630524229959132185175 10470945786344938698277763)
              ·
                refine ⟨15706418679517408047416645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470945786344938698277763 15706418679517408047416645)
                ·
                  refine ⟨2944953502409514008890621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15706418679517408047416645 2944953502409514008890621)
                  ·
                    refine ⟨1104357563403567753333983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944953502409514008890621 1104357563403567753333983)
                    ·
                      rfl

theorem cell22_3226093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3226093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226093 prefixEnd_3226093 := by exact prefixLift 3226093
  have htrace : WordTrace (prefixWord ++ tailWord_3226093) baseStart_3226093 baseEnd_3226093 := by
    simpa [prefixWord, tailWord_3226093, baseEnd_3226093] using wordTrace_append hprefix tailTrace_3226093
  have hstable : (prefixWord ++ tailWord_3226093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226093).length < 2 ^ (prefixWord ++ tailWord_3226093).sum := by decide
  have hdescent : baseEnd_3226093 < baseStart_3226093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226149 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3226149 : Nat := 118140960795 + 3226149 * 2 ^ 59
def prefixEnd_3226149 : Nat := 4983230072969 + 3 ^ 40 * 3226149 * 2
def baseEnd_3226149 : Nat := 1104376733348002273933811

theorem tailTrace_3226149 : CollatzResearch.WordTrace tailWord_3226149 prefixEnd_3226149 1104376733348002273933811 := by
  unfold tailWord_3226149
  simp only [CollatzResearch.WordTrace]
  refine ⟨117667320789220630228361501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78444880526147086818907667 117667320789220630228361501)
  ·
    refine ⟨44125245295957736335635563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117667320789220630228361501 44125245295957736335635563)
    ·
      refine ⟨66187867943936604503453345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44125245295957736335635563 66187867943936604503453345)
      ·
        refine ⟨49640900957952453377590009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66187867943936604503453345 49640900957952453377590009)
        ·
          refine ⟨37230675718464340033192507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49640900957952453377590009 37230675718464340033192507)
          ·
            refine ⟨55846013577696510049788761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37230675718464340033192507 55846013577696510049788761)
            ·
              refine ⟨41884510183272382537341571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55846013577696510049788761 41884510183272382537341571)
              ·
                refine ⟨62826765274908573806012357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41884510183272382537341571 62826765274908573806012357)
                ·
                  refine ⟨11780018489045357588627317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62826765274908573806012357 11780018489045357588627317)
                  ·
                    refine ⟨1104376733348002273933811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11780018489045357588627317 1104376733348002273933811)
                    ·
                      rfl

theorem cell22_3226149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3226149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226149 prefixEnd_3226149 := by exact prefixLift 3226149
  have htrace : WordTrace (prefixWord ++ tailWord_3226149) baseStart_3226149 baseEnd_3226149 := by
    simpa [prefixWord, tailWord_3226149, baseEnd_3226149] using wordTrace_append hprefix tailTrace_3226149
  have hstable : (prefixWord ++ tailWord_3226149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226149).length < 2 ^ (prefixWord ++ tailWord_3226149).sum := by decide
  have hdescent : baseEnd_3226149 < baseStart_3226149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226179 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 6]
def baseStart_3226179 : Nat := 118140960795 + 3226179 * 2 ^ 59
def prefixEnd_3226179 : Nat := 4983230072969 + 3 ^ 40 * 3226179 * 2
def baseEnd_3226179 : Nat := 368129000987030731894573

theorem tailTrace_3226179 : CollatzResearch.WordTrace tailWord_3226179 prefixEnd_3226179 368129000987030731894573 := by
  unfold tailWord_3226179
  simp only [CollatzResearch.WordTrace]
  refine ⟨117668414979111945351953591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78445609986074630234635727 117668414979111945351953591)
  ·
    refine ⟨176502622468667918027930387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117668414979111945351953591 176502622468667918027930387)
    ·
      refine ⟨264753933703001877041895581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176502622468667918027930387 264753933703001877041895581)
      ·
        refine ⟨99282725138625703890710843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264753933703001877041895581 99282725138625703890710843)
        ·
          refine ⟨148924087707938555836066265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99282725138625703890710843 148924087707938555836066265)
          ·
            refine ⟨111693065780953916877049699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148924087707938555836066265 111693065780953916877049699)
            ·
              refine ⟨167539598671430875315574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111693065780953916877049699 167539598671430875315574549)
              ·
                refine ⟨7853418687723322280417557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167539598671430875315574549 7853418687723322280417557)
                ·
                  refine ⟨368129000987030731894573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7853418687723322280417557 368129000987030731894573)
                  ·
                    rfl

theorem cell22_3226179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_3226179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226179 prefixEnd_3226179 := by exact prefixLift 3226179
  have htrace : WordTrace (prefixWord ++ tailWord_3226179) baseStart_3226179 baseEnd_3226179 := by
    simpa [prefixWord, tailWord_3226179, baseEnd_3226179] using wordTrace_append hprefix tailTrace_3226179
  have hstable : (prefixWord ++ tailWord_3226179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226179).length < 2 ^ (prefixWord ++ tailWord_3226179).sum := by decide
  have hdescent : baseEnd_3226179 < baseStart_3226179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226181 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3226181 : Nat := 118140960795 + 3226181 * 2 ^ 59
def prefixEnd_3226181 : Nat := 4983230072969 + 3 ^ 40 * 3226181 * 2
def baseEnd_3226181 : Nat := 1104387687601964857133713

theorem tailTrace_3226181 : CollatzResearch.WordTrace tailWord_3226181 prefixEnd_3226181 1104387687601964857133713 := by
  unfold tailWord_3226181
  simp only [CollatzResearch.WordTrace]
  refine ⟨117668487925104699693526397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78445658616736466462350931 117668487925104699693526397)
  ·
    refine ⟨44125682971914262385072399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117668487925104699693526397 44125682971914262385072399)
    ·
      refine ⟨66188524457871393577608599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44125682971914262385072399 66188524457871393577608599)
      ·
        refine ⟨99282786686807090366412899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66188524457871393577608599 99282786686807090366412899)
        ·
          refine ⟨148924180030210635549619349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99282786686807090366412899 148924180030210635549619349)
          ·
            refine ⟨6980820938916123541388407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148924180030210635549619349 6980820938916123541388407)
            ·
              refine ⟨10471231408374185312082611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980820938916123541388407 10471231408374185312082611)
              ·
                refine ⟨15706847112561277968123917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471231408374185312082611 15706847112561277968123917)
                ·
                  refine ⟨5890067667210479238046469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15706847112561277968123917 5890067667210479238046469)
                  ·
                    refine ⟨1104387687601964857133713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890067667210479238046469 1104387687601964857133713)
                    ·
                      rfl

theorem cell22_3226181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3226181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226181 prefixEnd_3226181 := by exact prefixLift 3226181
  have htrace : WordTrace (prefixWord ++ tailWord_3226181) baseStart_3226181 baseEnd_3226181 := by
    simpa [prefixWord, tailWord_3226181, baseEnd_3226181] using wordTrace_append hprefix tailTrace_3226181
  have hstable : (prefixWord ++ tailWord_3226181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226181).length < 2 ^ (prefixWord ++ tailWord_3226181).sum := by decide
  have hdescent : baseEnd_3226181 < baseStart_3226181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226206 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3226206 : Nat := 118140960795 + 3226206 * 2 ^ 59
def prefixEnd_3226206 : Nat := 4983230072969 + 3 ^ 40 * 3226206 * 2
def baseEnd_3226206 : Nat := 1104396245612873125258637

theorem tailTrace_3226206 : CollatzResearch.WordTrace tailWord_3226206 prefixEnd_3226206 1104396245612873125258637 := by
  unfold tailWord_3226206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708674968751766120398309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78446266500009419308790981 14708674968751766120398309)
  ·
    refine ⟨2757876556640956147574683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14708674968751766120398309 2757876556640956147574683)
    ·
      refine ⟨4136814834961434221362025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757876556640956147574683 4136814834961434221362025)
      ·
        refine ⟨3102611126221075666021519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136814834961434221362025 3102611126221075666021519)
        ·
          refine ⟨4653916689331613499032279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102611126221075666021519 4653916689331613499032279)
          ·
            refine ⟨6980875033997420248548419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653916689331613499032279 6980875033997420248548419)
            ·
              refine ⟨10471312550996130372822629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980875033997420248548419 10471312550996130372822629)
              ·
                refine ⟨1963371103311774444904243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10471312550996130372822629 1963371103311774444904243)
                ·
                  refine ⟨2945056654967661667356365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963371103311774444904243 2945056654967661667356365)
                  ·
                    refine ⟨1104396245612873125258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945056654967661667356365 1104396245612873125258637)
                    ·
                      rfl

theorem cell22_3226206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3226206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226206 prefixEnd_3226206 := by exact prefixLift 3226206
  have htrace : WordTrace (prefixWord ++ tailWord_3226206) baseStart_3226206 baseEnd_3226206 := by
    simpa [prefixWord, tailWord_3226206, baseEnd_3226206] using wordTrace_append hprefix tailTrace_3226206
  have hstable : (prefixWord ++ tailWord_3226206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226206).length < 2 ^ (prefixWord ++ tailWord_3226206).sum := by decide
  have hdescent : baseEnd_3226206 < baseStart_3226206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_3226239 : Nat := 118140960795 + 3226239 * 2 ^ 59
def prefixEnd_3226239 : Nat := 4983230072969 + 3 ^ 40 * 3226239 * 2
def baseEnd_3226239 : Nat := 1104407542187272039183535

theorem tailTrace_3226239 : CollatzResearch.WordTrace tailWord_3226239 prefixEnd_3226239 1104407542187272039183535 := by
  unfold tailWord_3226239
  simp only [CollatzResearch.WordTrace]
  refine ⟨117670603358894575599137771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78447068905929717066091847 117670603358894575599137771)
  ·
    refine ⟨176505905038341863398706657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117670603358894575599137771 176505905038341863398706657)
    ·
      refine ⟨132379428778756397549029993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176505905038341863398706657 132379428778756397549029993)
      ·
        refine ⟨99284571584067298161772495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132379428778756397549029993 99284571584067298161772495)
        ·
          refine ⟨148926857376100947242658743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99284571584067298161772495 148926857376100947242658743)
          ·
            refine ⟨223390286064151420863988115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148926857376100947242658743 223390286064151420863988115)
            ·
              refine ⟨335085429096227131295982173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223390286064151420863988115 335085429096227131295982173)
              ·
                refine ⟨125657035911085174235993315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335085429096227131295982173 125657035911085174235993315)
                ·
                  refine ⟨188485553866627761353989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125657035911085174235993315 188485553866627761353989973)
                  ·
                    refine ⟨1104407542187272039183535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188485553866627761353989973 1104407542187272039183535)
                    ·
                      rfl

theorem cell22_3226239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_3226239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226239 prefixEnd_3226239 := by exact prefixLift 3226239
  have htrace : WordTrace (prefixWord ++ tailWord_3226239) baseStart_3226239 baseEnd_3226239 := by
    simpa [prefixWord, tailWord_3226239, baseEnd_3226239] using wordTrace_append hprefix tailTrace_3226239
  have hstable : (prefixWord ++ tailWord_3226239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226239).length < 2 ^ (prefixWord ++ tailWord_3226239).sum := by decide
  have hdescent : baseEnd_3226239 < baseStart_3226239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226279 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3226279 : Nat := 118140960795 + 3226279 * 2 ^ 59
def prefixEnd_3226279 : Nat := 4983230072969 + 3 ^ 40 * 3226279 * 2
def baseEnd_3226279 : Nat := 1104421235004725268183413

theorem tailTrace_3226279 : CollatzResearch.WordTrace tailWord_3226279 prefixEnd_3226279 1104421235004725268183413 := by
  unfold tailWord_3226279
  simp only [CollatzResearch.WordTrace]
  refine ⟨117672062278749662430593891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78448041519166441620395927 117672062278749662430593891)
  ·
    refine ⟨176508093418124493645890837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117672062278749662430593891 176508093418124493645890837)
    ·
      refine ⟨8273816878974585639651133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176508093418124493645890837 8273816878974585639651133)
      ·
        refine ⟨3102681329615469614869175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8273816878974585639651133 3102681329615469614869175)
        ·
          refine ⟨4654021994423204422303763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102681329615469614869175 4654021994423204422303763)
          ·
            refine ⟨6981032991634806633455645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654021994423204422303763 6981032991634806633455645)
            ·
              refine ⟨2617887371863052487545867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6981032991634806633455645 2617887371863052487545867)
              ·
                refine ⟨3926831057794578731318801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617887371863052487545867 3926831057794578731318801)
                ·
                  refine ⟨2945123293345934048489101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926831057794578731318801 2945123293345934048489101)
                  ·
                    refine ⟨1104421235004725268183413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945123293345934048489101 1104421235004725268183413)
                    ·
                      rfl

theorem cell22_3226279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3226279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226279 prefixEnd_3226279 := by exact prefixLift 3226279
  have htrace : WordTrace (prefixWord ++ tailWord_3226279) baseStart_3226279 baseEnd_3226279 := by
    simpa [prefixWord, tailWord_3226279, baseEnd_3226279] using wordTrace_append hprefix tailTrace_3226279
  have hstable : (prefixWord ++ tailWord_3226279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226279).length < 2 ^ (prefixWord ++ tailWord_3226279).sum := by decide
  have hdescent : baseEnd_3226279 < baseStart_3226279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226324 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3226324 : Nat := 118140960795 + 3226324 * 2 ^ 59
def prefixEnd_3226324 : Nat := 4983230072969 + 3 ^ 40 * 3226324 * 2
def baseEnd_3226324 : Nat := 1104436639424360150808275

theorem tailTrace_3226324 : CollatzResearch.WordTrace tailWord_3226324 prefixEnd_3226324 1104436639424360150808275 := by
  unfold tailWord_3226324
  simp only [CollatzResearch.WordTrace]
  refine ⟨58836851781793317557991013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78449135709057756743988017 58836851781793317557991013)
  ·
    refine ⟨11031909709086247042123315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58836851781793317557991013 11031909709086247042123315)
    ·
      refine ⟨16547864563629370563184973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031909709086247042123315 16547864563629370563184973)
      ·
        refine ⟨6205449211361013961194365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16547864563629370563184973 6205449211361013961194365)
        ·
          refine ⟨2327043454260380235447887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6205449211361013961194365 2327043454260380235447887)
          ·
            refine ⟨3490565181390570353171831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327043454260380235447887 3490565181390570353171831)
            ·
              refine ⟨5235847772085855529757747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490565181390570353171831 5235847772085855529757747)
              ·
                refine ⟨7853771658128783294636621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235847772085855529757747 7853771658128783294636621)
                ·
                  refine ⟨2945164371798293735488733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7853771658128783294636621 2945164371798293735488733)
                  ·
                    refine ⟨1104436639424360150808275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945164371798293735488733 1104436639424360150808275)
                    ·
                      rfl

theorem cell22_3226324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3226324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226324 prefixEnd_3226324 := by exact prefixLift 3226324
  have htrace : WordTrace (prefixWord ++ tailWord_3226324) baseStart_3226324 baseEnd_3226324 := by
    simpa [prefixWord, tailWord_3226324, baseEnd_3226324] using wordTrace_append hprefix tailTrace_3226324
  have hstable : (prefixWord ++ tailWord_3226324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226324).length < 2 ^ (prefixWord ++ tailWord_3226324).sum := by decide
  have hdescent : baseEnd_3226324 < baseStart_3226324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226350 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3226350 : Nat := 118140960795 + 3226350 * 2 ^ 59
def prefixEnd_3226350 : Nat := 4983230072969 + 3 ^ 40 * 3226350 * 2
def baseEnd_3226350 : Nat := 1104445539755704749658195

theorem tailTrace_3226350 : CollatzResearch.WordTrace tailWord_3226350 prefixEnd_3226350 1104445539755704749658195 := by
  unfold tailWord_3226350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709331482686555194553563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78449767907661627704285669 14709331482686555194553563)
  ·
    refine ⟨22063997224029832791830345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14709331482686555194553563 22063997224029832791830345)
    ·
      refine ⟨16547997918022374593872759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22063997224029832791830345 16547997918022374593872759)
      ·
        refine ⟨24821996877033561890809139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547997918022374593872759 24821996877033561890809139)
        ·
          refine ⟨37232995315550342836213709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24821996877033561890809139 37232995315550342836213709)
          ·
            refine ⟨13962373243331378563580141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37232995315550342836213709 13962373243331378563580141)
            ·
              refine ⟨5235889966249266961342553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13962373243331378563580141 5235889966249266961342553)
              ·
                refine ⟨3926917474686950221006915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5235889966249266961342553 3926917474686950221006915)
                ·
                  refine ⟨5890376212030425331510373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926917474686950221006915 5890376212030425331510373)
                  ·
                    refine ⟨1104445539755704749658195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890376212030425331510373 1104445539755704749658195)
                    ·
                      rfl

theorem cell22_3226350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3226350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226350 prefixEnd_3226350 := by exact prefixLift 3226350
  have htrace : WordTrace (prefixWord ++ tailWord_3226350) baseStart_3226350 baseEnd_3226350 := by
    simpa [prefixWord, tailWord_3226350, baseEnd_3226350] using wordTrace_append hprefix tailTrace_3226350
  have hstable : (prefixWord ++ tailWord_3226350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226350).length < 2 ^ (prefixWord ++ tailWord_3226350).sum := by decide
  have hdescent : baseEnd_3226350 < baseStart_3226350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226361 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3226361 : Nat := 118140960795 + 3226361 * 2 ^ 59
def prefixEnd_3226361 : Nat := 4983230072969 + 3 ^ 40 * 3226361 * 2
def baseEnd_3226361 : Nat := 1104449305280504387633161

theorem tailTrace_3226361 : CollatzResearch.WordTrace tailWord_3226361 prefixEnd_3226361 1104449305280504387633161 := by
  unfold tailWord_3226361
  simp only [CollatzResearch.WordTrace]
  refine ⟨117675053064452590435078937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78450035376301726956719291 117675053064452590435078937)
  ·
    refine ⟨88256289798339442826309203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117675053064452590435078937 88256289798339442826309203)
    ·
      refine ⟨132384434697509164239463805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88256289798339442826309203 132384434697509164239463805)
      ·
        refine ⟨49644163011565936589798927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132384434697509164239463805 49644163011565936589798927)
        ·
          refine ⟨74466244517348904884698391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49644163011565936589798927 74466244517348904884698391)
          ·
            refine ⟨111699366776023357327047587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74466244517348904884698391 111699366776023357327047587)
            ·
              refine ⟨167549050164035035990571381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111699366776023357327047587 167549050164035035990571381)
              ·
                refine ⟨15707723452878284624116067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167549050164035035990571381 15707723452878284624116067)
                ·
                  refine ⟨23561585179317426936174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15707723452878284624116067 23561585179317426936174101)
                  ·
                    refine ⟨1104449305280504387633161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23561585179317426936174101 1104449305280504387633161)
                    ·
                      rfl

theorem cell22_3226361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3226361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226361 prefixEnd_3226361 := by exact prefixLift 3226361
  have htrace : WordTrace (prefixWord ++ tailWord_3226361) baseStart_3226361 baseEnd_3226361 := by
    simpa [prefixWord, tailWord_3226361, baseEnd_3226361] using wordTrace_append hprefix tailTrace_3226361
  have hstable : (prefixWord ++ tailWord_3226361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226361).length < 2 ^ (prefixWord ++ tailWord_3226361).sum := by decide
  have hdescent : baseEnd_3226361 < baseStart_3226361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226376 : List Nat := [2, 1, 3, 2, 2, 12]
def baseStart_3226376 : Nat := 118140960795 + 3226376 * 2 ^ 59
def prefixEnd_3226376 : Nat := 4983230072969 + 3 ^ 40 * 3226376 * 2
def baseEnd_3226376 : Nat := 13635240001074683314915

theorem tailTrace_3226376 : CollatzResearch.WordTrace tailWord_3226376 prefixEnd_3226376 13635240001074683314915 := by
  unfold tailWord_3226376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58837800079699123998437491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78450400106265498664583321 58837800079699123998437491)
  ·
    refine ⟨88256700119548685997656237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58837800079699123998437491 88256700119548685997656237)
    ·
      refine ⟨33096262544830757249121089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88256700119548685997656237 33096262544830757249121089)
      ·
        refine ⟨24822196908623067936840817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33096262544830757249121089 24822196908623067936840817)
        ·
          refine ⟨18616647681467300952630613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24822196908623067936840817 18616647681467300952630613)
          ·
            refine ⟨13635240001074683314915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18616647681467300952630613 13635240001074683314915)
            ·
              rfl

theorem cell22_3226376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 12].length) (baseStart_3226376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226376 prefixEnd_3226376 := by exact prefixLift 3226376
  have htrace : WordTrace (prefixWord ++ tailWord_3226376) baseStart_3226376 baseEnd_3226376 := by
    simpa [prefixWord, tailWord_3226376, baseEnd_3226376] using wordTrace_append hprefix tailTrace_3226376
  have hstable : (prefixWord ++ tailWord_3226376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226376).length < 2 ^ (prefixWord ++ tailWord_3226376).sum := by decide
  have hdescent : baseEnd_3226376 < baseStart_3226376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226378 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_3226378 : Nat := 118140960795 + 3226378 * 2 ^ 59
def prefixEnd_3226378 : Nat := 4983230072969 + 3 ^ 40 * 3226378 * 2
def baseEnd_3226378 : Nat := 1104455124727922009958109

theorem tailTrace_3226378 : CollatzResearch.WordTrace tailWord_3226378 prefixEnd_3226378 1104455124727922009958109 := by
  unfold tailWord_3226378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29418918276347750584611947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78450448736927334892298525 29418918276347750584611947)
  ·
    refine ⟨44128377414521625876917921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29418918276347750584611947 44128377414521625876917921)
    ·
      refine ⟨33096283060891219407688441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44128377414521625876917921 33096283060891219407688441)
      ·
        refine ⟨24822212295668414555766331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33096283060891219407688441 24822212295668414555766331)
        ·
          refine ⟨37233318443502621833649497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24822212295668414555766331 37233318443502621833649497)
          ·
            refine ⟨27924988832626966375237123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37233318443502621833649497 27924988832626966375237123)
            ·
              refine ⟨41887483248940449562855685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27924988832626966375237123 41887483248940449562855685)
              ·
                refine ⟨7853903109176334293035441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41887483248940449562855685 7853903109176334293035441)
                ·
                  refine ⟨5890427331882250719776581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853903109176334293035441 5890427331882250719776581)
                  ·
                    refine ⟨1104455124727922009958109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890427331882250719776581 1104455124727922009958109)
                    ·
                      rfl

theorem cell22_3226378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_3226378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226378 prefixEnd_3226378 := by exact prefixLift 3226378
  have htrace : WordTrace (prefixWord ++ tailWord_3226378) baseStart_3226378 baseEnd_3226378 := by
    simpa [prefixWord, tailWord_3226378, baseEnd_3226378] using wordTrace_append hprefix tailTrace_3226378
  have hstable : (prefixWord ++ tailWord_3226378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226378).length < 2 ^ (prefixWord ++ tailWord_3226378).sum := by decide
  have hdescent : baseEnd_3226378 < baseStart_3226378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226397 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3226397 : Nat := 118140960795 + 3226397 * 2 ^ 59
def prefixEnd_3226397 : Nat := 4983230072969 + 3 ^ 40 * 3226397 * 2
def baseEnd_3226397 : Nat := 1104461628816212293733051

theorem tailTrace_3226397 : CollatzResearch.WordTrace tailWord_3226397 prefixEnd_3226397 1104461628816212293733051 := by
  unfold tailWord_3226397
  simp only [CollatzResearch.WordTrace]
  refine ⟨117676366092322168583389445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78450910728214779055592963 117676366092322168583389445)
  ·
    refine ⟨22064318642310406609385521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117676366092322168583389445 22064318642310406609385521)
    ·
      refine ⟨16548238981732804957039141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22064318642310406609385521 16548238981732804957039141)
      ·
        refine ⟨3102794809074900929444839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16548238981732804957039141 3102794809074900929444839)
        ·
          refine ⟨4654192213612351394167259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102794809074900929444839 4654192213612351394167259)
          ·
            refine ⟨6981288320418527091250889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654192213612351394167259 6981288320418527091250889)
            ·
              refine ⟨5235966240313895318438167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6981288320418527091250889 5235966240313895318438167)
              ·
                refine ⟨7853949360470842977657251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235966240313895318438167 7853949360470842977657251)
                ·
                  refine ⟨11780924040706264466485877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853949360470842977657251 11780924040706264466485877)
                  ·
                    refine ⟨1104461628816212293733051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11780924040706264466485877 1104461628816212293733051)
                    ·
                      rfl

theorem cell22_3226397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3226397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226397 prefixEnd_3226397 := by exact prefixLift 3226397
  have htrace : WordTrace (prefixWord ++ tailWord_3226397) baseStart_3226397 baseEnd_3226397 := by
    simpa [prefixWord, tailWord_3226397, baseEnd_3226397] using wordTrace_append hprefix tailTrace_3226397
  have hstable : (prefixWord ++ tailWord_3226397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226397).length < 2 ^ (prefixWord ++ tailWord_3226397).sum := by decide
  have hdescent : baseEnd_3226397 < baseStart_3226397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226453 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3226453 : Nat := 118140960795 + 3226453 * 2 ^ 59
def prefixEnd_3226453 : Nat := 4983230072969 + 3 ^ 40 * 3226453 * 2
def baseEnd_3226453 : Nat := 1104480798760646814332879

theorem tailTrace_3226453 : CollatzResearch.WordTrace tailWord_3226453 prefixEnd_3226453 1104480798760646814332879 := by
  unfold tailWord_3226453
  simp only [CollatzResearch.WordTrace]
  refine ⟨117678408580119290147428013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78452272386746193431618675 117678408580119290147428013)
  ·
    refine ⟨44129403217544733805285505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117678408580119290147428013 44129403217544733805285505)
    ·
      refine ⟨33097052413158550353964129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44129403217544733805285505 33097052413158550353964129)
      ·
        refine ⟨24822789309868912765473097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33097052413158550353964129 24822789309868912765473097)
        ·
          refine ⟨18617091982401684574104823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24822789309868912765473097 18617091982401684574104823)
          ·
            refine ⟨27925637973602526861157235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18617091982401684574104823 27925637973602526861157235)
            ·
              refine ⟨41888456960403790291735853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27925637973602526861157235 41888456960403790291735853)
              ·
                refine ⟨15708171360151421359400945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41888456960403790291735853 15708171360151421359400945)
                ·
                  refine ⟨11781128520113566019550709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15708171360151421359400945 11781128520113566019550709)
                  ·
                    refine ⟨1104480798760646814332879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11781128520113566019550709 1104480798760646814332879)
                    ·
                      rfl

theorem cell22_3226453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3226453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226453 prefixEnd_3226453 := by exact prefixLift 3226453
  have htrace : WordTrace (prefixWord ++ tailWord_3226453) baseStart_3226453 baseEnd_3226453 := by
    simpa [prefixWord, tailWord_3226453, baseEnd_3226453] using wordTrace_append hprefix tailTrace_3226453
  have hstable : (prefixWord ++ tailWord_3226453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226453).length < 2 ^ (prefixWord ++ tailWord_3226453).sum := by decide
  have hdescent : baseEnd_3226453 < baseStart_3226453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3226513 : Nat := 118140960795 + 3226513 * 2 ^ 59
def prefixEnd_3226513 : Nat := 4983230072969 + 3 ^ 40 * 3226513 * 2
def baseEnd_3226513 : Nat := 1104501337986826657832695

theorem tailTrace_3226513 : CollatzResearch.WordTrace tailWord_3226513 prefixEnd_3226513 1104501337986826657832695 := by
  unfold tailWord_3226513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117680596959901920394612193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78453731306601280263074795 117680596959901920394612193)
  ·
    refine ⟨88260447719926440295959145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117680596959901920394612193 88260447719926440295959145)
    ·
      refine ⟨66195335789944830221969359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88260447719926440295959145 66195335789944830221969359)
      ·
        refine ⟨99293003684917245332954039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66195335789944830221969359 99293003684917245332954039)
        ·
          refine ⟨148939505527375867999431059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99293003684917245332954039 148939505527375867999431059)
          ·
            refine ⟨223409258291063801999146589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148939505527375867999431059 223409258291063801999146589)
            ·
              refine ⟨83778471859148925749679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223409258291063801999146589 83778471859148925749679971)
              ·
                refine ⟨125667707788723388624519957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83778471859148925749679971 125667707788723388624519957)
                ·
                  refine ⟨5890673802596408841774373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125667707788723388624519957 5890673802596408841774373)
                  ·
                    refine ⟨1104501337986826657832695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890673802596408841774373 1104501337986826657832695)
                    ·
                      rfl

theorem cell22_3226513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3226513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226513 prefixEnd_3226513 := by exact prefixLift 3226513
  have htrace : WordTrace (prefixWord ++ tailWord_3226513) baseStart_3226513 baseEnd_3226513 := by
    simpa [prefixWord, tailWord_3226513, baseEnd_3226513] using wordTrace_append hprefix tailTrace_3226513
  have hstable : (prefixWord ++ tailWord_3226513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226513).length < 2 ^ (prefixWord ++ tailWord_3226513).sum := by decide
  have hdescent : baseEnd_3226513 < baseStart_3226513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226528 : List Nat := [2, 1, 1, 4, 1, 1, 4, 8]
def baseStart_3226528 : Nat := 118140960795 + 3226528 * 2 ^ 59
def prefixEnd_3226528 : Nat := 4983230072969 + 3 ^ 40 * 3226528 * 2
def baseEnd_3226528 : Nat := 122722941421485735411961

theorem tailTrace_3226528 : CollatzResearch.WordTrace tailWord_3226528 prefixEnd_3226528 122722941421485735411961 := by
  unfold tailWord_3226528
  simp only [CollatzResearch.WordTrace]
  refine ⟨58840572027423788978204119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78454096036565051970938825 58840572027423788978204119)
  ·
    refine ⟨88260858041135683467306179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58840572027423788978204119 88260858041135683467306179)
    ·
      refine ⟨132391287061703525200959269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88260858041135683467306179 132391287061703525200959269)
      ·
        refine ⟨24823366324069410975179863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132391287061703525200959269 24823366324069410975179863)
        ·
          refine ⟨37235049486104116462769795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24823366324069410975179863 37235049486104116462769795)
          ·
            refine ⟨55852574229156174694154693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37235049486104116462769795 55852574229156174694154693)
            ·
              refine ⟨10472357667966782755154005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55852574229156174694154693 10472357667966782755154005)
              ·
                refine ⟨122722941421485735411961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10472357667966782755154005 122722941421485735411961)
                ·
                  rfl

theorem cell22_3226528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_3226528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226528 prefixEnd_3226528 := by exact prefixLift 3226528
  have htrace : WordTrace (prefixWord ++ tailWord_3226528) baseStart_3226528 baseEnd_3226528 := by
    simpa [prefixWord, tailWord_3226528, baseEnd_3226528] using wordTrace_append hprefix tailTrace_3226528
  have hstable : (prefixWord ++ tailWord_3226528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226528).length < 2 ^ (prefixWord ++ tailWord_3226528).sum := by decide
  have hdescent : baseEnd_3226528 < baseStart_3226528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226545 : List Nat := [1, 2, 2, 4, 4, 9]
def baseStart_3226545 : Nat := 118140960795 + 3226545 * 2 ^ 59
def prefixEnd_3226545 : Nat := 4983230072969 + 3 ^ 40 * 3226545 * 2
def baseEnd_3226545 : Nat := 13635954225194928901637

theorem tailTrace_3226545 : CollatzResearch.WordTrace tailWord_3226545 prefixEnd_3226545 13635954225194928901637 := by
  unfold tailWord_3226545
  simp only [CollatzResearch.WordTrace]
  refine ⟨117681764095785989859777089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78454509397190659906518059 117681764095785989859777089)
  ·
    refine ⟨88261323071839492394832817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117681764095785989859777089 88261323071839492394832817)
    ·
      refine ⟨66195992303879619296124613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88261323071839492394832817 66195992303879619296124613)
      ·
        refine ⟨12411748556977428618023365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66195992303879619296124613 12411748556977428618023365)
        ·
          refine ⟨2327202854433267865879381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12411748556977428618023365 2327202854433267865879381)
          ·
            refine ⟨13635954225194928901637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2327202854433267865879381 13635954225194928901637)
            ·
              rfl

theorem cell22_3226545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 9].length) (baseStart_3226545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226545 prefixEnd_3226545 := by exact prefixLift 3226545
  have htrace : WordTrace (prefixWord ++ tailWord_3226545) baseStart_3226545 baseEnd_3226545 := by
    simpa [prefixWord, tailWord_3226545, baseEnd_3226545] using wordTrace_append hprefix tailTrace_3226545
  have hstable : (prefixWord ++ tailWord_3226545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226545).length < 2 ^ (prefixWord ++ tailWord_3226545).sum := by decide
  have hdescent : baseEnd_3226545 < baseStart_3226545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226607 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 5]
def baseStart_3226607 : Nat := 118140960795 + 3226607 * 2 ^ 59
def prefixEnd_3226607 : Nat := 4983230072969 + 3 ^ 40 * 3226607 * 2
def baseEnd_3226607 : Nat := 368177838702613915327469

theorem tailTrace_3226607 : CollatzResearch.WordTrace tailWord_3226607 prefixEnd_3226607 368177838702613915327469 := by
  unfold tailWord_3226607
  simp only [CollatzResearch.WordTrace]
  refine ⟨117684025421561374448534075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78456016947707582965689383 117684025421561374448534075)
  ·
    refine ⟨176526038132342061672801113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117684025421561374448534075 176526038132342061672801113)
    ·
      refine ⟨132394528599256546254600835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176526038132342061672801113 132394528599256546254600835)
      ·
        refine ⟨198591792898884819381901253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132394528599256546254600835 198591792898884819381901253)
        ·
          refine ⟨37235961168540903634106485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198591792898884819381901253 37235961168540903634106485)
          ·
            refine ⟨3490871359550709715697483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37235961168540903634106485 3490871359550709715697483)
            ·
              refine ⟨5236307039326064573546225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490871359550709715697483 5236307039326064573546225)
              ·
                refine ⟨3927230279494548430159669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5236307039326064573546225 3927230279494548430159669)
                ·
                  refine ⟨368177838702613915327469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927230279494548430159669 368177838702613915327469)
                  ·
                    rfl

theorem cell22_3226607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].length) (baseStart_3226607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226607 prefixEnd_3226607 := by exact prefixLift 3226607
  have htrace : WordTrace (prefixWord ++ tailWord_3226607) baseStart_3226607 baseEnd_3226607 := by
    simpa [prefixWord, tailWord_3226607, baseEnd_3226607] using wordTrace_append hprefix tailTrace_3226607
  have hstable : (prefixWord ++ tailWord_3226607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226607).length < 2 ^ (prefixWord ++ tailWord_3226607).sum := by decide
  have hdescent : baseEnd_3226607 < baseStart_3226607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226635 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 6]
def baseStart_3226635 : Nat := 118140960795 + 3226635 * 2 ^ 59
def prefixEnd_3226635 : Nat := 4983230072969 + 3 ^ 40 * 3226635 * 2
def baseEnd_3226635 : Nat := 368181033693353002094107

theorem tailTrace_3226635 : CollatzResearch.WordTrace tailWord_3226635 prefixEnd_3226635 368181033693353002094107 := by
  unfold tailWord_3226635
  simp only [CollatzResearch.WordTrace]
  refine ⟨117685046665459935230553359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78456697776973290153702239 117685046665459935230553359)
  ·
    refine ⟨176527569998189902845830039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117685046665459935230553359 176527569998189902845830039)
    ·
      refine ⟨264791354997284854268745059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176527569998189902845830039 264791354997284854268745059)
      ·
        refine ⟨397187032495927281403117589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264791354997284854268745059 397187032495927281403117589)
        ·
          refine ⟨18618142148246591315771137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 397187032495927281403117589 18618142148246591315771137)
          ·
            refine ⟨13963606611184943486828353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18618142148246591315771137 13963606611184943486828353)
            ·
              refine ⟨10472704958388707615121265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13963606611184943486828353 10472704958388707615121265)
              ·
                refine ⟨7854528718791530711340949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10472704958388707615121265 7854528718791530711340949)
                ·
                  refine ⟨368181033693353002094107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7854528718791530711340949 368181033693353002094107)
                  ·
                    rfl

theorem cell22_3226635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_3226635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226635 prefixEnd_3226635 := by exact prefixLift 3226635
  have htrace : WordTrace (prefixWord ++ tailWord_3226635) baseStart_3226635 baseEnd_3226635 := by
    simpa [prefixWord, tailWord_3226635, baseEnd_3226635] using wordTrace_append hprefix tailTrace_3226635
  have hstable : (prefixWord ++ tailWord_3226635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226635).length < 2 ^ (prefixWord ++ tailWord_3226635).sum := by decide
  have hdescent : baseEnd_3226635 < baseStart_3226635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226650 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_3226650 : Nat := 118140960795 + 3226650 * 2 ^ 59
def prefixEnd_3226650 : Nat := 4983230072969 + 3 ^ 40 * 3226650 * 2
def baseEnd_3226650 : Nat := 1104548235886603967157275

theorem tailTrace_3226650 : CollatzResearch.WordTrace tailWord_3226650 prefixEnd_3226650 1104548235886603967157275 := by
  unfold tailWord_3226650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29421398440101398198087351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78457062506937061861566269 29421398440101398198087351)
  ·
    refine ⟨44132097660152097297131027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29421398440101398198087351 44132097660152097297131027)
    ·
      refine ⟨66198146490228145945696541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44132097660152097297131027 66198146490228145945696541)
      ·
        refine ⟨24824304933835554729636203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66198146490228145945696541 24824304933835554729636203)
        ·
          refine ⟨37236457400753332094454305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24824304933835554729636203 37236457400753332094454305)
          ·
            refine ⟨27927343050564999070840729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37236457400753332094454305 27927343050564999070840729)
            ·
              refine ⟨20945507287923749303130547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27927343050564999070840729 20945507287923749303130547)
              ·
                refine ⟨31418260931885623954695821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20945507287923749303130547 31418260931885623954695821)
                ·
                  refine ⟨11781847849457108983010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31418260931885623954695821 11781847849457108983010933)
                  ·
                    refine ⟨1104548235886603967157275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11781847849457108983010933 1104548235886603967157275)
                    ·
                      rfl

theorem cell22_3226650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_3226650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226650 prefixEnd_3226650 := by exact prefixLift 3226650
  have htrace : WordTrace (prefixWord ++ tailWord_3226650) baseStart_3226650 baseEnd_3226650 := by
    simpa [prefixWord, tailWord_3226650, baseEnd_3226650] using wordTrace_append hprefix tailTrace_3226650
  have hstable : (prefixWord ++ tailWord_3226650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226650).length < 2 ^ (prefixWord ++ tailWord_3226650).sum := by decide
  have hdescent : baseEnd_3226650 < baseStart_3226650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226667 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 2, 3]
def baseStart_3226667 : Nat := 118140960795 + 3226667 * 2 ^ 59
def prefixEnd_3226667 : Nat := 4983230072969 + 3 ^ 40 * 3226667 * 2
def baseEnd_3226667 : Nat := 1104554055334021589482223

theorem tailTrace_3226667 : CollatzResearch.WordTrace tailWord_3226667 prefixEnd_3226667 1104554055334021589482223 := by
  unfold tailWord_3226667
  simp only [CollatzResearch.WordTrace]
  refine ⟨117686213801344004695718255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78457475867562669797145503 117686213801344004695718255)
  ·
    refine ⟨176529320702016007043577383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117686213801344004695718255 176529320702016007043577383)
    ·
      refine ⟨264793981053024010565366075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176529320702016007043577383 264793981053024010565366075)
      ·
        refine ⟨397190971579536015848049113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264793981053024010565366075 397190971579536015848049113)
        ·
          refine ⟨297893228684652011886036835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397190971579536015848049113 297893228684652011886036835)
          ·
            refine ⟨446839843026978017829055253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297893228684652011886036835 446839843026978017829055253)
            ·
              refine ⟨20945617641889594585736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 446839843026978017829055253 20945617641889594585736965)
              ·
                refine ⟨3927303307854298984825681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20945617641889594585736965 3927303307854298984825681)
                ·
                  refine ⟨2945477480890724238619261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927303307854298984825681 2945477480890724238619261)
                  ·
                    refine ⟨1104554055334021589482223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945477480890724238619261 1104554055334021589482223)
                    ·
                      rfl

theorem cell22_3226667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].length) (baseStart_3226667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226667 prefixEnd_3226667 := by exact prefixLift 3226667
  have htrace : WordTrace (prefixWord ++ tailWord_3226667) baseStart_3226667 baseEnd_3226667 := by
    simpa [prefixWord, tailWord_3226667, baseEnd_3226667] using wordTrace_append hprefix tailTrace_3226667
  have hstable : (prefixWord ++ tailWord_3226667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226667).length < 2 ^ (prefixWord ++ tailWord_3226667).sum := by decide
  have hdescent : baseEnd_3226667 < baseStart_3226667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226680 : List Nat := [2, 1, 2, 1, 5, 1, 1, 9]
def baseStart_3226680 : Nat := 118140960795 + 3226680 * 2 ^ 59
def prefixEnd_3226680 : Nat := 4983230072969 + 3 ^ 40 * 3226680 * 2
def baseEnd_3226680 : Nat := 122728722833299320989687

theorem tailTrace_3226680 : CollatzResearch.WordTrace tailWord_3226680 prefixEnd_3226680 122728722833299320989687 := by
  unfold tailWord_3226680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58843343975148453957970747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78457791966864605277294329 58843343975148453957970747)
  ·
    refine ⟨88265015962722680936956121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58843343975148453957970747 88265015962722680936956121)
    ·
      refine ⟨66198761972042010702717091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88265015962722680936956121 66198761972042010702717091)
      ·
        refine ⟨99298142958063016054075637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66198761972042010702717091 99298142958063016054075637)
        ·
          refine ⟨9309200902318407755069591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99298142958063016054075637 9309200902318407755069591)
          ·
            refine ⟨13963801353477611632604387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309200902318407755069591 13963801353477611632604387)
            ·
              refine ⟨20945702030216417448906581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13963801353477611632604387 20945702030216417448906581)
              ·
                refine ⟨122728722833299320989687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20945702030216417448906581 122728722833299320989687)
                ·
                  rfl

theorem cell22_3226680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_3226680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226680 prefixEnd_3226680 := by exact prefixLift 3226680
  have htrace : WordTrace (prefixWord ++ tailWord_3226680) baseStart_3226680 baseEnd_3226680 := by
    simpa [prefixWord, tailWord_3226680, baseEnd_3226680] using wordTrace_append hprefix tailTrace_3226680
  have hstable : (prefixWord ++ tailWord_3226680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226680).length < 2 ^ (prefixWord ++ tailWord_3226680).sum := by decide
  have hdescent : baseEnd_3226680 < baseStart_3226680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226684 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3226684 : Nat := 118140960795 + 3226684 * 2 ^ 59
def prefixEnd_3226684 : Nat := 4983230072969 + 3 ^ 40 * 3226684 * 2
def baseEnd_3226684 : Nat := 1104559874781439211807171

theorem tailTrace_3226684 : CollatzResearch.WordTrace tailWord_3226684 prefixEnd_3226684 1104559874781439211807171 := by
  unfold tailWord_3226684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58843416921141208299543553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78457889228188277732724737 58843416921141208299543553)
  ·
    refine ⟨44132562690855906224657665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58843416921141208299543553 44132562690855906224657665)
    ·
      refine ⟨33099422018141929668493249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44132562690855906224657665 33099422018141929668493249)
      ·
        refine ⟨24824566513606447251369937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33099422018141929668493249 24824566513606447251369937)
        ·
          refine ⟨18618424885204835438527453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24824566513606447251369937 18618424885204835438527453)
          ·
            refine ⟨6981909331951813289447795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18618424885204835438527453 6981909331951813289447795)
            ·
              refine ⟨10472863997927719934171693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981909331951813289447795 10472863997927719934171693)
              ·
                refine ⟨3927323999222894975314385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10472863997927719934171693 3927323999222894975314385)
                ·
                  refine ⟨2945492999417171231485789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927323999222894975314385 2945492999417171231485789)
                  ·
                    refine ⟨1104559874781439211807171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945492999417171231485789 1104559874781439211807171)
                    ·
                      rfl

theorem cell22_3226684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3226684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226684 prefixEnd_3226684 := by exact prefixLift 3226684
  have htrace : WordTrace (prefixWord ++ tailWord_3226684) baseStart_3226684 baseEnd_3226684 := by
    simpa [prefixWord, tailWord_3226684, baseEnd_3226684] using wordTrace_append hprefix tailTrace_3226684
  have hstable : (prefixWord ++ tailWord_3226684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226684).length < 2 ^ (prefixWord ++ tailWord_3226684).sum := by decide
  have hdescent : baseEnd_3226684 < baseStart_3226684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226718 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3226718 : Nat := 118140960795 + 3226718 * 2 ^ 59
def prefixEnd_3226718 : Nat := 4983230072969 + 3 ^ 40 * 3226718 * 2
def baseEnd_3226718 : Nat := 1104571513676274456457067

theorem tailTrace_3226718 : CollatzResearch.WordTrace tailWord_3226718 prefixEnd_3226718 1104571513676274456457067 := by
  unfold tailWord_3226718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711009240519905050728101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78458715949439493603883205 14711009240519905050728101)
  ·
    refine ⟨2758314232597482197011519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14711009240519905050728101 2758314232597482197011519)
    ·
      refine ⟨4137471348896223295517279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758314232597482197011519 4137471348896223295517279)
      ·
        refine ⟨6206207023344334943275919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137471348896223295517279 6206207023344334943275919)
        ·
          refine ⟨9309310535016502414913879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206207023344334943275919 9309310535016502414913879)
          ·
            refine ⟨13963965802524753622370819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309310535016502414913879 13963965802524753622370819)
            ·
              refine ⟨20945948703787130433556229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13963965802524753622370819 20945948703787130433556229)
              ·
                refine ⟨3927365381960086956291793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20945948703787130433556229 3927365381960086956291793)
                ·
                  refine ⟨2945524036470065217218845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927365381960086956291793 2945524036470065217218845)
                  ·
                    refine ⟨1104571513676274456457067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945524036470065217218845 1104571513676274456457067)
                    ·
                      rfl

theorem cell22_3226718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3226718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226718 prefixEnd_3226718 := by exact prefixLift 3226718
  have htrace : WordTrace (prefixWord ++ tailWord_3226718) baseStart_3226718 baseEnd_3226718 := by
    simpa [prefixWord, tailWord_3226718, baseEnd_3226718] using wordTrace_append hprefix tailTrace_3226718
  have hstable : (prefixWord ++ tailWord_3226718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226718).length < 2 ^ (prefixWord ++ tailWord_3226718).sum := by decide
  have hdescent : baseEnd_3226718 < baseStart_3226718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226750 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3226750 : Nat := 118140960795 + 3226750 * 2 ^ 59
def prefixEnd_3226750 : Nat := 4983230072969 + 3 ^ 40 * 3226750 * 2
def baseEnd_3226750 : Nat := 1104582467930237039656969

theorem tailTrace_3226750 : CollatzResearch.WordTrace tailWord_3226750 prefixEnd_3226750 1104582467930237039656969 := by
  unfold tailWord_3226750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711155132505413733873713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78459494040028873247326469 14711155132505413733873713)
  ·
    refine ⟨11033366349379060300405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14711155132505413733873713 11033366349379060300405285)
    ·
      refine ⟨2068756190508573806325991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11033366349379060300405285 2068756190508573806325991)
      ·
        refine ⟨3103134285762860709488987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068756190508573806325991 3103134285762860709488987)
        ·
          refine ⟨4654701428644291064233481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103134285762860709488987 4654701428644291064233481)
          ·
            refine ⟨3491026071483218298175111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654701428644291064233481 3491026071483218298175111)
            ·
              refine ⟨5236539107224827447262667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491026071483218298175111 5236539107224827447262667)
              ·
                refine ⟨7854808660837241170894001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236539107224827447262667 7854808660837241170894001)
                ·
                  refine ⟨5891106495627930878170501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7854808660837241170894001 5891106495627930878170501)
                  ·
                    refine ⟨1104582467930237039656969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5891106495627930878170501 1104582467930237039656969)
                    ·
                      rfl

theorem cell22_3226750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3226750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226750 prefixEnd_3226750 := by exact prefixLift 3226750
  have htrace : WordTrace (prefixWord ++ tailWord_3226750) baseStart_3226750 baseEnd_3226750 := by
    simpa [prefixWord, tailWord_3226750, baseEnd_3226750] using wordTrace_append hprefix tailTrace_3226750
  have hstable : (prefixWord ++ tailWord_3226750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226750).length < 2 ^ (prefixWord ++ tailWord_3226750).sum := by decide
  have hdescent : baseEnd_3226750 < baseStart_3226750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226834 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3226834 : Nat := 118140960795 + 3226834 * 2 ^ 59
def prefixEnd_3226834 : Nat := 4983230072969 + 3 ^ 40 * 3226834 * 2
def baseEnd_3226834 : Nat := 1104611222846888820556711

theorem tailTrace_3226834 : CollatzResearch.WordTrace tailWord_3226834 prefixEnd_3226834 1104611222846888820556711 := by
  unfold tailWord_3226834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423076197934748054261889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78461536527825994811365037 29423076197934748054261889)
  ·
    refine ⟨22067307148451061040696417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29423076197934748054261889 22067307148451061040696417)
    ·
      refine ⟨16550480361338295780522313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22067307148451061040696417 16550480361338295780522313)
      ·
        refine ⟨12412860271003721835391735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16550480361338295780522313 12412860271003721835391735)
        ·
          refine ⟨18619290406505582753087603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412860271003721835391735 18619290406505582753087603)
          ·
            refine ⟨27928935609758374129631405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18619290406505582753087603 27928935609758374129631405)
            ·
              refine ⟨10473350853659390298611777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27928935609758374129631405 10473350853659390298611777)
              ·
                refine ⟨7855013140244542723958833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10473350853659390298611777 7855013140244542723958833)
                ·
                  refine ⟨5891259855183407042969125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7855013140244542723958833 5891259855183407042969125)
                  ·
                    refine ⟨1104611222846888820556711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5891259855183407042969125 1104611222846888820556711)
                    ·
                      rfl

theorem cell22_3226834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3226834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226834 prefixEnd_3226834 := by exact prefixLift 3226834
  have htrace : WordTrace (prefixWord ++ tailWord_3226834) baseStart_3226834 baseEnd_3226834 := by
    simpa [prefixWord, tailWord_3226834, baseEnd_3226834] using wordTrace_append hprefix tailTrace_3226834
  have hstable : (prefixWord ++ tailWord_3226834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226834).length < 2 ^ (prefixWord ++ tailWord_3226834).sum := by decide
  have hdescent : baseEnd_3226834 < baseStart_3226834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226838 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3226838 : Nat := 118140960795 + 3226838 * 2 ^ 59
def prefixEnd_3226838 : Nat := 4983230072969 + 3 ^ 40 * 3226838 * 2
def baseEnd_3226838 : Nat := 368204197376211381152233

theorem tailTrace_3226838 : CollatzResearch.WordTrace tailWord_3226838 prefixEnd_3226838 368204197376211381152233 := by
  unfold tailWord_3226838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355778167732781306262073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78461633789149667266795445 7355778167732781306262073)
  ·
    refine ⟨5516833625799585979696555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7355778167732781306262073 5516833625799585979696555)
    ·
      refine ⟨8275250438699378969544833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516833625799585979696555 8275250438699378969544833)
      ·
        refine ⟨6206437829024534227158625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8275250438699378969544833 6206437829024534227158625)
        ·
          refine ⟨4654828371768400670368969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6206437829024534227158625 4654828371768400670368969)
          ·
            refine ⟨3491121278826300502776727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654828371768400670368969 3491121278826300502776727)
            ·
              refine ⟨5236681918239450754165091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491121278826300502776727 5236681918239450754165091)
              ·
                refine ⟨7855022877359176131247637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236681918239450754165091 7855022877359176131247637)
                ·
                  refine ⟨368204197376211381152233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7855022877359176131247637 368204197376211381152233)
                  ·
                    rfl

theorem cell22_3226838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3226838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226838 prefixEnd_3226838 := by exact prefixLift 3226838
  have htrace : WordTrace (prefixWord ++ tailWord_3226838) baseStart_3226838 baseEnd_3226838 := by
    simpa [prefixWord, tailWord_3226838, baseEnd_3226838] using wordTrace_append hprefix tailTrace_3226838
  have hstable : (prefixWord ++ tailWord_3226838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226838).length < 2 ^ (prefixWord ++ tailWord_3226838).sum := by decide
  have hdescent : baseEnd_3226838 < baseStart_3226838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226894 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3226894 : Nat := 118140960795 + 3226894 * 2 ^ 59
def prefixEnd_3226894 : Nat := 4983230072969 + 3 ^ 40 * 3226894 * 2
def baseEnd_3226894 : Nat := 368210587357689554685509

theorem tailTrace_3226894 : CollatzResearch.WordTrace tailWord_3226894 prefixEnd_3226894 368210587357689554685509 := by
  unfold tailWord_3226894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711811646440202808028967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78462995447681081642821157 14711811646440202808028967)
  ·
    refine ⟨22067717469660304212043451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14711811646440202808028967 22067717469660304212043451)
    ·
      refine ⟨33101576204490456318065177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22067717469660304212043451 33101576204490456318065177)
      ·
        refine ⟨24826182153367842238548883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33101576204490456318065177 24826182153367842238548883)
        ·
          refine ⟨37239273230051763357823325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24826182153367842238548883 37239273230051763357823325)
          ·
            refine ⟨13964727461269411259183747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37239273230051763357823325 13964727461269411259183747)
            ·
              refine ⟨20947091191904116888775621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964727461269411259183747 20947091191904116888775621)
              ·
                refine ⟨3927579598482021916645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20947091191904116888775621 3927579598482021916645429)
                ·
                  refine ⟨368210587357689554685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927579598482021916645429 368210587357689554685509)
                  ·
                    rfl

theorem cell22_3226894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3226894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226894 prefixEnd_3226894 := by exact prefixLift 3226894
  have htrace : WordTrace (prefixWord ++ tailWord_3226894) baseStart_3226894 baseEnd_3226894 := by
    simpa [prefixWord, tailWord_3226894, baseEnd_3226894] using wordTrace_append hprefix tailTrace_3226894
  have hstable : (prefixWord ++ tailWord_3226894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226894).length < 2 ^ (prefixWord ++ tailWord_3226894).sum := by decide
  have hdescent : baseEnd_3226894 < baseStart_3226894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226909 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_3226909 : Nat := 118140960795 + 3226909 * 2 ^ 59
def prefixEnd_3226909 : Nat := 4983230072969 + 3 ^ 40 * 3226909 * 2
def baseEnd_3226909 : Nat := 1104636896879613624931481

theorem tailTrace_3226909 : CollatzResearch.WordTrace tailWord_3226909 prefixEnd_3226909 1104636896879613624931481 := by
  unfold tailWord_3226909
  simp only [CollatzResearch.WordTrace]
  refine ⟨117695040266467280026027781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78463360177644853350685187 117695040266467280026027781)
  ·
    refine ⟨22067820049962615004880209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117695040266467280026027781 22067820049962615004880209)
    ·
      refine ⟨16550865037471961253660157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22067820049962615004880209 16550865037471961253660157)
      ·
        refine ⟨6206574389051985470122559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16550865037471961253660157 6206574389051985470122559)
        ·
          refine ⟨9309861583577978205183839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206574389051985470122559 9309861583577978205183839)
          ·
            refine ⟨13964792375366967307775759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309861583577978205183839 13964792375366967307775759)
            ·
              refine ⟨20947188563050450961663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964792375366967307775759 20947188563050450961663639)
              ·
                refine ⟨31420782844575676442495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20947188563050450961663639 31420782844575676442495459)
                ·
                  refine ⟨47131174266863514663743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31420782844575676442495459 47131174266863514663743189)
                  ·
                    refine ⟨1104636896879613624931481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47131174266863514663743189 1104636896879613624931481)
                    ·
                      rfl

theorem cell22_3226909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_3226909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226909 prefixEnd_3226909 := by exact prefixLift 3226909
  have htrace : WordTrace (prefixWord ++ tailWord_3226909) baseStart_3226909 baseEnd_3226909 := by
    simpa [prefixWord, tailWord_3226909, baseEnd_3226909] using wordTrace_append hprefix tailTrace_3226909
  have hstable : (prefixWord ++ tailWord_3226909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226909).length < 2 ^ (prefixWord ++ tailWord_3226909).sum := by decide
  have hdescent : baseEnd_3226909 < baseStart_3226909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226924 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_3226924 : Nat := 118140960795 + 3226924 * 2 ^ 59
def prefixEnd_3226924 : Nat := 4983230072969 + 3 ^ 40 * 3226924 * 2
def baseEnd_3226924 : Nat := 1104642031686158585806435

theorem tailTrace_3226924 : CollatzResearch.WordTrace tailWord_3226924 prefixEnd_3226924 1104642031686158585806435 := by
  unfold tailWord_3226924
  simp only [CollatzResearch.WordTrace]
  refine ⟨58847793680706468793911913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78463724907608625058549217 58847793680706468793911913)
  ·
    refine ⟨44135845260529851595433935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58847793680706468793911913 44135845260529851595433935)
    ·
      refine ⟨66203767890794777393150903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44135845260529851595433935 66203767890794777393150903)
      ·
        refine ⟨99305651836192166089726355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66203767890794777393150903 99305651836192166089726355)
        ·
          refine ⟨148958477754288249134589533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99305651836192166089726355 148958477754288249134589533)
          ·
            refine ⟨55859429157858093425471075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148958477754288249134589533 55859429157858093425471075)
            ·
              refine ⟨83789143736787140138206613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55859429157858093425471075 83789143736787140138206613)
              ·
                refine ⟨3927616112661897193978435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83789143736787140138206613 3927616112661897193978435)
                ·
                  refine ⟨5891424168992845790967653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927616112661897193978435 5891424168992845790967653)
                  ·
                    refine ⟨1104642031686158585806435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5891424168992845790967653 1104642031686158585806435)
                    ·
                      rfl

theorem cell22_3226924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_3226924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226924 prefixEnd_3226924 := by exact prefixLift 3226924
  have htrace : WordTrace (prefixWord ++ tailWord_3226924) baseStart_3226924 baseEnd_3226924 := by
    simpa [prefixWord, tailWord_3226924, baseEnd_3226924] using wordTrace_append hprefix tailTrace_3226924
  have hstable : (prefixWord ++ tailWord_3226924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226924).length < 2 ^ (prefixWord ++ tailWord_3226924).sum := by decide
  have hdescent : baseEnd_3226924 < baseStart_3226924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226956 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_3226956 : Nat := 118140960795 + 3226956 * 2 ^ 59
def prefixEnd_3226956 : Nat := 4983230072969 + 3 ^ 40 * 3226956 * 2
def baseEnd_3226956 : Nat := 368217661980040389668779

theorem tailTrace_3226956 : CollatzResearch.WordTrace tailWord_3226956 prefixEnd_3226956 368217661980040389668779 := by
  unfold tailWord_3226956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58848377248648503526494361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78464502998198004701992481 58848377248648503526494361)
  ·
    refine ⟨44136282936486377644870771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58848377248648503526494361 44136282936486377644870771)
    ·
      refine ⟨66204424404729566467306157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44136282936486377644870771 66204424404729566467306157)
      ·
        refine ⟨24826659151773587425239809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66204424404729566467306157 24826659151773587425239809)
        ·
          refine ⟨18619994363830190568929857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24826659151773587425239809 18619994363830190568929857)
          ·
            refine ⟨13964995772872642926697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18619994363830190568929857 13964995772872642926697393)
            ·
              refine ⟨10473746829654482195023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13964995772872642926697393 10473746829654482195023045)
              ·
                refine ⟨1963827530560215411566821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10473746829654482195023045 1963827530560215411566821)
                ·
                  refine ⟨368217661980040389668779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963827530560215411566821 368217661980040389668779)
                  ·
                    rfl

theorem cell22_3226956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_3226956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3226956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3226956 prefixEnd_3226956 := by exact prefixLift 3226956
  have htrace : WordTrace (prefixWord ++ tailWord_3226956) baseStart_3226956 baseEnd_3226956 := by
    simpa [prefixWord, tailWord_3226956, baseEnd_3226956] using wordTrace_append hprefix tailTrace_3226956
  have hstable : (prefixWord ++ tailWord_3226956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226956).length < 2 ^ (prefixWord ++ tailWord_3226956).sum := by decide
  have hdescent : baseEnd_3226956 < baseStart_3226956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227022 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3227022 : Nat := 118140960795 + 3227022 * 2 ^ 59
def prefixEnd_3227022 : Nat := 4983230072969 + 3 ^ 40 * 3227022 * 2
def baseEnd_3227022 : Nat := 1104675579088918996856135

theorem tailTrace_3227022 : CollatzResearch.WordTrace tailWord_3227022 prefixEnd_3227022 1104675579088918996856135 := by
  unfold tailWord_3227022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14712395214382237540611415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78466107810038600216594213 14712395214382237540611415)
  ·
    refine ⟨22068592821573356310917123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14712395214382237540611415 22068592821573356310917123)
    ·
      refine ⟨33102889232360034466375685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22068592821573356310917123 33102889232360034466375685)
      ·
        refine ⟨6206791731067506462445441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33102889232360034466375685 6206791731067506462445441)
        ·
          refine ⟨4655093798300629846834081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6206791731067506462445441 4655093798300629846834081)
          ·
            refine ⟨3491320348725472385125561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4655093798300629846834081 3491320348725472385125561)
            ·
              refine ⟨2618490261544104288844171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491320348725472385125561 2618490261544104288844171)
              ·
                refine ⟨3927735392316156433266257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618490261544104288844171 3927735392316156433266257)
                ·
                  refine ⟨2945801544237117324949693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927735392316156433266257 2945801544237117324949693)
                  ·
                    refine ⟨1104675579088918996856135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945801544237117324949693 1104675579088918996856135)
                    ·
                      rfl

theorem cell22_3227022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3227022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227022 prefixEnd_3227022 := by exact prefixLift 3227022
  have htrace : WordTrace (prefixWord ++ tailWord_3227022) baseStart_3227022 baseEnd_3227022 := by
    simpa [prefixWord, tailWord_3227022, baseEnd_3227022] using wordTrace_append hprefix tailTrace_3227022
  have hstable : (prefixWord ++ tailWord_3227022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227022).length < 2 ^ (prefixWord ++ tailWord_3227022).sum := by decide
  have hdescent : baseEnd_3227022 < baseStart_3227022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227044 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3227044 : Nat := 118140960795 + 3227044 * 2 ^ 59
def prefixEnd_3227044 : Nat := 4983230072969 + 3 ^ 40 * 3227044 * 2
def baseEnd_3227044 : Nat := 1104683110138518272806067

theorem tailTrace_3227044 : CollatzResearch.WordTrace tailWord_3227044 prefixEnd_3227044 1104683110138518272806067 := by
  unfold tailWord_3227044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58849982060489099041096093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78466642747318798721461457 58849982060489099041096093)
  ·
    refine ⟨22068743272683412140411035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58849982060489099041096093 22068743272683412140411035)
    ·
      refine ⟨33103114909025118210616553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22068743272683412140411035 33103114909025118210616553)
      ·
        refine ⟨24827336181768838657962415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33103114909025118210616553 24827336181768838657962415)
        ·
          refine ⟨37241004272653257986943623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24827336181768838657962415 37241004272653257986943623)
          ·
            refine ⟨55861506408979886980415435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37241004272653257986943623 55861506408979886980415435)
            ·
              refine ⟨83792259613469830470623153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55861506408979886980415435 83792259613469830470623153)
              ·
                refine ⟨62844194710102372852967365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83792259613469830470623153 62844194710102372852967365)
                ·
                  refine ⟨11783286508144194909931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62844194710102372852967365 11783286508144194909931381)
                  ·
                    refine ⟨1104683110138518272806067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11783286508144194909931381 1104683110138518272806067)
                    ·
                      rfl

theorem cell22_3227044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3227044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227044 prefixEnd_3227044 := by exact prefixLift 3227044
  have htrace : WordTrace (prefixWord ++ tailWord_3227044) baseStart_3227044 baseEnd_3227044 := by
    simpa [prefixWord, tailWord_3227044, baseEnd_3227044] using wordTrace_append hprefix tailTrace_3227044
  have hstable : (prefixWord ++ tailWord_3227044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227044).length < 2 ^ (prefixWord ++ tailWord_3227044).sum := by decide
  have hdescent : baseEnd_3227044 < baseStart_3227044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227125 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 4]
def baseStart_3227125 : Nat := 118140960795 + 3227125 * 2 ^ 59
def prefixEnd_3227125 : Nat := 4983230072969 + 3 ^ 40 * 3227125 * 2
def baseEnd_3227125 : Nat := 368236946031287020510273

theorem tailTrace_3227125 : CollatzResearch.WordTrace tailWord_3227125 prefixEnd_3227125 368236946031287020510273 := by
  unfold tailWord_3227125
  simp only [CollatzResearch.WordTrace]
  refine ⟨117702918433684748915890829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78468612289123165943927219 117702918433684748915890829)
  ·
    refine ⟨44138594412631780843459061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117702918433684748915890829 44138594412631780843459061)
    ·
      refine ⟨4137993226184229454074287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44138594412631780843459061 4137993226184229454074287)
      ·
        refine ⟨6206989839276344181111431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137993226184229454074287 6206989839276344181111431)
        ·
          refine ⟨9310484758914516271667147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206989839276344181111431 9310484758914516271667147)
          ·
            refine ⟨13965727138371774407500721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310484758914516271667147 13965727138371774407500721)
            ·
              refine ⟨10474295353778830805625541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13965727138371774407500721 10474295353778830805625541)
              ·
                refine ⟨1963930378833530776054789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10474295353778830805625541 1963930378833530776054789)
                ·
                  refine ⟨368236946031287020510273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963930378833530776054789 368236946031287020510273)
                  ·
                    rfl

theorem cell22_3227125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_3227125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227125 prefixEnd_3227125 := by exact prefixLift 3227125
  have htrace : WordTrace (prefixWord ++ tailWord_3227125) baseStart_3227125 baseEnd_3227125 := by
    simpa [prefixWord, tailWord_3227125, baseEnd_3227125] using wordTrace_append hprefix tailTrace_3227125
  have hstable : (prefixWord ++ tailWord_3227125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227125).length < 2 ^ (prefixWord ++ tailWord_3227125).sum := by decide
  have hdescent : baseEnd_3227125 < baseStart_3227125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227138 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3227138 : Nat := 118140960795 + 3227138 * 2 ^ 59
def prefixEnd_3227138 : Nat := 4983230072969 + 3 ^ 40 * 3227138 * 2
def baseEnd_3227138 : Nat := 1104715288259533360955779

theorem tailTrace_3227138 : CollatzResearch.WordTrace tailWord_3227138 prefixEnd_3227138 1104715288259533360955779 := by
  unfold tailWord_3227138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425848145659413034028517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78468928388425101424076045 29425848145659413034028517)
  ·
    refine ⟨5517346527311139943880347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29425848145659413034028517 5517346527311139943880347)
    ·
      refine ⟨8276019790966709915820521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517346527311139943880347 8276019790966709915820521)
      ·
        refine ⟨6207014843225032436865391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8276019790966709915820521 6207014843225032436865391)
        ·
          refine ⟨9310522264837548655298087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6207014843225032436865391 9310522264837548655298087)
          ·
            refine ⟨13965783397256322982947131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310522264837548655298087 13965783397256322982947131)
            ·
              refine ⟨20948675095884484474420697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13965783397256322982947131 20948675095884484474420697)
              ·
                refine ⟨15711506321913363355815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20948675095884484474420697 15711506321913363355815523)
                ·
                  refine ⟨23567259482870045033723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15711506321913363355815523 23567259482870045033723285)
                  ·
                    refine ⟨1104715288259533360955779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23567259482870045033723285 1104715288259533360955779)
                    ·
                      rfl

theorem cell22_3227138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3227138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227138 prefixEnd_3227138 := by exact prefixLift 3227138
  have htrace : WordTrace (prefixWord ++ tailWord_3227138) baseStart_3227138 baseEnd_3227138 := by
    simpa [prefixWord, tailWord_3227138, baseEnd_3227138] using wordTrace_append hprefix tailTrace_3227138
  have hstable : (prefixWord ++ tailWord_3227138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227138).length < 2 ^ (prefixWord ++ tailWord_3227138).sum := by decide
  have hdescent : baseEnd_3227138 < baseStart_3227138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227140 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3227140 : Nat := 118140960795 + 3227140 * 2 ^ 59
def prefixEnd_3227140 : Nat := 4983230072969 + 3 ^ 40 * 3227140 * 2
def baseEnd_3227140 : Nat := 1104715972900406022405773

theorem tailTrace_3227140 : CollatzResearch.WordTrace tailWord_3227140 prefixEnd_3227140 1104715972900406022405773 := by
  unfold tailWord_3227140
  simp only [CollatzResearch.WordTrace]
  refine ⟨58851732764315203238843437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78468977019086937651791249 58851732764315203238843437)
  ·
    refine ⟨22069399786618201214566289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58851732764315203238843437 22069399786618201214566289)
    ·
      refine ⟨16552049839963650910924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22069399786618201214566289 16552049839963650910924717)
      ·
        refine ⟨6207018689986369091596769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16552049839963650910924717 6207018689986369091596769)
        ·
          refine ⟨4655264017489776818697577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6207018689986369091596769 4655264017489776818697577)
          ·
            refine ⟨3491448013117332614023183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4655264017489776818697577 3491448013117332614023183)
            ·
              refine ⟨5237172019675998921034775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491448013117332614023183 5237172019675998921034775)
              ·
                refine ⟨7855758029513998381552163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237172019675998921034775 7855758029513998381552163)
                ·
                  refine ⟨11783637044270997572328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855758029513998381552163 11783637044270997572328245)
                  ·
                    refine ⟨1104715972900406022405773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11783637044270997572328245 1104715972900406022405773)
                    ·
                      rfl

theorem cell22_3227140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3227140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227140 prefixEnd_3227140 := by exact prefixLift 3227140
  have htrace : WordTrace (prefixWord ++ tailWord_3227140) baseStart_3227140 baseEnd_3227140 := by
    simpa [prefixWord, tailWord_3227140, baseEnd_3227140] using wordTrace_append hprefix tailTrace_3227140
  have hstable : (prefixWord ++ tailWord_3227140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227140).length < 2 ^ (prefixWord ++ tailWord_3227140).sum := by decide
  have hdescent : baseEnd_3227140 < baseStart_3227140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227273 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_3227273 : Nat := 118140960795 + 3227273 * 2 ^ 59
def prefixEnd_3227273 : Nat := 4983230072969 + 3 ^ 40 * 3227273 * 2
def baseEnd_3227273 : Nat := 1104761501518438008830365

theorem tailTrace_3227273 : CollatzResearch.WordTrace tailWord_3227273 prefixEnd_3227273 1104761501518438008830365 := by
  unfold tailWord_3227273
  simp only [CollatzResearch.WordTrace]
  refine ⟨117708316437148570192278473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78472210958099046794852315 117708316437148570192278473)
  ·
    refine ⟨88281237327861427644208855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117708316437148570192278473 88281237327861427644208855)
    ·
      refine ⟨132421855991792141466313283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88281237327861427644208855 132421855991792141466313283)
      ·
        refine ⟨198632783987688212199469925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132421855991792141466313283 198632783987688212199469925)
        ·
          refine ⟨37243646997691539787400611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198632783987688212199469925 37243646997691539787400611)
          ·
            refine ⟨55865470496537309681100917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37243646997691539787400611 55865470496537309681100917)
            ·
              refine ⟨5237387859050372782603211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55865470496537309681100917 5237387859050372782603211)
              ·
                refine ⟨7856081788575559173904817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237387859050372782603211 7856081788575559173904817)
                ·
                  refine ⟨5892061341431669380428613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856081788575559173904817 5892061341431669380428613)
                  ·
                    refine ⟨1104761501518438008830365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892061341431669380428613 1104761501518438008830365)
                    ·
                      rfl

theorem cell22_3227273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_3227273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227273 prefixEnd_3227273 := by exact prefixLift 3227273
  have htrace : WordTrace (prefixWord ++ tailWord_3227273) baseStart_3227273 baseEnd_3227273 := by
    simpa [prefixWord, tailWord_3227273, baseEnd_3227273] using wordTrace_append hprefix tailTrace_3227273
  have hstable : (prefixWord ++ tailWord_3227273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227273).length < 2 ^ (prefixWord ++ tailWord_3227273).sum := by decide
  have hdescent : baseEnd_3227273 < baseStart_3227273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227301 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3227301 : Nat := 118140960795 + 3227301 * 2 ^ 59
def prefixEnd_3227301 : Nat := 4983230072969 + 3 ^ 40 * 3227301 * 2
def baseEnd_3227301 : Nat := 1104771086490655269130279

theorem tailTrace_3227301 : CollatzResearch.WordTrace tailWord_3227301 prefixEnd_3227301 1104771086490655269130279 := by
  unfold tailWord_3227301
  simp only [CollatzResearch.WordTrace]
  refine ⟨117709337681047130974297757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78472891787364753982865171 117709337681047130974297757)
  ·
    refine ⟨44141001630392674115361659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117709337681047130974297757 44141001630392674115361659)
    ·
      refine ⟨66211502445589011173042489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44141001630392674115361659 66211502445589011173042489)
      ·
        refine ⟨49658626834191758379781867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66211502445589011173042489 49658626834191758379781867)
        ·
          refine ⟨74487940251287637569672801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49658626834191758379781867 74487940251287637569672801)
          ·
            refine ⟨55865955188465728177254601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74487940251287637569672801 55865955188465728177254601)
            ·
              refine ⟨41899466391349296132940951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55865955188465728177254601 41899466391349296132940951)
              ·
                refine ⟨62849199587023944199411427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41899466391349296132940951 62849199587023944199411427)
                ·
                  refine ⟨94273799380535916299117141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62849199587023944199411427 94273799380535916299117141)
                  ·
                    refine ⟨1104771086490655269130279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94273799380535916299117141 1104771086490655269130279)
                    ·
                      rfl

theorem cell22_3227301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3227301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227301 prefixEnd_3227301 := by exact prefixLift 3227301
  have htrace : WordTrace (prefixWord ++ tailWord_3227301) baseStart_3227301 baseEnd_3227301 := by
    simpa [prefixWord, tailWord_3227301, baseEnd_3227301] using wordTrace_append hprefix tailTrace_3227301
  have hstable : (prefixWord ++ tailWord_3227301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227301).length < 2 ^ (prefixWord ++ tailWord_3227301).sum := by decide
  have hdescent : baseEnd_3227301 < baseStart_3227301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227354 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_3227354 : Nat := 118140960795 + 3227354 * 2 ^ 59
def prefixEnd_3227354 : Nat := 4983230072969 + 3 ^ 40 * 3227354 * 2
def baseEnd_3227354 : Nat := 1104789229473780797555117

theorem tailTrace_3227354 : CollatzResearch.WordTrace tailWord_3227354 prefixEnd_3227354 1104789229473780797555117 := by
  unfold tailWord_3227354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29427817687463780256494279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78474180499903414017318077 29427817687463780256494279)
  ·
    refine ⟨44141726531195670384741419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29427817687463780256494279 44141726531195670384741419)
    ·
      refine ⟨66212589796793505577112129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44141726531195670384741419 66212589796793505577112129)
      ·
        refine ⟨49659442347595129182834097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66212589796793505577112129 49659442347595129182834097)
        ·
          refine ⟨37244581760696346887125573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49659442347595129182834097 37244581760696346887125573)
          ·
            refine ⟨6983359080130565041336045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37244581760696346887125573 6983359080130565041336045)
            ·
              refine ⟨2618759655048961890501017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6983359080130565041336045 2618759655048961890501017)
              ·
                refine ⟨1964069741286721417875763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618759655048961890501017 1964069741286721417875763)
                ·
                  refine ⟨2946104611930082126813645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964069741286721417875763 2946104611930082126813645)
                  ·
                    refine ⟨1104789229473780797555117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2946104611930082126813645 1104789229473780797555117)
                    ·
                      rfl

theorem cell22_3227354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_3227354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227354 prefixEnd_3227354 := by exact prefixLift 3227354
  have htrace : WordTrace (prefixWord ++ tailWord_3227354) baseStart_3227354 baseEnd_3227354 := by
    simpa [prefixWord, tailWord_3227354, baseEnd_3227354] using wordTrace_append hprefix tailTrace_3227354
  have hstable : (prefixWord ++ tailWord_3227354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227354).length < 2 ^ (prefixWord ++ tailWord_3227354).sum := by decide
  have hdescent : baseEnd_3227354 < baseStart_3227354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227367 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 5]
def baseStart_3227367 : Nat := 118140960795 + 3227367 * 2 ^ 59
def prefixEnd_3227367 : Nat := 4983230072969 + 3 ^ 40 * 3227367 * 2
def baseEnd_3227367 : Nat := 368264559879817698993359

theorem tailTrace_3227367 : CollatzResearch.WordTrace tailWord_3227367 prefixEnd_3227367 368264559879817698993359 := by
  unfold tailWord_3227367
  simp only [CollatzResearch.WordTrace]
  refine ⟨117711744898808024246200355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78474496599205349497466903 117711744898808024246200355)
  ·
    refine ⟨176567617348212036369300533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117711744898808024246200355 176567617348212036369300533)
    ·
      refine ⟨16553214126394878409621925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176567617348212036369300533 16553214126394878409621925)
      ·
        refine ⟨3103727648699039701804111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16553214126394878409621925 3103727648699039701804111)
        ·
          refine ⟨4655591473048559552706167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103727648699039701804111 4655591473048559552706167)
          ·
            refine ⟨6983387209572839329059251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4655591473048559552706167 6983387209572839329059251)
            ·
              refine ⟨10475080814359258993588877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6983387209572839329059251 10475080814359258993588877)
              ·
                refine ⟨3928155305384722122595829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10475080814359258993588877 3928155305384722122595829)
                ·
                  refine ⟨368264559879817698993359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928155305384722122595829 368264559879817698993359)
                  ·
                    rfl

theorem cell22_3227367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].length) (baseStart_3227367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227367 prefixEnd_3227367 := by exact prefixLift 3227367
  have htrace : WordTrace (prefixWord ++ tailWord_3227367) baseStart_3227367 baseEnd_3227367 := by
    simpa [prefixWord, tailWord_3227367, baseEnd_3227367] using wordTrace_append hprefix tailTrace_3227367
  have hstable : (prefixWord ++ tailWord_3227367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227367).length < 2 ^ (prefixWord ++ tailWord_3227367).sum := by decide
  have hdescent : baseEnd_3227367 < baseStart_3227367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227378 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_3227378 : Nat := 118140960795 + 3227378 * 2 ^ 59
def prefixEnd_3227378 : Nat := 4983230072969 + 3 ^ 40 * 3227378 * 2
def baseEnd_3227378 : Nat := 368265815054750911651681

theorem tailTrace_3227378 : CollatzResearch.WordTrace tailWord_3227378 prefixEnd_3227378 368265815054750911651681 := by
  unfold tailWord_3227378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29428036525442043281212697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78474764067845448749900525 29428036525442043281212697)
  ·
    refine ⟨22071027394081532460909523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29428036525442043281212697 22071027394081532460909523)
    ·
      refine ⟨33106541091122298691364285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071027394081532460909523 33106541091122298691364285)
      ·
        refine ⟨12414952909170862009261607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33106541091122298691364285 12414952909170862009261607)
        ·
          refine ⟨18622429363756293013892411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414952909170862009261607 18622429363756293013892411)
          ·
            refine ⟨27933644045634439520838617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18622429363756293013892411 27933644045634439520838617)
            ·
              refine ⟨20950233034225829640628963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27933644045634439520838617 20950233034225829640628963)
              ·
                refine ⟨31425349551338744460943445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20950233034225829640628963 31425349551338744460943445)
                ·
                  refine ⟨368265815054750911651681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31425349551338744460943445 368265815054750911651681)
                  ·
                    rfl

theorem cell22_3227378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_3227378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227378 prefixEnd_3227378 := by exact prefixLift 3227378
  have htrace : WordTrace (prefixWord ++ tailWord_3227378) baseStart_3227378 baseEnd_3227378 := by
    simpa [prefixWord, tailWord_3227378, baseEnd_3227378] using wordTrace_append hprefix tailTrace_3227378
  have hstable : (prefixWord ++ tailWord_3227378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227378).length < 2 ^ (prefixWord ++ tailWord_3227378).sum := by decide
  have hdescent : baseEnd_3227378 < baseStart_3227378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227393 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3227393 : Nat := 118140960795 + 3227393 * 2 ^ 59
def prefixEnd_3227393 : Nat := 4983230072969 + 3 ^ 40 * 3227393 * 2
def baseEnd_3227393 : Nat := 1104802579970797695829997

theorem tailTrace_3227393 : CollatzResearch.WordTrace tailWord_3227393 prefixEnd_3227393 1104802579970797695829997 := by
  unfold tailWord_3227393
  simp only [CollatzResearch.WordTrace]
  refine ⟨117712693196713830686646833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78475128797809220457764555 117712693196713830686646833)
  ·
    refine ⟨88284519897535373014985125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117712693196713830686646833 88284519897535373014985125)
    ·
      refine ⟨16553347480787882440309711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88284519897535373014985125 16553347480787882440309711)
      ·
        refine ⟨24830021221181823660464567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16553347480787882440309711 24830021221181823660464567)
        ·
          refine ⟨37245031831772735490696851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24830021221181823660464567 37245031831772735490696851)
          ·
            refine ⟨55867547747659103236045277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37245031831772735490696851 55867547747659103236045277)
            ·
              refine ⟨20950330405372163713516979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55867547747659103236045277 20950330405372163713516979)
              ·
                refine ⟨31425495608058245570275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20950330405372163713516979 31425495608058245570275469)
                ·
                  refine ⟨11784560853021842088853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31425495608058245570275469 11784560853021842088853301)
                  ·
                    refine ⟨1104802579970797695829997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11784560853021842088853301 1104802579970797695829997)
                    ·
                      rfl

theorem cell22_3227393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3227393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227393 prefixEnd_3227393 := by exact prefixLift 3227393
  have htrace : WordTrace (prefixWord ++ tailWord_3227393) baseStart_3227393 baseEnd_3227393 := by
    simpa [prefixWord, tailWord_3227393, baseEnd_3227393] using wordTrace_append hprefix tailTrace_3227393
  have hstable : (prefixWord ++ tailWord_3227393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227393).length < 2 ^ (prefixWord ++ tailWord_3227393).sum := by decide
  have hdescent : baseEnd_3227393 < baseStart_3227393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227405 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3227405 : Nat := 118140960795 + 3227405 * 2 ^ 59
def prefixEnd_3227405 : Nat := 4983230072969 + 3 ^ 40 * 3227405 * 2
def baseEnd_3227405 : Nat := 1104806687816033664529961

theorem tailTrace_3227405 : CollatzResearch.WordTrace tailWord_3227405 prefixEnd_3227405 1104806687816033664529961 := by
  unfold tailWord_3227405
  simp only [CollatzResearch.WordTrace]
  refine ⟨117713130872670356736083669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78475420581780237824055779 117713130872670356736083669)
  ·
    refine ⟨2758901504828211486001961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117713130872670356736083669 2758901504828211486001961)
    ·
      refine ⟨2069176128621158614501471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2758901504828211486001961 2069176128621158614501471)
      ·
        refine ⟨3103764192931737921752207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069176128621158614501471 3103764192931737921752207)
        ·
          refine ⟨4655646289397606882628311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103764192931737921752207 4655646289397606882628311)
          ·
            refine ⟨6983469434096410323942467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4655646289397606882628311 6983469434096410323942467)
            ·
              refine ⟨10475204151144615485913701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6983469434096410323942467 10475204151144615485913701)
              ·
                refine ⟨1964100778339615403608819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10475204151144615485913701 1964100778339615403608819)
                ·
                  refine ⟨2946151167509423105413229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964100778339615403608819 2946151167509423105413229)
                  ·
                    refine ⟨1104806687816033664529961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2946151167509423105413229 1104806687816033664529961)
                    ·
                      rfl

theorem cell22_3227405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3227405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227405 prefixEnd_3227405 := by exact prefixLift 3227405
  have htrace : WordTrace (prefixWord ++ tailWord_3227405) baseStart_3227405 baseEnd_3227405 := by
    simpa [prefixWord, tailWord_3227405, baseEnd_3227405] using wordTrace_append hprefix tailTrace_3227405
  have hstable : (prefixWord ++ tailWord_3227405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227405).length < 2 ^ (prefixWord ++ tailWord_3227405).sum := by decide
  have hdescent : baseEnd_3227405 < baseStart_3227405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227442 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_3227442 : Nat := 118140960795 + 3227442 * 2 ^ 59
def prefixEnd_3227442 : Nat := 4983230072969 + 3 ^ 40 * 3227442 * 2
def baseEnd_3227442 : Nat := 1104819353672177901354847

theorem tailTrace_3227442 : CollatzResearch.WordTrace tailWord_3227442 prefixEnd_3227442 1104819353672177901354847 := by
  unfold tailWord_3227442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29428620093384078013795145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78476320249024208036787053 29428620093384078013795145)
  ·
    refine ⟨22071465070038058510346359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29428620093384078013795145 22071465070038058510346359)
    ·
      refine ⟨33107197605057087765519539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071465070038058510346359 33107197605057087765519539)
      ·
        refine ⟨49660796407585631648279309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33107197605057087765519539 49660796407585631648279309)
        ·
          refine ⟨18622798652844611868104741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49660796407585631648279309 18622798652844611868104741)
          ·
            refine ⟨3491774747408364725269639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18622798652844611868104741 3491774747408364725269639)
            ·
              refine ⟨5237662121112547087904459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491774747408364725269639 5237662121112547087904459)
              ·
                refine ⟨7856493181668820631856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237662121112547087904459 7856493181668820631856689)
                ·
                  refine ⟨5892369886251615473892517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856493181668820631856689 5892369886251615473892517)
                  ·
                    refine ⟨1104819353672177901354847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892369886251615473892517 1104819353672177901354847)
                    ·
                      rfl

theorem cell22_3227442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_3227442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227442 prefixEnd_3227442 := by exact prefixLift 3227442
  have htrace : WordTrace (prefixWord ++ tailWord_3227442) baseStart_3227442 baseEnd_3227442 := by
    simpa [prefixWord, tailWord_3227442, baseEnd_3227442] using wordTrace_append hprefix tailTrace_3227442
  have hstable : (prefixWord ++ tailWord_3227442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227442).length < 2 ^ (prefixWord ++ tailWord_3227442).sum := by decide
  have hdescent : baseEnd_3227442 < baseStart_3227442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227549 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3227549 : Nat := 118140960795 + 3227549 * 2 ^ 59
def prefixEnd_3227549 : Nat := 4983230072969 + 3 ^ 40 * 3227549 * 2
def baseEnd_3227549 : Nat := 1104855981958865288929519

theorem tailTrace_3227549 : CollatzResearch.WordTrace tailWord_3227549 prefixEnd_3227549 1104855981958865288929519 := by
  unfold tailWord_3227549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117718382984148669329325701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78478921989432446219550467 117718382984148669329325701)
  ·
    refine ⟨22072196809527875499248569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117718382984148669329325701 22072196809527875499248569)
    ·
      refine ⟨16554147607145906624436427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22072196809527875499248569 16554147607145906624436427)
      ·
        refine ⟨24831221410718859936654641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16554147607145906624436427 24831221410718859936654641)
        ·
          refine ⟨18623416058039144952490981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24831221410718859936654641 18623416058039144952490981)
          ·
            refine ⟨3491890510882339678592059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18623416058039144952490981 3491890510882339678592059)
            ·
              refine ⟨5237835766323509517888089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491890510882339678592059 5237835766323509517888089)
              ·
                refine ⟨3928376824742632138416067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237835766323509517888089 3928376824742632138416067)
                ·
                  refine ⟨5892565237113948207624101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928376824742632138416067 5892565237113948207624101)
                  ·
                    refine ⟨1104855981958865288929519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892565237113948207624101 1104855981958865288929519)
                    ·
                      rfl

theorem cell22_3227549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3227549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227549 prefixEnd_3227549 := by exact prefixLift 3227549
  have htrace : WordTrace (prefixWord ++ tailWord_3227549) baseStart_3227549 baseEnd_3227549 := by
    simpa [prefixWord, tailWord_3227549, baseEnd_3227549] using wordTrace_append hprefix tailTrace_3227549
  have hstable : (prefixWord ++ tailWord_3227549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227549).length < 2 ^ (prefixWord ++ tailWord_3227549).sum := by decide
  have hdescent : baseEnd_3227549 < baseStart_3227549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227581 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 4]
def baseStart_3227581 : Nat := 118140960795 + 3227581 * 2 ^ 59
def prefixEnd_3227581 : Nat := 4983230072969 + 3 ^ 40 * 3227581 * 2
def baseEnd_3227581 : Nat := 368288978737609290709807

theorem tailTrace_3227581 : CollatzResearch.WordTrace tailWord_3227581 prefixEnd_3227581 368288978737609290709807 := by
  unfold tailWord_3227581
  simp only [CollatzResearch.WordTrace]
  refine ⟨117719550120032738794490597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78479700080021825862993731 117719550120032738794490597)
  ·
    refine ⟨22072415647506138523966987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117719550120032738794490597 22072415647506138523966987)
    ·
      refine ⟨33108623471259207785950481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072415647506138523966987 33108623471259207785950481)
      ·
        refine ⟨24831467603444405839462861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33108623471259207785950481 24831467603444405839462861)
        ·
          refine ⟨9311800351291652189798573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24831467603444405839462861 9311800351291652189798573)
          ·
            refine ⟨3491925131734369571174465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9311800351291652189798573 3491925131734369571174465)
            ·
              refine ⟨2618943848800777178380849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491925131734369571174465 2618943848800777178380849)
              ·
                refine ⟨1964207886600582883785637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618943848800777178380849 1964207886600582883785637)
                ·
                  refine ⟨368288978737609290709807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964207886600582883785637 368288978737609290709807)
                  ·
                    rfl

theorem cell22_3227581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_3227581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227581 prefixEnd_3227581 := by exact prefixLift 3227581
  have htrace : WordTrace (prefixWord ++ tailWord_3227581) baseStart_3227581 baseEnd_3227581 := by
    simpa [prefixWord, tailWord_3227581, baseEnd_3227581] using wordTrace_append hprefix tailTrace_3227581
  have hstable : (prefixWord ++ tailWord_3227581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227581).length < 2 ^ (prefixWord ++ tailWord_3227581).sum := by decide
  have hdescent : baseEnd_3227581 < baseStart_3227581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227592 : List Nat := [2, 1, 3, 1, 4, 3, 1, 7]
def baseStart_3227592 : Nat := 118140960795 + 3227592 * 2 ^ 59
def prefixEnd_3227592 : Nat := 4983230072969 + 3 ^ 40 * 3227592 * 2
def baseEnd_3227592 : Nat := 122763411304180834456043

theorem tailTrace_3227592 : CollatzResearch.WordTrace tailWord_3227592 prefixEnd_3227592 122763411304180834456043 := by
  unfold tailWord_3227592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58859975661496443836570515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78479967548661925115427353 58859975661496443836570515)
  ·
    refine ⟨88289963492244665754855773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58859975661496443836570515 88289963492244665754855773)
    ·
      refine ⟨33108736309591749658070915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88289963492244665754855773 33108736309591749658070915)
      ·
        refine ⟨49663104464387624487106373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33108736309591749658070915 49663104464387624487106373)
        ·
          refine ⟨9311832087072679591332445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49663104464387624487106373 9311832087072679591332445)
          ·
            refine ⟨3491937032652254846749667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9311832087072679591332445 3491937032652254846749667)
            ·
              refine ⟨5237905548978382270124501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491937032652254846749667 5237905548978382270124501)
              ·
                refine ⟨122763411304180834456043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5237905548978382270124501 122763411304180834456043)
                ·
                  rfl

theorem cell22_3227592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_3227592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227592 prefixEnd_3227592 := by exact prefixLift 3227592
  have htrace : WordTrace (prefixWord ++ tailWord_3227592) baseStart_3227592 baseEnd_3227592 := by
    simpa [prefixWord, tailWord_3227592, baseEnd_3227592] using wordTrace_append hprefix tailTrace_3227592
  have hstable : (prefixWord ++ tailWord_3227592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227592).length < 2 ^ (prefixWord ++ tailWord_3227592).sum := by decide
  have hdescent : baseEnd_3227592 < baseStart_3227592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227607 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 3, 3]
def baseStart_3227607 : Nat := 118140960795 + 3227607 * 2 ^ 59
def prefixEnd_3227607 : Nat := 4983230072969 + 3 ^ 40 * 3227607 * 2
def baseEnd_3227607 : Nat := 1104875836544172470979341

theorem tailTrace_3227607 : CollatzResearch.WordTrace tailWord_3227607 prefixEnd_3227607 1104875836544172470979341 := by
  unfold tailWord_3227607
  simp only [CollatzResearch.WordTrace]
  refine ⟨117720498417938545234937075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78480332278625696823291383 117720498417938545234937075)
  ·
    refine ⟨176580747626907817852405613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117720498417938545234937075 176580747626907817852405613)
    ·
      refine ⟨66217780360090431694652105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176580747626907817852405613 66217780360090431694652105)
      ·
        refine ⟨49663335270067823770989079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66217780360090431694652105 49663335270067823770989079)
        ·
          refine ⟨74495002905101735656483619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49663335270067823770989079 74495002905101735656483619)
          ·
            refine ⟨111742504357652603484725429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74495002905101735656483619 111742504357652603484725429)
            ·
              refine ⟨10475859783529931576693009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111742504357652603484725429 10475859783529931576693009)
              ·
                refine ⟨7856894837647448682519757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10475859783529931576693009 7856894837647448682519757)
                ·
                  refine ⟨2946335564117793255944909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7856894837647448682519757 2946335564117793255944909)
                  ·
                    refine ⟨1104875836544172470979341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2946335564117793255944909 1104875836544172470979341)
                    ·
                      rfl

theorem cell22_3227607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_3227607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227607 prefixEnd_3227607 := by exact prefixLift 3227607
  have htrace : WordTrace (prefixWord ++ tailWord_3227607) baseStart_3227607 baseEnd_3227607 := by
    simpa [prefixWord, tailWord_3227607, baseEnd_3227607] using wordTrace_append hprefix tailTrace_3227607
  have hstable : (prefixWord ++ tailWord_3227607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227607).length < 2 ^ (prefixWord ++ tailWord_3227607).sum := by decide
  have hdescent : baseEnd_3227607 < baseStart_3227607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227620 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3227620 : Nat := 118140960795 + 3227620 * 2 ^ 59
def prefixEnd_3227620 : Nat := 4983230072969 + 3 ^ 40 * 3227620 * 2
def baseEnd_3227620 : Nat := 368293428903281590134767

theorem tailTrace_3227620 : CollatzResearch.WordTrace tailWord_3227620 prefixEnd_3227620 368293428903281590134767 := by
  unfold tailWord_3227620
  simp only [CollatzResearch.WordTrace]
  refine ⟨58860486283445724227580157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78480648377927632303440209 58860486283445724227580157)
  ·
    refine ⟨22072682356292146585342559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58860486283445724227580157 22072682356292146585342559)
    ·
      refine ⟨33109023534438219878013839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072682356292146585342559 33109023534438219878013839)
      ·
        refine ⟨49663535301657329817020759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33109023534438219878013839 49663535301657329817020759)
        ·
          refine ⟨74495302952485994725531139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49663535301657329817020759 74495302952485994725531139)
          ·
            refine ⟨111742954428728992088296709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74495302952485994725531139 111742954428728992088296709)
            ·
              refine ⟨20951803955386686016555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111742954428728992088296709 20951803955386686016555633)
              ·
                refine ⟨15713852966540014512416725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20951803955386686016555633 15713852966540014512416725)
                ·
                  refine ⟨368293428903281590134767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15713852966540014512416725 368293428903281590134767)
                  ·
                    rfl

theorem cell22_3227620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3227620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227620 prefixEnd_3227620 := by exact prefixLift 3227620
  have htrace : WordTrace (prefixWord ++ tailWord_3227620) baseStart_3227620 baseEnd_3227620 := by
    simpa [prefixWord, tailWord_3227620, baseEnd_3227620] using wordTrace_append hprefix tailTrace_3227620
  have hstable : (prefixWord ++ tailWord_3227620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227620).length < 2 ^ (prefixWord ++ tailWord_3227620).sum := by decide
  have hdescent : baseEnd_3227620 < baseStart_3227620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227667 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 1, 4]
def baseStart_3227667 : Nat := 118140960795 + 3227667 * 2 ^ 59
def prefixEnd_3227667 : Nat := 4983230072969 + 3 ^ 40 * 3227667 * 2
def baseEnd_3227667 : Nat := 1104896375770352314479157

theorem tailTrace_3227667 : CollatzResearch.WordTrace tailWord_3227667 prefixEnd_3227667 1104896375770352314479157 := by
  unfold tailWord_3227667
  simp only [CollatzResearch.WordTrace]
  refine ⟨117722686797721175482121255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78481791198480783654747503 117722686797721175482121255)
  ·
    refine ⟨176584030196581763223181883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117722686797721175482121255 176584030196581763223181883)
    ·
      refine ⟨264876045294872644834772825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176584030196581763223181883 264876045294872644834772825)
      ·
        refine ⟨198657033971154483626079619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264876045294872644834772825 198657033971154483626079619)
        ·
          refine ⟨297985550956731725439119429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198657033971154483626079619 297985550956731725439119429)
          ·
            refine ⟨55872290804387198519834893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297985550956731725439119429 55872290804387198519834893)
            ·
              refine ⟨20952109051645199444938085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55872290804387198519834893 20952109051645199444938085)
              ·
                refine ⟨3928520447183474895925891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20952109051645199444938085 3928520447183474895925891)
                ·
                  refine ⟨5892780670775212343888837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928520447183474895925891 5892780670775212343888837)
                  ·
                    refine ⟨1104896375770352314479157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892780670775212343888837 1104896375770352314479157)
                    ·
                      rfl

theorem cell22_3227667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_3227667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227667 prefixEnd_3227667 := by exact prefixLift 3227667
  have htrace : WordTrace (prefixWord ++ tailWord_3227667) baseStart_3227667 baseEnd_3227667 := by
    simpa [prefixWord, tailWord_3227667, baseEnd_3227667] using wordTrace_append hprefix tailTrace_3227667
  have hstable : (prefixWord ++ tailWord_3227667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227667).length < 2 ^ (prefixWord ++ tailWord_3227667).sum := by decide
  have hdescent : baseEnd_3227667 < baseStart_3227667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227695 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_3227695 : Nat := 118140960795 + 3227695 * 2 ^ 59
def prefixEnd_3227695 : Nat := 4983230072969 + 3 ^ 40 * 3227695 * 2
def baseEnd_3227695 : Nat := 1104905960742569574779071

theorem tailTrace_3227695 : CollatzResearch.WordTrace tailWord_3227695 prefixEnd_3227695 1104905960742569574779071 := by
  unfold tailWord_3227695
  simp only [CollatzResearch.WordTrace]
  refine ⟨117723708041619736264140539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78482472027746490842760359 117723708041619736264140539)
  ·
    refine ⟨176585562062429604396210809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117723708041619736264140539 176585562062429604396210809)
    ·
      refine ⟨132439171546822203297158107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176585562062429604396210809 132439171546822203297158107)
      ·
        refine ⟨198658757320233304945737161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132439171546822203297158107 198658757320233304945737161)
        ·
          refine ⟨148994067990174978709302871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198658757320233304945737161 148994067990174978709302871)
          ·
            refine ⟨223491101985262468063954307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148994067990174978709302871 223491101985262468063954307)
            ·
              refine ⟨335236652977893702095931461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223491101985262468063954307 335236652977893702095931461)
              ·
                refine ⟨62856872433355069142987149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335236652977893702095931461 62856872433355069142987149)
                ·
                  refine ⟨23571327162508150928620181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62856872433355069142987149 23571327162508150928620181)
                  ·
                    refine ⟨1104905960742569574779071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23571327162508150928620181 1104905960742569574779071)
                    ·
                      rfl

theorem cell22_3227695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_3227695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227695 prefixEnd_3227695 := by exact prefixLift 3227695
  have htrace : WordTrace (prefixWord ++ tailWord_3227695) baseStart_3227695 baseEnd_3227695 := by
    simpa [prefixWord, tailWord_3227695, baseEnd_3227695] using wordTrace_append hprefix tailTrace_3227695
  have hstable : (prefixWord ++ tailWord_3227695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227695).length < 2 ^ (prefixWord ++ tailWord_3227695).sum := by decide
  have hdescent : baseEnd_3227695 < baseStart_3227695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227757 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3227757 : Nat := 118140960795 + 3227757 * 2 ^ 59
def prefixEnd_3227757 : Nat := 4983230072969 + 3 ^ 40 * 3227757 * 2
def baseEnd_3227757 : Nat := 1104927184609622079728881

theorem tailTrace_3227757 : CollatzResearch.WordTrace tailWord_3227757 prefixEnd_3227757 1104927184609622079728881 := by
  unfold tailWord_3227757
  simp only [CollatzResearch.WordTrace]
  refine ⟨117725969367395120852897525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78483979578263413901931683 117725969367395120852897525)
  ·
    refine ⟨11036809628193292579959143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117725969367395120852897525 11036809628193292579959143)
    ·
      refine ⟨16555214442289938869938715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11036809628193292579959143 16555214442289938869938715)
      ·
        refine ⟨24832821663434908304908073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16555214442289938869938715 24832821663434908304908073)
        ·
          refine ⟨18624616247576181228681055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24832821663434908304908073 18624616247576181228681055)
          ·
            refine ⟨27936924371364271843021583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624616247576181228681055 27936924371364271843021583)
            ·
              refine ⟨41905386557046407764532375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27936924371364271843021583 41905386557046407764532375)
              ·
                refine ⟨62858079835569611646798563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41905386557046407764532375 62858079835569611646798563)
                ·
                  refine ⟨94287119753354417470197845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62858079835569611646798563 94287119753354417470197845)
                  ·
                    refine ⟨1104927184609622079728881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94287119753354417470197845 1104927184609622079728881)
                    ·
                      rfl

theorem cell22_3227757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3227757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227757 prefixEnd_3227757 := by exact prefixLift 3227757
  have htrace : WordTrace (prefixWord ++ tailWord_3227757) baseStart_3227757 baseEnd_3227757 := by
    simpa [prefixWord, tailWord_3227757, baseEnd_3227757] using wordTrace_append hprefix tailTrace_3227757
  have hstable : (prefixWord ++ tailWord_3227757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227757).length < 2 ^ (prefixWord ++ tailWord_3227757).sum := by decide
  have hdescent : baseEnd_3227757 < baseStart_3227757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227806 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3227806 : Nat := 118140960795 + 3227806 * 2 ^ 59
def prefixEnd_3227806 : Nat := 4983230072969 + 3 ^ 40 * 3227806 * 2
def baseEnd_3227806 : Nat := 368314652770334095084577

theorem tailTrace_3227806 : CollatzResearch.WordTrace tailWord_3227806 prefixEnd_3227806 368314652770334095084577 := by
  unfold tailWord_3227806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715969568027200277678909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78485171029478401480954181 14715969568027200277678909)
  ·
    refine ⟨5518488588010200104129591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14715969568027200277678909 5518488588010200104129591)
    ·
      refine ⟨8277732882015300156194387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518488588010200104129591 8277732882015300156194387)
      ·
        refine ⟨12416599323022950234291581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277732882015300156194387 12416599323022950234291581)
        ·
          refine ⟨4656224746133606337859343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12416599323022950234291581 4656224746133606337859343)
          ·
            refine ⟨6984337119200409506789015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656224746133606337859343 6984337119200409506789015)
            ·
              refine ⟨10476505678800614260183523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984337119200409506789015 10476505678800614260183523)
              ·
                refine ⟨15714758518200921390275285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476505678800614260183523 15714758518200921390275285)
                ·
                  refine ⟨368314652770334095084577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15714758518200921390275285 368314652770334095084577)
                  ·
                    rfl

theorem cell22_3227806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3227806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227806 prefixEnd_3227806 := by exact prefixLift 3227806
  have htrace : WordTrace (prefixWord ++ tailWord_3227806) baseStart_3227806 baseEnd_3227806 := by
    simpa [prefixWord, tailWord_3227806, baseEnd_3227806] using wordTrace_append hprefix tailTrace_3227806
  have hstable : (prefixWord ++ tailWord_3227806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227806).length < 2 ^ (prefixWord ++ tailWord_3227806).sum := by decide
  have hdescent : baseEnd_3227806 < baseStart_3227806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227864 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3227864 : Nat := 118140960795 + 3227864 * 2 ^ 59
def prefixEnd_3227864 : Nat := 4983230072969 + 3 ^ 40 * 3227864 * 2
def baseEnd_3227864 : Nat := 1104963812896309467303553

theorem tailTrace_3227864 : CollatzResearch.WordTrace tailWord_3227864 prefixEnd_3227864 1104963812896309467303553 := by
  unfold tailWord_3227864
  simp only [CollatzResearch.WordTrace]
  refine ⟨58864935989003739063521323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78486581318671652084695097 58864935989003739063521323)
  ·
    refine ⟨88297403983505608595281985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58864935989003739063521323 88297403983505608595281985)
    ·
      refine ⟨66223052987629206446461489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88297403983505608595281985 66223052987629206446461489)
      ·
        refine ⟨49667289740721904834846117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66223052987629206446461489 49667289740721904834846117)
        ·
          refine ⟨9312616826385357156533647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49667289740721904834846117 9312616826385357156533647)
          ·
            refine ⟨13968925239578035734800471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312616826385357156533647 13968925239578035734800471)
            ·
              refine ⟨20953387859367053602200707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968925239578035734800471 20953387859367053602200707)
              ·
                refine ⟨31430081789050580403301061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20953387859367053602200707 31430081789050580403301061)
                ·
                  refine ⟨5893140335446983825618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31430081789050580403301061 5893140335446983825618949)
                  ·
                    refine ⟨1104963812896309467303553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893140335446983825618949 1104963812896309467303553)
                    ·
                      rfl

theorem cell22_3227864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3227864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227864 prefixEnd_3227864 := by exact prefixLift 3227864
  have htrace : WordTrace (prefixWord ++ tailWord_3227864) baseStart_3227864 baseEnd_3227864 := by
    simpa [prefixWord, tailWord_3227864, baseEnd_3227864] using wordTrace_append hprefix tailTrace_3227864
  have hstable : (prefixWord ++ tailWord_3227864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227864).length < 2 ^ (prefixWord ++ tailWord_3227864).sum := by decide
  have hdescent : baseEnd_3227864 < baseStart_3227864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227874 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3227874 : Nat := 118140960795 + 3227874 * 2 ^ 59
def prefixEnd_3227874 : Nat := 4983230072969 + 3 ^ 40 * 3227874 * 2
def baseEnd_3227874 : Nat := 368322412033557591517841

theorem tailTrace_3227874 : CollatzResearch.WordTrace tailWord_3227874 prefixEnd_3227874 368322412033557591517841 := by
  unfold tailWord_3227874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29432559176992812458726669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78486824471980833223271117 29432559176992812458726669)
  ·
    refine ⟨11037209691372304672022501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29432559176992812458726669 11037209691372304672022501)
    ·
      refine ⟨2069476817132307126004219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11037209691372304672022501 2069476817132307126004219)
      ·
        refine ⟨3104215225698460689006329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069476817132307126004219 3104215225698460689006329)
        ·
          refine ⟨2328161419273845516754747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104215225698460689006329 2328161419273845516754747)
          ·
            refine ⟨3492242128910768275132121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328161419273845516754747 3492242128910768275132121)
            ·
              refine ⟨2619181596683076206349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492242128910768275132121 2619181596683076206349091)
              ·
                refine ⟨3928772395024614309523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619181596683076206349091 3928772395024614309523637)
                ·
                  refine ⟨368322412033557591517841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928772395024614309523637 368322412033557591517841)
                  ·
                    rfl

theorem cell22_3227874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3227874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227874 prefixEnd_3227874 := by exact prefixLift 3227874
  have htrace : WordTrace (prefixWord ++ tailWord_3227874) baseStart_3227874 baseEnd_3227874 := by
    simpa [prefixWord, tailWord_3227874, baseEnd_3227874] using wordTrace_append hprefix tailTrace_3227874
  have hstable : (prefixWord ++ tailWord_3227874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227874).length < 2 ^ (prefixWord ++ tailWord_3227874).sum := by decide
  have hdescent : baseEnd_3227874 < baseStart_3227874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227879 : List Nat := [1, 1, 5, 3, 1, 1, 1, 9]
def baseStart_3227879 : Nat := 118140960795 + 3227879 * 2 ^ 59
def prefixEnd_3227879 : Nat := 4983230072969 + 3 ^ 40 * 3227879 * 2
def baseEnd_3227879 : Nat := 122774327522539380908723

theorem tailTrace_3227879 : CollatzResearch.WordTrace tailWord_3227879 prefixEnd_3227879 122774327522539380908723 := by
  unfold tailWord_3227879
  simp only [CollatzResearch.WordTrace]
  refine ⟨117730419072953135688838691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78486946048635423792559127 117730419072953135688838691)
  ·
    refine ⟨176595628609429703533258037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117730419072953135688838691 176595628609429703533258037)
    ·
      refine ⟨16555840182134034706242941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176595628609429703533258037 16555840182134034706242941)
      ·
        refine ⟨6208440068300263014841103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16555840182134034706242941 6208440068300263014841103)
        ·
          refine ⟨9312660102450394522261655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208440068300263014841103 9312660102450394522261655)
          ·
            refine ⟨13968990153675591783392483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312660102450394522261655 13968990153675591783392483)
            ·
              refine ⟨20953485230513387675088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968990153675591783392483 20953485230513387675088725)
              ·
                refine ⟨122774327522539380908723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20953485230513387675088725 122774327522539380908723)
                ·
                  rfl

theorem cell22_3227879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 9].length) (baseStart_3227879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227879 prefixEnd_3227879 := by exact prefixLift 3227879
  have htrace : WordTrace (prefixWord ++ tailWord_3227879) baseStart_3227879 baseEnd_3227879 := by
    simpa [prefixWord, tailWord_3227879, baseEnd_3227879] using wordTrace_append hprefix tailTrace_3227879
  have hstable : (prefixWord ++ tailWord_3227879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227879).length < 2 ^ (prefixWord ++ tailWord_3227879).sum := by decide
  have hdescent : baseEnd_3227879 < baseStart_3227879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227894 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3227894 : Nat := 118140960795 + 3227894 * 2 ^ 59
def prefixEnd_3227894 : Nat := 4983230072969 + 3 ^ 40 * 3227894 * 2
def baseEnd_3227894 : Nat := 1104974082509399389053461

theorem tailTrace_3227894 : CollatzResearch.WordTrace tailWord_3227894 prefixEnd_3227894 1104974082509399389053461 := by
  unfold tailWord_3227894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358185385493674578164671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78487310778599195500423157 7358185385493674578164671)
  ·
    refine ⟨11037278078240511867247007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7358185385493674578164671 11037278078240511867247007)
    ·
      refine ⟨16555917117360767800870511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11037278078240511867247007 16555917117360767800870511)
      ·
        refine ⟨24833875676041151701305767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16555917117360767800870511 24833875676041151701305767)
        ·
          refine ⟨37250813514061727551958651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24833875676041151701305767 37250813514061727551958651)
          ·
            refine ⟨55876220271092591327937977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37250813514061727551958651 55876220271092591327937977)
            ·
              refine ⟨41907165203319443495953483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55876220271092591327937977 41907165203319443495953483)
              ·
                refine ⟨62860747804979165243930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41907165203319443495953483 62860747804979165243930225)
                ·
                  refine ⟨47145560853734373932947669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62860747804979165243930225 47145560853734373932947669)
                  ·
                    refine ⟨1104974082509399389053461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47145560853734373932947669 1104974082509399389053461)
                    ·
                      rfl

theorem cell22_3227894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3227894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227894 prefixEnd_3227894 := by exact prefixLift 3227894
  have htrace : WordTrace (prefixWord ++ tailWord_3227894) baseStart_3227894 baseEnd_3227894 := by
    simpa [prefixWord, tailWord_3227894, baseEnd_3227894] using wordTrace_append hprefix tailTrace_3227894
  have hstable : (prefixWord ++ tailWord_3227894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227894).length < 2 ^ (prefixWord ++ tailWord_3227894).sum := by decide
  have hdescent : baseEnd_3227894 < baseStart_3227894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227928 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_3227928 : Nat := 118140960795 + 3227928 * 2 ^ 59
def prefixEnd_3227928 : Nat := 4983230072969 + 3 ^ 40 * 3227928 * 2
def baseEnd_3227928 : Nat := 1104985721404234633703357

theorem tailTrace_3227928 : CollatzResearch.WordTrace tailWord_3227928 prefixEnd_3227928 1104985721404234633703357 := by
  unfold tailWord_3227928
  simp only [CollatzResearch.WordTrace]
  refine ⟨58866103124887808528686219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78488137499850411371581625 58866103124887808528686219)
  ·
    refine ⟨88299154687331712793029329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58866103124887808528686219 88299154687331712793029329)
    ·
      refine ⟨66224366015498784594771997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88299154687331712793029329 66224366015498784594771997)
      ·
        refine ⟨24834137255812044223039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66224366015498784594771997 24834137255812044223039499)
        ·
          refine ⟨37251205883718066334559249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24834137255812044223039499 37251205883718066334559249)
          ·
            refine ⟨27938404412788549750919437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37251205883718066334559249 27938404412788549750919437)
            ·
              refine ⟨10476901654795706156594789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27938404412788549750919437 10476901654795706156594789)
              ·
                refine ⟨1964419060274194904361523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10476901654795706156594789 1964419060274194904361523)
                ·
                  refine ⟨2946628590411292356542285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964419060274194904361523 2946628590411292356542285)
                  ·
                    refine ⟨1104985721404234633703357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2946628590411292356542285 1104985721404234633703357)
                    ·
                      rfl

theorem cell22_3227928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_3227928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227928 prefixEnd_3227928 := by exact prefixLift 3227928
  have htrace : WordTrace (prefixWord ++ tailWord_3227928) baseStart_3227928 baseEnd_3227928 := by
    simpa [prefixWord, tailWord_3227928, baseEnd_3227928] using wordTrace_append hprefix tailTrace_3227928
  have hstable : (prefixWord ++ tailWord_3227928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227928).length < 2 ^ (prefixWord ++ tailWord_3227928).sum := by decide
  have hdescent : baseEnd_3227928 < baseStart_3227928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227939 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_3227939 : Nat := 118140960795 + 3227939 * 2 ^ 59
def prefixEnd_3227939 : Nat := 4983230072969 + 3 ^ 40 * 3227939 * 2
def baseEnd_3227939 : Nat := 1104989486929034271678323

theorem tailTrace_3227939 : CollatzResearch.WordTrace tailWord_3227939 prefixEnd_3227939 1104989486929034271678323 := by
  unfold tailWord_3227939
  simp only [CollatzResearch.WordTrace]
  refine ⟨117732607452735765936022871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78488404968490510624015247 117732607452735765936022871)
  ·
    refine ⟨176598911179103648904034307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117732607452735765936022871 176598911179103648904034307)
    ·
      refine ⟨264898366768655473356051461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176598911179103648904034307 264898366768655473356051461)
      ·
        refine ⟨49668443769122901254259649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264898366768655473356051461 49668443769122901254259649)
        ·
          refine ⟨37251332826842175940694737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49668443769122901254259649 37251332826842175940694737)
          ·
            refine ⟨27938499620131631955521053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37251332826842175940694737 27938499620131631955521053)
            ·
              refine ⟨10476937357549361983320395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27938499620131631955521053 10476937357549361983320395)
              ·
                refine ⟨15715406036324042974980593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476937357549361983320395 15715406036324042974980593)
                ·
                  refine ⟨11786554527243032231235445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15715406036324042974980593 11786554527243032231235445)
                  ·
                    refine ⟨1104989486929034271678323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11786554527243032231235445 1104989486929034271678323)
                    ·
                      rfl

theorem cell22_3227939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_3227939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227939 prefixEnd_3227939 := by exact prefixLift 3227939
  have htrace : WordTrace (prefixWord ++ tailWord_3227939) baseStart_3227939 baseEnd_3227939 := by
    simpa [prefixWord, tailWord_3227939, baseEnd_3227939] using wordTrace_append hprefix tailTrace_3227939
  have hstable : (prefixWord ++ tailWord_3227939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227939).length < 2 ^ (prefixWord ++ tailWord_3227939).sum := by decide
  have hdescent : baseEnd_3227939 < baseStart_3227939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227999 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_3227999 : Nat := 118140960795 + 3227999 * 2 ^ 59
def prefixEnd_3227999 : Nat := 4983230072969 + 3 ^ 40 * 3227999 * 2
def baseEnd_3227999 : Nat := 1105010026155214115178139

theorem tailTrace_3227999 : CollatzResearch.WordTrace tailWord_3227999 prefixEnd_3227999 1105010026155214115178139 := by
  unfold tailWord_3227999
  simp only [CollatzResearch.WordTrace]
  refine ⟨117734795832518396183207051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78489863888345597455471367 117734795832518396183207051)
  ·
    refine ⟨176602193748777594274810577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117734795832518396183207051 176602193748777594274810577)
    ·
      refine ⟨132451645311583195706107933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176602193748777594274810577 132451645311583195706107933)
      ·
        refine ⟨49669366991843698389790475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132451645311583195706107933 49669366991843698389790475)
        ·
          refine ⟨74504050487765547584685713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49669366991843698389790475 74504050487765547584685713)
          ·
            refine ⟨55878037865824160688514285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74504050487765547584685713 55878037865824160688514285)
            ·
              refine ⟨20954264199684060258192857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55878037865824160688514285 20954264199684060258192857)
              ·
                refine ⟨15715698149763045193644643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20954264199684060258192857 15715698149763045193644643)
                ·
                  refine ⟨23573547224644567790466965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15715698149763045193644643 23573547224644567790466965)
                  ·
                    refine ⟨1105010026155214115178139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23573547224644567790466965 1105010026155214115178139)
                    ·
                      rfl

theorem cell22_3227999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_3227999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3227999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3227999 prefixEnd_3227999 := by exact prefixLift 3227999
  have htrace : WordTrace (prefixWord ++ tailWord_3227999) baseStart_3227999 baseEnd_3227999 := by
    simpa [prefixWord, tailWord_3227999, baseEnd_3227999] using wordTrace_append hprefix tailTrace_3227999
  have hstable : (prefixWord ++ tailWord_3227999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227999).length < 2 ^ (prefixWord ++ tailWord_3227999).sum := by decide
  have hdescent : baseEnd_3227999 < baseStart_3227999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228033 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3228033 : Nat := 118140960795 + 3228033 * 2 ^ 59
def prefixEnd_3228033 : Nat := 4983230072969 + 3 ^ 40 * 3228033 * 2
def baseEnd_3228033 : Nat := 1105021665050049359828035

theorem tailTrace_3228033 : CollatzResearch.WordTrace tailWord_3228033 prefixEnd_3228033 1105021665050049359828035 := by
  unfold tailWord_3228033
  simp only [CollatzResearch.WordTrace]
  refine ⟨117736035914395219989944753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78490690609596813326629835 117736035914395219989944753)
  ·
    refine ⟨88302026935796414992458565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117736035914395219989944753 88302026935796414992458565)
    ·
      refine ⟨16556630050461827811085981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88302026935796414992458565 16556630050461827811085981)
      ·
        refine ⟨6208736268923185429157243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16556630050461827811085981 6208736268923185429157243)
        ·
          refine ⟨9313104403384778143735865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208736268923185429157243 9313104403384778143735865)
          ·
            refine ⟨6984828302538583607801899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9313104403384778143735865 6984828302538583607801899)
            ·
              refine ⟨10477242453807875411702849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984828302538583607801899 10477242453807875411702849)
              ·
                refine ⟨7857931840355906558777137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477242453807875411702849 7857931840355906558777137)
                ·
                  refine ⟨5893448880266929919082853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7857931840355906558777137 5893448880266929919082853)
                  ·
                    refine ⟨1105021665050049359828035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893448880266929919082853 1105021665050049359828035)
                    ·
                      rfl

theorem cell22_3228033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3228033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228033 prefixEnd_3228033 := by exact prefixLift 3228033
  have htrace : WordTrace (prefixWord ++ tailWord_3228033) baseStart_3228033 baseEnd_3228033 := by
    simpa [prefixWord, tailWord_3228033, baseEnd_3228033] using wordTrace_append hprefix tailTrace_3228033
  have hstable : (prefixWord ++ tailWord_3228033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228033).length < 2 ^ (prefixWord ++ tailWord_3228033).sum := by decide
  have hdescent : baseEnd_3228033 < baseStart_3228033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228093 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3228093 : Nat := 118140960795 + 3228093 * 2 ^ 59
def prefixEnd_3228093 : Nat := 4983230072969 + 3 ^ 40 * 3228093 * 2
def baseEnd_3228093 : Nat := 368347401425409734442617

theorem tailTrace_3228093 : CollatzResearch.WordTrace tailWord_3228093 prefixEnd_3228093 368347401425409734442617 := by
  unfold tailWord_3228093
  simp only [CollatzResearch.WordTrace]
  refine ⟨117738224294177850237128933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78492149529451900158085955 117738224294177850237128933)
  ·
    refine ⟨22075917055158346919461675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117738224294177850237128933 22075917055158346919461675)
    ·
      refine ⟨33113875582737520379192513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22075917055158346919461675 33113875582737520379192513)
      ·
        refine ⟨24835406687053140284394385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33113875582737520379192513 24835406687053140284394385)
        ·
          refine ⟨18626555015289855213295789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24835406687053140284394385 18626555015289855213295789)
          ·
            refine ⟨6984958130733695704985921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18626555015289855213295789 6984958130733695704985921)
            ·
              refine ⟨5238718598050271778739441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6984958130733695704985921 5238718598050271778739441)
              ·
                refine ⟨3929038948537703834054581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238718598050271778739441 3929038948537703834054581)
                ·
                  refine ⟨368347401425409734442617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3929038948537703834054581 368347401425409734442617)
                  ·
                    rfl

theorem cell22_3228093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3228093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228093 prefixEnd_3228093 := by exact prefixLift 3228093
  have htrace : WordTrace (prefixWord ++ tailWord_3228093) baseStart_3228093 baseEnd_3228093 := by
    simpa [prefixWord, tailWord_3228093, baseEnd_3228093] using wordTrace_append hprefix tailTrace_3228093
  have hstable : (prefixWord ++ tailWord_3228093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228093).length < 2 ^ (prefixWord ++ tailWord_3228093).sum := by decide
  have hdescent : baseEnd_3228093 < baseStart_3228093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228106 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_3228106 : Nat := 118140960795 + 3228106 * 2 ^ 59
def prefixEnd_3228106 : Nat := 4983230072969 + 3 ^ 40 * 3228106 * 2
def baseEnd_3228106 : Nat := 1105046654441901502752811

theorem tailTrace_3228106 : CollatzResearch.WordTrace tailWord_3228106 prefixEnd_3228106 1105046654441901502752811 := by
  unfold tailWord_3228106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29434674610782688364338043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78492465628753835638234781 29434674610782688364338043)
  ·
    refine ⟨44152011916174032546507065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29434674610782688364338043 44152011916174032546507065)
    ·
      refine ⟨33114008937130524409880299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44152011916174032546507065 33114008937130524409880299)
      ·
        refine ⟨49671013405695786614820449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33114008937130524409880299 49671013405695786614820449)
        ·
          refine ⟨37253260054271839961115337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49671013405695786614820449 37253260054271839961115337)
          ·
            refine ⟨27939945040703879970836503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37253260054271839961115337 27939945040703879970836503)
            ·
              refine ⟨41909917561055819956254755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27939945040703879970836503 41909917561055819956254755)
              ·
                refine ⟨62864876341583729934382133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41909917561055819956254755 62864876341583729934382133)
                ·
                  refine ⟨5893582157023474681348325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62864876341583729934382133 5893582157023474681348325)
                  ·
                    refine ⟨1105046654441901502752811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893582157023474681348325 1105046654441901502752811)
                    ·
                      rfl

theorem cell22_3228106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3228106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228106 prefixEnd_3228106 := by exact prefixLift 3228106
  have htrace : WordTrace (prefixWord ++ tailWord_3228106) baseStart_3228106 baseEnd_3228106 := by
    simpa [prefixWord, tailWord_3228106, baseEnd_3228106] using wordTrace_append hprefix tailTrace_3228106
  have hstable : (prefixWord ++ tailWord_3228106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228106).length < 2 ^ (prefixWord ++ tailWord_3228106).sum := by decide
  have hdescent : baseEnd_3228106 < baseStart_3228106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228108 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_3228108 : Nat := 118140960795 + 3228108 * 2 ^ 59
def prefixEnd_3228108 : Nat := 4983230072969 + 3 ^ 40 * 3228108 * 2
def baseEnd_3228108 : Nat := 1105047339082774164202805

theorem tailTrace_3228108 : CollatzResearch.WordTrace tailWord_3228108 prefixEnd_3228108 1105047339082774164202805 := by
  unfold tailWord_3228108
  simp only [CollatzResearch.WordTrace]
  refine ⟨58869385694561753899462489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78492514259415671865949985 58869385694561753899462489)
  ·
    refine ⟨44152039270921315424596867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58869385694561753899462489 44152039270921315424596867)
    ·
      refine ⟨66228058906381973136895301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44152039270921315424596867 66228058906381973136895301)
      ·
        refine ⟨12417761044946619963167869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66228058906381973136895301 12417761044946619963167869)
        ·
          refine ⟨4656660391854982486187951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12417761044946619963167869 4656660391854982486187951)
          ·
            refine ⟨6984990587782473729281927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656660391854982486187951 6984990587782473729281927)
            ·
              refine ⟨10477485881673710593922891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984990587782473729281927 10477485881673710593922891)
              ·
                refine ⟨15716228822510565890884337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10477485881673710593922891 15716228822510565890884337)
                ·
                  refine ⟨11787171616882924418163253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15716228822510565890884337 11787171616882924418163253)
                  ·
                    refine ⟨1105047339082774164202805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11787171616882924418163253 1105047339082774164202805)
                    ·
                      rfl

theorem cell22_3228108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_3228108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228108 prefixEnd_3228108 := by exact prefixLift 3228108
  have htrace : WordTrace (prefixWord ++ tailWord_3228108) baseStart_3228108 baseEnd_3228108 := by
    simpa [prefixWord, tailWord_3228108, baseEnd_3228108] using wordTrace_append hprefix tailTrace_3228108
  have hstable : (prefixWord ++ tailWord_3228108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228108).length < 2 ^ (prefixWord ++ tailWord_3228108).sum := by decide
  have hdescent : baseEnd_3228108 < baseStart_3228108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228121 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 6]
def baseStart_3228121 : Nat := 118140960795 + 3228121 * 2 ^ 59
def prefixEnd_3228121 : Nat := 4983230072969 + 3 ^ 40 * 3228121 * 2
def baseEnd_3228121 : Nat := 368350596416148821209255

theorem tailTrace_3228121 : CollatzResearch.WordTrace tailWord_3228121 prefixEnd_3228121 368350596416148821209255 := by
  unfold tailWord_3228121
  simp only [CollatzResearch.WordTrace]
  refine ⟨117739245538076411019148217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78492830358717607346098811 117739245538076411019148217)
  ·
    refine ⟨88304434153557308264361163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117739245538076411019148217 88304434153557308264361163)
    ·
      refine ⟨132456651230335962396541745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88304434153557308264361163 132456651230335962396541745)
      ·
        refine ⟨99342488422751971797406309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132456651230335962396541745 99342488422751971797406309)
        ·
          refine ⟨18626716579265994712013683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99342488422751971797406309 18626716579265994712013683)
          ·
            refine ⟨27940074868898992068020525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626716579265994712013683 27940074868898992068020525)
            ·
              refine ⟨10477528075837122025507697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27940074868898992068020525 10477528075837122025507697)
              ·
                refine ⟨7858146056877841519130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477528075837122025507697 7858146056877841519130773)
                ·
                  refine ⟨368350596416148821209255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7858146056877841519130773 368350596416148821209255)
                  ·
                    rfl

theorem cell22_3228121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_3228121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228121 prefixEnd_3228121 := by exact prefixLift 3228121
  have htrace : WordTrace (prefixWord ++ tailWord_3228121) baseStart_3228121 baseEnd_3228121 := by
    simpa [prefixWord, tailWord_3228121, baseEnd_3228121] using wordTrace_append hprefix tailTrace_3228121
  have hstable : (prefixWord ++ tailWord_3228121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228121).length < 2 ^ (prefixWord ++ tailWord_3228121).sum := by decide
  have hdescent : baseEnd_3228121 < baseStart_3228121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228181 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3228181 : Nat := 118140960795 + 3228181 * 2 ^ 59
def prefixEnd_3228181 : Nat := 4983230072969 + 3 ^ 40 * 3228181 * 2
def baseEnd_3228181 : Nat := 1105072328474626307127581

theorem tailTrace_3228181 : CollatzResearch.WordTrace tailWord_3228181 prefixEnd_3228181 1105072328474626307127581 := by
  unfold tailWord_3228181
  simp only [CollatzResearch.WordTrace]
  refine ⟨117741433917859041266332397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78494289278572694177554931 117741433917859041266332397)
  ·
    refine ⟨44153037719197140474874649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117741433917859041266332397 44153037719197140474874649)
    ·
      refine ⟨33114778289397855356155987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44153037719197140474874649 33114778289397855356155987)
      ·
        refine ⟨49672167434096783034233981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33114778289397855356155987 49672167434096783034233981)
        ·
          refine ⟨18627062787786293637837743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49672167434096783034233981 18627062787786293637837743)
          ·
            refine ⟨27940594181679440456756615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18627062787786293637837743 27940594181679440456756615)
            ·
              refine ⟨41910891272519160685134923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27940594181679440456756615 41910891272519160685134923)
              ·
                refine ⟨62866336908778741027702385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41910891272519160685134923 62866336908778741027702385)
                ·
                  refine ⟨47149752681584055770776789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62866336908778741027702385 47149752681584055770776789)
                  ·
                    refine ⟨1105072328474626307127581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47149752681584055770776789 1105072328474626307127581)
                    ·
                      rfl

theorem cell22_3228181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3228181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228181 prefixEnd_3228181 := by exact prefixLift 3228181
  have htrace : WordTrace (prefixWord ++ tailWord_3228181) baseStart_3228181 baseEnd_3228181 := by
    simpa [prefixWord, tailWord_3228181, baseEnd_3228181] using wordTrace_append hprefix tailTrace_3228181
  have hstable : (prefixWord ++ tailWord_3228181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228181).length < 2 ^ (prefixWord ++ tailWord_3228181).sum := by decide
  have hdescent : baseEnd_3228181 < baseStart_3228181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228211 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 7]
def baseStart_3228211 : Nat := 118140960795 + 3228211 * 2 ^ 59
def prefixEnd_3228211 : Nat := 4983230072969 + 3 ^ 40 * 3228211 * 2
def baseEnd_3228211 : Nat := 368360866029238742959163

theorem tailTrace_3228211 : CollatzResearch.WordTrace tailWord_3228211 prefixEnd_3228211 368360866029238742959163 := by
  unfold tailWord_3228211
  simp only [CollatzResearch.WordTrace]
  refine ⟨117742528107750356389924487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78495018738500237593282991 117742528107750356389924487)
  ·
    refine ⟨176613792161625534584886731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117742528107750356389924487 176613792161625534584886731)
    ·
      refine ⟨264920688242438301877330097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176613792161625534584886731 264920688242438301877330097)
      ·
        refine ⟨198690516181828726407997573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264920688242438301877330097 198690516181828726407997573)
        ·
          refine ⟨37254471784092886201499545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198690516181828726407997573 37254471784092886201499545)
          ·
            refine ⟨27940853838069664651124659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37254471784092886201499545 27940853838069664651124659)
            ·
              refine ⟨41911280757104496976686989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27940853838069664651124659 41911280757104496976686989)
              ·
                refine ⟨15716730283914186366257621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41911280757104496976686989 15716730283914186366257621)
                ·
                  refine ⟨368360866029238742959163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15716730283914186366257621 368360866029238742959163)
                  ·
                    rfl

theorem cell22_3228211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_3228211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228211 prefixEnd_3228211 := by exact prefixLift 3228211
  have htrace : WordTrace (prefixWord ++ tailWord_3228211) baseStart_3228211 baseEnd_3228211 := by
    simpa [prefixWord, tailWord_3228211, baseEnd_3228211] using wordTrace_append hprefix tailTrace_3228211
  have hstable : (prefixWord ++ tailWord_3228211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228211).length < 2 ^ (prefixWord ++ tailWord_3228211).sum := by decide
  have hdescent : baseEnd_3228211 < baseStart_3228211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228288 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_3228288 : Nat := 118140960795 + 3228288 * 2 ^ 59
def prefixEnd_3228288 : Nat := 4983230072969 + 3 ^ 40 * 3228288 * 2
def baseEnd_3228288 : Nat := 1105108956761313694702253

theorem tailTrace_3228288 : CollatzResearch.WordTrace tailWord_3228288 prefixEnd_3228288 1105108956761313694702253 := by
  unfold tailWord_3228288
  simp only [CollatzResearch.WordTrace]
  refine ⟨58872668264235699270238759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78496891018980932360318345 58872668264235699270238759)
  ·
    refine ⟨88309002396353548905358139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58872668264235699270238759 88309002396353548905358139)
    ·
      refine ⟨132463503594530323358037209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88309002396353548905358139 132463503594530323358037209)
      ·
        refine ⟨99347627695897742518527907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132463503594530323358037209 99347627695897742518527907)
        ·
          refine ⟨149021441543846613777791861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99347627695897742518527907 149021441543846613777791861)
          ·
            refine ⟨13970760144735620041667987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149021441543846613777791861 13970760144735620041667987)
            ·
              refine ⟨20956140217103430062501981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13970760144735620041667987 20956140217103430062501981)
              ·
                refine ⟨7858552581413786273438243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20956140217103430062501981 7858552581413786273438243)
                ·
                  refine ⟨11787828872120679410157365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7858552581413786273438243 11787828872120679410157365)
                  ·
                    refine ⟨1105108956761313694702253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11787828872120679410157365 1105108956761313694702253)
                    ·
                      rfl

theorem cell22_3228288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_3228288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228288 prefixEnd_3228288 := by exact prefixLift 3228288
  have htrace : WordTrace (prefixWord ++ tailWord_3228288) baseStart_3228288 baseEnd_3228288 := by
    simpa [prefixWord, tailWord_3228288, baseEnd_3228288] using wordTrace_append hprefix tailTrace_3228288
  have hstable : (prefixWord ++ tailWord_3228288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228288).length < 2 ^ (prefixWord ++ tailWord_3228288).sum := by decide
  have hdescent : baseEnd_3228288 < baseStart_3228288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228358 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3228358 : Nat := 118140960795 + 3228358 * 2 ^ 59
def prefixEnd_3228358 : Nat := 4983230072969 + 3 ^ 40 * 3228358 * 2
def baseEnd_3228358 : Nat := 368377639730618948484013

theorem tailTrace_3228358 : CollatzResearch.WordTrace tailWord_3228358 prefixEnd_3228358 368377639730618948484013 := by
  unfold tailWord_3228358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679621551194306265485179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78498593092145200330350485 3679621551194306265485179)
  ·
    refine ⟨5519432326791459398227769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679621551194306265485179 5519432326791459398227769)
    ·
      refine ⟨4139574245093594548670827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5519432326791459398227769 4139574245093594548670827)
      ·
        refine ⟨6209361367640391823006241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139574245093594548670827 6209361367640391823006241)
        ·
          refine ⟨4657021025730293867254681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6209361367640391823006241 4657021025730293867254681)
          ·
            refine ⟨3492765769297720400441011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4657021025730293867254681 3492765769297720400441011)
            ·
              refine ⟨5239148653946580600661517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492765769297720400441011 5239148653946580600661517)
              ·
                refine ⟨1964680745229967725248069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5239148653946580600661517 1964680745229967725248069)
                ·
                  refine ⟨368377639730618948484013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964680745229967725248069 368377639730618948484013)
                  ·
                    rfl

theorem cell22_3228358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3228358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228358 prefixEnd_3228358 := by exact prefixLift 3228358
  have htrace : WordTrace (prefixWord ++ tailWord_3228358) baseStart_3228358 baseEnd_3228358 := by
    simpa [prefixWord, tailWord_3228358, baseEnd_3228358] using wordTrace_append hprefix tailTrace_3228358
  have hstable : (prefixWord ++ tailWord_3228358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228358).length < 2 ^ (prefixWord ++ tailWord_3228358).sum := by decide
  have hdescent : baseEnd_3228358 < baseStart_3228358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228408 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_3228408 : Nat := 118140960795 + 3228408 * 2 ^ 59
def prefixEnd_3228408 : Nat := 4983230072969 + 3 ^ 40 * 3228408 * 2
def baseEnd_3228408 : Nat := 368383345071224460567295

theorem tailTrace_3228408 : CollatzResearch.WordTrace tailWord_3228408 prefixEnd_3228408 368383345071224460567295 := by
  unfold tailWord_3228408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58874856644018329517422939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78499808858691106023230585 58874856644018329517422939)
  ·
    refine ⟨88312284966027494276134409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58874856644018329517422939 88312284966027494276134409)
    ·
      refine ⟨66234213724520620707100807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88312284966027494276134409 66234213724520620707100807)
      ·
        refine ⟨99351320586780931060651211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66234213724520620707100807 99351320586780931060651211)
        ·
          refine ⟨149026980880171396590976817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99351320586780931060651211 149026980880171396590976817)
          ·
            refine ⟨111770235660128547443232613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149026980880171396590976817 111770235660128547443232613)
            ·
              refine ⟨20956919186274102645606115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111770235660128547443232613 20956919186274102645606115)
              ·
                refine ⟨31435378779411153968409173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956919186274102645606115 31435378779411153968409173)
                ·
                  refine ⟨368383345071224460567295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31435378779411153968409173 368383345071224460567295)
                  ·
                    rfl

theorem cell22_3228408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_3228408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228408 prefixEnd_3228408 := by exact prefixLift 3228408
  have htrace : WordTrace (prefixWord ++ tailWord_3228408) baseStart_3228408 baseEnd_3228408 := by
    simpa [prefixWord, tailWord_3228408, baseEnd_3228408] using wordTrace_append hprefix tailTrace_3228408
  have hstable : (prefixWord ++ tailWord_3228408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228408).length < 2 ^ (prefixWord ++ tailWord_3228408).sum := by decide
  have hdescent : baseEnd_3228408 < baseStart_3228408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228442 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_3228442 : Nat := 118140960795 + 3228442 * 2 ^ 59
def prefixEnd_3228442 : Nat := 4983230072969 + 3 ^ 40 * 3228442 * 2
def baseEnd_3228442 : Nat := 368387224702836208783927

theorem tailTrace_3228442 : CollatzResearch.WordTrace tailWord_3228442 prefixEnd_3228442 368387224702836208783927 := by
  unfold tailWord_3228442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437738342478370710395895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78500635579942321894389053 29437738342478370710395895)
  ·
    refine ⟨44156607513717556065593843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29437738342478370710395895 44156607513717556065593843)
    ·
      refine ⟨66234911270576334098390765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44156607513717556065593843 66234911270576334098390765)
      ·
        refine ⟨24838091726466125286896537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66234911270576334098390765 24838091726466125286896537)
        ·
          refine ⟨18628568794849593965172403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24838091726466125286896537 18628568794849593965172403)
          ·
            refine ⟨27942853192274390947758605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628568794849593965172403 27942853192274390947758605)
            ·
              refine ⟨10478569947102896605409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27942853192274390947758605 10478569947102896605409477)
              ·
                refine ⟨1964731865081793113514277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10478569947102896605409477 1964731865081793113514277)
                ·
                  refine ⟨368387224702836208783927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964731865081793113514277 368387224702836208783927)
                  ·
                    rfl

theorem cell22_3228442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_3228442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228442 prefixEnd_3228442 := by exact prefixLift 3228442
  have htrace : WordTrace (prefixWord ++ tailWord_3228442) baseStart_3228442 baseEnd_3228442 := by
    simpa [prefixWord, tailWord_3228442, baseEnd_3228442] using wordTrace_append hprefix tailTrace_3228442
  have hstable : (prefixWord ++ tailWord_3228442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228442).length < 2 ^ (prefixWord ++ tailWord_3228442).sum := by decide
  have hdescent : baseEnd_3228442 < baseStart_3228442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228478 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3228478 : Nat := 118140960795 + 3228478 * 2 ^ 59
def prefixEnd_3228478 : Nat := 4983230072969 + 3 ^ 40 * 3228478 * 2
def baseEnd_3228478 : Nat := 1105173997644216532451671

theorem tailTrace_3228478 : CollatzResearch.WordTrace tailWord_3228478 prefixEnd_3228478 1105173997644216532451671 := by
  unfold tailWord_3228478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719033299722882623736761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78501510931855373993262725 14719033299722882623736761)
  ·
    refine ⟨11039274974792161967802571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14719033299722882623736761 11039274974792161967802571)
    ·
      refine ⟨16558912462188242951703857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039274974792161967802571 16558912462188242951703857)
      ·
        refine ⟨12419184346641182213777893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16558912462188242951703857 12419184346641182213777893)
        ·
          refine ⟨2328597064995221665083355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12419184346641182213777893 2328597064995221665083355)
          ·
            refine ⟨3492895597492832497625033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328597064995221665083355 3492895597492832497625033)
            ·
              refine ⟨2619671698119624373218775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492895597492832497625033 2619671698119624373218775)
              ·
                refine ⟨3929507547179436559828163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619671698119624373218775 3929507547179436559828163)
                ·
                  refine ⟨5894261320769154839742245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929507547179436559828163 5894261320769154839742245)
                  ·
                    refine ⟨1105173997644216532451671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894261320769154839742245 1105173997644216532451671)
                    ·
                      rfl

theorem cell22_3228478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3228478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228478 prefixEnd_3228478 := by exact prefixLift 3228478
  have htrace : WordTrace (prefixWord ++ tailWord_3228478) baseStart_3228478 baseEnd_3228478 := by
    simpa [prefixWord, tailWord_3228478, baseEnd_3228478] using wordTrace_append hprefix tailTrace_3228478
  have hstable : (prefixWord ++ tailWord_3228478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228478).length < 2 ^ (prefixWord ++ tailWord_3228478).sum := by decide
  have hdescent : baseEnd_3228478 < baseStart_3228478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228530 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_3228530 : Nat := 118140960795 + 3228530 * 2 ^ 59
def prefixEnd_3228530 : Nat := 4983230072969 + 3 ^ 40 * 3228530 * 2
def baseEnd_3228530 : Nat := 1105191798306905730151511

theorem tailTrace_3228530 : CollatzResearch.WordTrace tailWord_3228530 prefixEnd_3228530 1105191798306905730151511 := by
  unfold tailWord_3228530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29438540748398668467696761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78502775329063115913858029 29438540748398668467696761)
  ·
    refine ⟨22078905561299001350772571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29438540748398668467696761 22078905561299001350772571)
    ·
      refine ⟨33118358341948502026158857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22078905561299001350772571 33118358341948502026158857)
      ·
        refine ⟨24838768756461376519619143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33118358341948502026158857 24838768756461376519619143)
        ·
          refine ⟨37258153134692064779428715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24838768756461376519619143 37258153134692064779428715)
          ·
            refine ⟨55887229702038097169143073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37258153134692064779428715 55887229702038097169143073)
            ·
              refine ⟨41915422276528572876857305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55887229702038097169143073 41915422276528572876857305)
              ·
                refine ⟨31436566707396429657642979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41915422276528572876857305 31436566707396429657642979)
                ·
                  refine ⟨47154850061094644486464469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31436566707396429657642979 47154850061094644486464469)
                  ·
                    refine ⟨1105191798306905730151511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47154850061094644486464469 1105191798306905730151511)
                    ·
                      rfl

theorem cell22_3228530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3228530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228530 prefixEnd_3228530 := by exact prefixLift 3228530
  have htrace : WordTrace (prefixWord ++ tailWord_3228530) baseStart_3228530 baseEnd_3228530 := by
    simpa [prefixWord, tailWord_3228530, baseEnd_3228530] using wordTrace_append hprefix tailTrace_3228530
  have hstable : (prefixWord ++ tailWord_3228530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228530).length < 2 ^ (prefixWord ++ tailWord_3228530).sum := by decide
  have hdescent : baseEnd_3228530 < baseStart_3228530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228605 : List Nat := [1, 4, 1, 2, 14]
def baseStart_3228605 : Nat := 118140960795 + 3228605 * 2 ^ 59
def prefixEnd_3228605 : Nat := 4983230072969 + 3 ^ 40 * 3228605 * 2
def baseEnd_3228605 : Nat := 4548220050780372570067

theorem tailTrace_3228605 : CollatzResearch.WordTrace tailWord_3228605 prefixEnd_3228605 4548220050780372570067 := by
  unfold tailWord_3228605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117756898468322961679767269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78504598978881974453178179 117756898468322961679767269)
  ·
    refine ⟨22079418462810555314956363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117756898468322961679767269 22079418462810555314956363)
    ·
      refine ⟨33119127694215832972434545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22079418462810555314956363 33119127694215832972434545)
      ·
        refine ⟨24839345770661874729325909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33119127694215832972434545 24839345770661874729325909)
        ·
          refine ⟨4548220050780372570067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24839345770661874729325909 4548220050780372570067)
          ·
            rfl

theorem cell22_3228605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 14].length) (baseStart_3228605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228605 prefixEnd_3228605 := by exact prefixLift 3228605
  have htrace : WordTrace (prefixWord ++ tailWord_3228605) baseStart_3228605 baseEnd_3228605 := by
    simpa [prefixWord, tailWord_3228605, baseEnd_3228605] using wordTrace_append hprefix tailTrace_3228605
  have hstable : (prefixWord ++ tailWord_3228605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228605).length < 2 ^ (prefixWord ++ tailWord_3228605).sum := by decide
  have hdescent : baseEnd_3228605 < baseStart_3228605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228622 : List Nat := [4, 1, 1, 1, 2, 3, 3, 7]
def baseStart_3228622 : Nat := 118140960795 + 3228622 * 2 ^ 59
def prefixEnd_3228622 : Nat := 4983230072969 + 3 ^ 40 * 3228622 * 2
def baseEnd_3228622 : Nat := 122802587976338684094581

theorem tailTrace_3228622 : CollatzResearch.WordTrace tailWord_3228622 prefixEnd_3228622 122802587976338684094581 := by
  unfold tailWord_3228622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719689813657671697892015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78505012339507582388757413 14719689813657671697892015)
  ·
    refine ⟨22079534720486507546838023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14719689813657671697892015 22079534720486507546838023)
    ·
      refine ⟨33119302080729761320257035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22079534720486507546838023 33119302080729761320257035)
      ·
        refine ⟨49678953121094641980385553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33119302080729761320257035 49678953121094641980385553)
        ·
          refine ⟨37259214840820981485289165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49678953121094641980385553 37259214840820981485289165)
          ·
            refine ⟨13972205565307868056983437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37259214840820981485289165 13972205565307868056983437)
            ·
              refine ⟨5239577086990450521368789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13972205565307868056983437 5239577086990450521368789)
              ·
                refine ⟨122802587976338684094581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5239577086990450521368789 122802587976338684094581)
                ·
                  rfl

theorem cell22_3228622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_3228622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228622 prefixEnd_3228622 := by exact prefixLift 3228622
  have htrace : WordTrace (prefixWord ++ tailWord_3228622) baseStart_3228622 baseEnd_3228622 := by
    simpa [prefixWord, tailWord_3228622, baseEnd_3228622] using wordTrace_append hprefix tailTrace_3228622
  have hstable : (prefixWord ++ tailWord_3228622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228622).length < 2 ^ (prefixWord ++ tailWord_3228622).sum := by decide
  have hdescent : baseEnd_3228622 < baseStart_3228622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228626 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3228626 : Nat := 118140960795 + 3228626 * 2 ^ 59
def prefixEnd_3228626 : Nat := 4983230072969 + 3 ^ 40 * 3228626 * 2
def baseEnd_3228626 : Nat := 1105224661068793479751217

theorem tailTrace_3228626 : CollatzResearch.WordTrace tailWord_3228626 prefixEnd_3228626 1105224661068793479751217 := by
  unfold tailWord_3228626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439416100311720566570433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78505109600831254844187821 29439416100311720566570433)
  ·
    refine ⟨22079562075233790424927825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29439416100311720566570433 22079562075233790424927825)
    ·
      refine ⟨16559671556425342818695869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22079562075233790424927825 16559671556425342818695869)
      ·
        refine ⟨6209876833659503557010951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16559671556425342818695869 6209876833659503557010951)
        ·
          refine ⟨9314815250489255335516427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209876833659503557010951 9314815250489255335516427)
          ·
            refine ⟨13972222875733883003274641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314815250489255335516427 13972222875733883003274641)
            ·
              refine ⟨10479167156800412252455981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13972222875733883003274641 10479167156800412252455981)
              ·
                refine ⟨3929687683800154594670993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10479167156800412252455981 3929687683800154594670993)
                ·
                  refine ⟨2947265762850115946003245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929687683800154594670993 2947265762850115946003245)
                  ·
                    refine ⟨1105224661068793479751217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947265762850115946003245 1105224661068793479751217)
                    ·
                      rfl

theorem cell22_3228626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3228626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228626 prefixEnd_3228626 := by exact prefixLift 3228626
  have htrace : WordTrace (prefixWord ++ tailWord_3228626) baseStart_3228626 baseEnd_3228626 := by
    simpa [prefixWord, tailWord_3228626, baseEnd_3228626] using wordTrace_append hprefix tailTrace_3228626
  have hstable : (prefixWord ++ tailWord_3228626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228626).length < 2 ^ (prefixWord ++ tailWord_3228626).sum := by decide
  have hdescent : baseEnd_3228626 < baseStart_3228626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228639 : List Nat := [1, 1, 2, 3, 5, 1, 3, 6]
def baseStart_3228639 : Nat := 118140960795 + 3228639 * 2 ^ 59
def prefixEnd_3228639 : Nat := 4983230072969 + 3 ^ 40 * 3228639 * 2
def baseEnd_3228639 : Nat := 122803234581607308797353

theorem tailTrace_3228639 : CollatzResearch.WordTrace tailWord_3228639 prefixEnd_3228639 122803234581607308797353 := by
  unfold tailWord_3228639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117758138550199785486504971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78505425700133190324336647 117758138550199785486504971)
  ·
    refine ⟨176637207825299678229757457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117758138550199785486504971 176637207825299678229757457)
    ·
      refine ⟨132477905868974758672318093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176637207825299678229757457 132477905868974758672318093)
      ·
        refine ⟨49679214700865534502119285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132477905868974758672318093 49679214700865534502119285)
        ·
          refine ⟨4657426378206143859573683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49679214700865534502119285 4657426378206143859573683)
          ·
            refine ⟨6986139567309215789360525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657426378206143859573683 6986139567309215789360525)
            ·
              refine ⟨2619802337740955921010197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6986139567309215789360525 2619802337740955921010197)
              ·
                refine ⟨122803234581607308797353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2619802337740955921010197 122803234581607308797353)
                ·
                  rfl

theorem cell22_3228639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 6].length) (baseStart_3228639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228639 prefixEnd_3228639 := by exact prefixLift 3228639
  have htrace : WordTrace (prefixWord ++ tailWord_3228639) baseStart_3228639 baseEnd_3228639 := by
    simpa [prefixWord, tailWord_3228639, baseEnd_3228639] using wordTrace_append hprefix tailTrace_3228639
  have hstable : (prefixWord ++ tailWord_3228639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228639).length < 2 ^ (prefixWord ++ tailWord_3228639).sum := by decide
  have hdescent : baseEnd_3228639 < baseStart_3228639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228690 : List Nat := [3, 2, 5, 1, 1, 2, 2, 6]
def baseStart_3228690 : Nat := 118140960795 + 3228690 * 2 ^ 59
def prefixEnd_3228690 : Nat := 4983230072969 + 3 ^ 40 * 3228690 * 2
def baseEnd_3228690 : Nat := 122805174397413182905669

theorem tailTrace_3228690 : CollatzResearch.WordTrace tailWord_3228690 prefixEnd_3228690 122805174397413182905669 := by
  unfold tailWord_3228690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439999668253755299152881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78506665782010014131074349 29439999668253755299152881)
  ·
    refine ⟨22079999751190316474364661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29439999668253755299152881 22079999751190316474364661)
    ·
      refine ⟨2069999976674092169471687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22079999751190316474364661 2069999976674092169471687)
      ·
        refine ⟨3104999965011138254207531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069999976674092169471687 3104999965011138254207531)
        ·
          refine ⟨4657499947516707381311297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104999965011138254207531 4657499947516707381311297)
          ·
            refine ⟨3493124960637530535983473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4657499947516707381311297 3493124960637530535983473)
            ·
              refine ⟨2619843720478147901987605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493124960637530535983473 2619843720478147901987605)
              ·
                refine ⟨122805174397413182905669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2619843720478147901987605 122805174397413182905669)
                ·
                  rfl

theorem cell22_3228690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_3228690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228690 prefixEnd_3228690 := by exact prefixLift 3228690
  have htrace : WordTrace (prefixWord ++ tailWord_3228690) baseStart_3228690 baseEnd_3228690 := by
    simpa [prefixWord, tailWord_3228690, baseEnd_3228690] using wordTrace_append hprefix tailTrace_3228690
  have hstable : (prefixWord ++ tailWord_3228690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228690).length < 2 ^ (prefixWord ++ tailWord_3228690).sum := by decide
  have hdescent : baseEnd_3228690 < baseStart_3228690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228697 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_3228697 : Nat := 118140960795 + 3228697 * 2 ^ 59
def prefixEnd_3228697 : Nat := 4983230072969 + 3 ^ 40 * 3228697 * 2
def baseEnd_3228697 : Nat := 1105248965819772961225999

theorem tailTrace_3228697 : CollatzResearch.WordTrace tailWord_3228697 prefixEnd_3228697 1105248965819772961225999 := by
  unfold tailWord_3228697
  simp only [CollatzResearch.WordTrace]
  refine ⟨117760253983989661392116345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78506835989326440928077563 117760253983989661392116345)
  ·
    refine ⟨88320190487992246044087259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117760253983989661392116345 88320190487992246044087259)
    ·
      refine ⟨132480285731988369066130889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88320190487992246044087259 132480285731988369066130889)
      ·
        refine ⟨99360214298991276799598167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132480285731988369066130889 99360214298991276799598167)
        ·
          refine ⟨149040321448486915199397251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99360214298991276799598167 149040321448486915199397251)
          ·
            refine ⟨223560482172730372799095877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149040321448486915199397251 223560482172730372799095877)
            ·
              refine ⟨41917590407386944899830477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223560482172730372799095877 41917590407386944899830477)
              ·
                refine ⟨15719096402770104337436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41917590407386944899830477 15719096402770104337436429)
                ·
                  refine ⟨5894661151038789126538661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15719096402770104337436429 5894661151038789126538661)
                  ·
                    refine ⟨1105248965819772961225999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894661151038789126538661 1105248965819772961225999)
                    ·
                      rfl

theorem cell22_3228697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_3228697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228697 prefixEnd_3228697 := by exact prefixLift 3228697
  have htrace : WordTrace (prefixWord ++ tailWord_3228697) baseStart_3228697 baseEnd_3228697 := by
    simpa [prefixWord, tailWord_3228697, baseEnd_3228697] using wordTrace_append hprefix tailTrace_3228697
  have hstable : (prefixWord ++ tailWord_3228697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228697).length < 2 ^ (prefixWord ++ tailWord_3228697).sum := by decide
  have hdescent : baseEnd_3228697 < baseStart_3228697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228729 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 6]
def baseStart_3228729 : Nat := 118140960795 + 3228729 * 2 ^ 59
def prefixEnd_3228729 : Nat := 4983230072969 + 3 ^ 40 * 3228729 * 2
def baseEnd_3228729 : Nat := 368419973357911848141967

theorem tailTrace_3228729 : CollatzResearch.WordTrace tailWord_3228729 prefixEnd_3228729 368419973357911848141967 := by
  unfold tailWord_3228729
  simp only [CollatzResearch.WordTrace]
  refine ⟨117761421119873730857281241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78507614079915820571520827 117761421119873730857281241)
  ·
    refine ⟨88321065839905298142960931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117761421119873730857281241 88321065839905298142960931)
    ·
      refine ⟨132481598759857947214441397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88321065839905298142960931 132481598759857947214441397)
      ·
        refine ⟨12420149883736682551353881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132481598759857947214441397 12420149883736682551353881)
        ·
          refine ⟨9315112412802511913515411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12420149883736682551353881 9315112412802511913515411)
          ·
            refine ⟨13972668619203767870273117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315112412802511913515411 13972668619203767870273117)
            ·
              refine ⟨5239750732201412951352419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13972668619203767870273117 5239750732201412951352419)
              ·
                refine ⟨7859626098302119427028629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239750732201412951352419 7859626098302119427028629)
                ·
                  refine ⟨368419973357911848141967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7859626098302119427028629 368419973357911848141967)
                  ·
                    rfl

theorem cell22_3228729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_3228729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228729 prefixEnd_3228729 := by exact prefixLift 3228729
  have htrace : WordTrace (prefixWord ++ tailWord_3228729) baseStart_3228729 baseEnd_3228729 := by
    simpa [prefixWord, tailWord_3228729, baseEnd_3228729] using wordTrace_append hprefix tailTrace_3228729
  have hstable : (prefixWord ++ tailWord_3228729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228729).length < 2 ^ (prefixWord ++ tailWord_3228729).sum := by decide
  have hdescent : baseEnd_3228729 < baseStart_3228729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228757 : List Nat := [1, 3, 2, 2, 1, 2, 1, 10]
def baseStart_3228757 : Nat := 118140960795 + 3228757 * 2 ^ 59
def prefixEnd_3228757 : Nat := 4983230072969 + 3 ^ 40 * 3228757 * 2
def baseEnd_3228757 : Nat := 122807722782883644969535

theorem tailTrace_3228757 : CollatzResearch.WordTrace tailWord_3228757 prefixEnd_3228757 122807722782883644969535 := by
  unfold tailWord_3228757
  simp only [CollatzResearch.WordTrace]
  refine ⟨117762442363772291639300525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78508294909181527759533683 117762442363772291639300525)
  ·
    refine ⟨44160915886414609364737697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117762442363772291639300525 44160915886414609364737697)
    ·
      refine ⟨33120686914810957023553273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44160915886414609364737697 33120686914810957023553273)
      ·
        refine ⟨24840515186108217767664955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33120686914810957023553273 24840515186108217767664955)
        ·
          refine ⟨37260772779162326651497433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24840515186108217767664955 37260772779162326651497433)
          ·
            refine ⟨27945579584371744988623075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37260772779162326651497433 27945579584371744988623075)
            ·
              refine ⟨41918369376557617482934613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27945579584371744988623075 41918369376557617482934613)
              ·
                refine ⟨122807722782883644969535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41918369376557617482934613 122807722782883644969535)
                ·
                  rfl

theorem cell22_3228757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 10].length) (baseStart_3228757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228757 prefixEnd_3228757 := by exact prefixLift 3228757
  have htrace : WordTrace (prefixWord ++ tailWord_3228757) baseStart_3228757 baseEnd_3228757 := by
    simpa [prefixWord, tailWord_3228757, baseEnd_3228757] using wordTrace_append hprefix tailTrace_3228757
  have hstable : (prefixWord ++ tailWord_3228757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228757).length < 2 ^ (prefixWord ++ tailWord_3228757).sum := by decide
  have hdescent : baseEnd_3228757 < baseStart_3228757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228765 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3228765 : Nat := 118140960795 + 3228765 * 2 ^ 59
def prefixEnd_3228765 : Nat := 4983230072969 + 3 ^ 40 * 3228765 * 2
def baseEnd_3228765 : Nat := 1105272243609443450525791

theorem tailTrace_3228765 : CollatzResearch.WordTrace tailWord_3228765 prefixEnd_3228765 1105272243609443450525791 := by
  unfold tailWord_3228765
  simp only [CollatzResearch.WordTrace]
  refine ⟨117762734147743309005591749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78508489431828872670394499 117762734147743309005591749)
  ·
    refine ⟨22080512652701870438548453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117762734147743309005591749 22080512652701870438548453)
    ·
      refine ⟨4140096122381600707227835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22080512652701870438548453 4140096122381600707227835)
      ·
        refine ⟨6210144183572401060841753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140096122381600707227835 6210144183572401060841753)
        ·
          refine ⟨4657608137679300795631315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6210144183572401060841753 4657608137679300795631315)
          ·
            refine ⟨6986412206518951193446973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657608137679300795631315 6986412206518951193446973)
            ·
              refine ⟨2619904577444606697542615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6986412206518951193446973 2619904577444606697542615)
              ·
                refine ⟨3929856866166910046313923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619904577444606697542615 3929856866166910046313923)
                ·
                  refine ⟨5894785299250365069470885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929856866166910046313923 5894785299250365069470885)
                  ·
                    refine ⟨1105272243609443450525791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894785299250365069470885 1105272243609443450525791)
                    ·
                      rfl

theorem cell22_3228765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3228765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228765 prefixEnd_3228765 := by exact prefixLift 3228765
  have htrace : WordTrace (prefixWord ++ tailWord_3228765) baseStart_3228765 baseEnd_3228765 := by
    simpa [prefixWord, tailWord_3228765, baseEnd_3228765] using wordTrace_append hprefix tailTrace_3228765
  have hstable : (prefixWord ++ tailWord_3228765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228765).length < 2 ^ (prefixWord ++ tailWord_3228765).sum := by decide
  have hdescent : baseEnd_3228765 < baseStart_3228765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228778 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_3228778 : Nat := 118140960795 + 3228778 * 2 ^ 59
def prefixEnd_3228778 : Nat := 4983230072969 + 3 ^ 40 * 3228778 * 2
def baseEnd_3228778 : Nat := 1105276693775115749950751

theorem tailTrace_3228778 : CollatzResearch.WordTrace tailWord_3228778 prefixEnd_3228778 1105276693775115749950751 := by
  unfold tailWord_3228778
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440802074174053056453747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78508805531130808150543325 29440802074174053056453747)
  ·
    refine ⟨44161203111261079584680621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29440802074174053056453747 44161203111261079584680621)
    ·
      refine ⟨16560451166722904844255233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44161203111261079584680621 16560451166722904844255233)
      ·
        refine ⟨12420338375042178633191425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16560451166722904844255233 12420338375042178633191425)
        ·
          refine ⟨9315253781281633974893569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12420338375042178633191425 9315253781281633974893569)
          ·
            refine ⟨6986440335961225481170177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315253781281633974893569 6986440335961225481170177)
            ·
              refine ⟨5239830251970919110877633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986440335961225481170177 5239830251970919110877633)
              ·
                refine ⟨3929872688978189333158225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239830251970919110877633 3929872688978189333158225)
                ·
                  refine ⟨2947404516733641999868669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929872688978189333158225 2947404516733641999868669)
                  ·
                    refine ⟨1105276693775115749950751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947404516733641999868669 1105276693775115749950751)
                    ·
                      rfl

theorem cell22_3228778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_3228778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228778 prefixEnd_3228778 := by exact prefixLift 3228778
  have htrace : WordTrace (prefixWord ++ tailWord_3228778) baseStart_3228778 baseEnd_3228778 := by
    simpa [prefixWord, tailWord_3228778, baseEnd_3228778] using wordTrace_append hprefix tailTrace_3228778
  have hstable : (prefixWord ++ tailWord_3228778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228778).length < 2 ^ (prefixWord ++ tailWord_3228778).sum := by decide
  have hdescent : baseEnd_3228778 < baseStart_3228778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228823 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 1, 3]
def baseStart_3228823 : Nat := 118140960795 + 3228823 * 2 ^ 59
def prefixEnd_3228823 : Nat := 4983230072969 + 3 ^ 40 * 3228823 * 2
def baseEnd_3228823 : Nat := 1105292098194750632575613

theorem tailTrace_3228823 : CollatzResearch.WordTrace tailWord_3228823 prefixEnd_3228823 1105292098194750632575613 := by
  unfold tailWord_3228823
  simp only [CollatzResearch.WordTrace]
  refine ⟨117764849581533184911203123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78509899721022123274135415 117764849581533184911203123)
  ·
    refine ⟨176647274372299777366804685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117764849581533184911203123 176647274372299777366804685)
    ·
      refine ⟨66242727889612416512551757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176647274372299777366804685 66242727889612416512551757)
      ·
        refine ⟨24841022958604656192206909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66242727889612416512551757 24841022958604656192206909)
        ·
          refine ⟨9315383609476746072077591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24841022958604656192206909 9315383609476746072077591)
          ·
            refine ⟨13973075414215119108116387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315383609476746072077591 13973075414215119108116387)
            ·
              refine ⟨20959613121322678662174581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973075414215119108116387 20959613121322678662174581)
              ·
                refine ⟨1964963730124001124578867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20959613121322678662174581 1964963730124001124578867)
                ·
                  refine ⟨2947445595186001686868301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964963730124001124578867 2947445595186001686868301)
                  ·
                    refine ⟨1105292098194750632575613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947445595186001686868301 1105292098194750632575613)
                    ·
                      rfl

theorem cell22_3228823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_3228823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228823 prefixEnd_3228823 := by exact prefixLift 3228823
  have htrace : WordTrace (prefixWord ++ tailWord_3228823) baseStart_3228823 baseEnd_3228823 := by
    simpa [prefixWord, tailWord_3228823, baseEnd_3228823] using wordTrace_append hprefix tailTrace_3228823
  have hstable : (prefixWord ++ tailWord_3228823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228823).length < 2 ^ (prefixWord ++ tailWord_3228823).sum := by decide
  have hdescent : baseEnd_3228823 < baseStart_3228823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
