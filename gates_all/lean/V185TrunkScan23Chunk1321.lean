import V185TrunkScan23Chunk1320

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7824664 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7824664 : Nat := 118140960795 + 7824664 * 2 ^ 59
def prefixEnd_7824664 : Nat := 4983230072969 + 3 ^ 40 * 7824664 * 2
def baseEnd_7824664 : Nat := 4017813591932079199815031

theorem tailTrace_7824664 : CollatzResearch.WordTrace tailWord_7824664 prefixEnd_7824664 4017813591932079199815031 := by
  unfold tailWord_7824664
  simp only [CollatzResearch.WordTrace]
  refine ⟨142694470862293074532176523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190259294483057432709568697 142694470862293074532176523)
  ·
    refine ⟨214041706293439611798264785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142694470862293074532176523 214041706293439611798264785)
    ·
      refine ⟨160531279720079708848698589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214041706293439611798264785 160531279720079708848698589)
      ·
        refine ⟨60199229895029890818261971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160531279720079708848698589 60199229895029890818261971)
        ·
          refine ⟨90298844842544836227392957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60199229895029890818261971 90298844842544836227392957)
          ·
            refine ⟨33862066815954313585272359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90298844842544836227392957 33862066815954313585272359)
            ·
              refine ⟨50793100223931470377908539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33862066815954313585272359 50793100223931470377908539)
              ·
                refine ⟨76189650335897205566862809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50793100223931470377908539 76189650335897205566862809)
                ·
                  refine ⟨57142237751922904175147107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76189650335897205566862809 57142237751922904175147107)
                  ·
                    refine ⟨85713356627884356262720661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57142237751922904175147107 85713356627884356262720661)
                    ·
                      refine ⟨4017813591932079199815031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85713356627884356262720661 4017813591932079199815031)
                      ·
                        rfl

theorem cell23_7824664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7824664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824664 prefixEnd_7824664 := by exact prefixLift 7824664
  have htrace : WordTrace (prefixWord ++ tailWord_7824664) baseStart_7824664 baseEnd_7824664 := by
    simpa [prefixWord, tailWord_7824664, baseEnd_7824664] using wordTrace_append hprefix tailTrace_7824664
  have hstable : (prefixWord ++ tailWord_7824664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824664).length < 2 ^ (prefixWord ++ tailWord_7824664).sum := by decide
  have hdescent : baseEnd_7824664 < baseStart_7824664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824685 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7824685 : Nat := 118140960795 + 7824685 * 2 ^ 59
def prefixEnd_7824685 : Nat := 4983230072969 + 3 ^ 40 * 7824685 * 2
def baseEnd_7824685 : Nat := 4017824375025823617652435

theorem tailTrace_7824685 : CollatzResearch.WordTrace tailWord_7824685 prefixEnd_7824685 4017824375025823617652435 := by
  unfold tailWord_7824685
  simp only [CollatzResearch.WordTrace]
  refine ⟨285389707657510069650867509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190259805105006713100578339 285389707657510069650867509)
  ·
    refine ⟨26755285092891569029768829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285389707657510069650867509 26755285092891569029768829)
    ·
      refine ⟨10033231909834338386163311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26755285092891569029768829 10033231909834338386163311)
      ·
        refine ⟨15049847864751507579244967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033231909834338386163311 15049847864751507579244967)
        ·
          refine ⟨22574771797127261368867451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049847864751507579244967 22574771797127261368867451)
          ·
            refine ⟨33862157695690892053301177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574771797127261368867451 33862157695690892053301177)
            ·
              refine ⟨25396618271768169039975883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33862157695690892053301177 25396618271768169039975883)
              ·
                refine ⟨38094927407652253559963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25396618271768169039975883 38094927407652253559963825)
                ·
                  refine ⟨28571195555739190169972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38094927407652253559963825 28571195555739190169972869)
                  ·
                    refine ⟨5357099166701098156869913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28571195555739190169972869 5357099166701098156869913)
                    ·
                      refine ⟨4017824375025823617652435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357099166701098156869913 4017824375025823617652435)
                      ·
                        rfl

theorem cell23_7824685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7824685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824685 prefixEnd_7824685 := by exact prefixLift 7824685
  have htrace : WordTrace (prefixWord ++ tailWord_7824685) baseStart_7824685 baseEnd_7824685 := by
    simpa [prefixWord, tailWord_7824685, baseEnd_7824685] using wordTrace_append hprefix tailTrace_7824685
  have hstable : (prefixWord ++ tailWord_7824685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824685).length < 2 ^ (prefixWord ++ tailWord_7824685).sum := by decide
  have hdescent : baseEnd_7824685 < baseStart_7824685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824721 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_7824721 : Nat := 118140960795 + 7824721 * 2 ^ 59
def prefixEnd_7824721 : Nat := 4983230072969 + 3 ^ 40 * 7824721 * 2
def baseEnd_7824721 : Nat := 1339280953443128492267423

theorem tailTrace_7824721 : CollatzResearch.WordTrace tailWord_7824721 prefixEnd_7824721 1339280953443128492267423 := by
  unfold tailWord_7824721
  simp only [CollatzResearch.WordTrace]
  refine ⟨285391020685379647799178017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190260680456919765199452011 285391020685379647799178017)
  ·
    refine ⟨214043265514034735849383513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285391020685379647799178017 214043265514034735849383513)
    ·
      refine ⟨160532449135526051887037635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214043265514034735849383513 160532449135526051887037635)
      ·
        refine ⟨240798673703289077830556453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160532449135526051887037635 240798673703289077830556453)
        ·
          refine ⟨45149751319366702093229335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240798673703289077830556453 45149751319366702093229335)
          ·
            refine ⟨67724626979050053139844003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45149751319366702093229335 67724626979050053139844003)
            ·
              refine ⟨101586940468575079709766005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67724626979050053139844003 101586940468575079709766005)
              ·
                refine ⟨9523775668928913722790563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101586940468575079709766005 9523775668928913722790563)
                ·
                  refine ⟨14285663503393370584185845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523775668928913722790563 14285663503393370584185845)
                  ·
                    refine ⟨1339280953443128492267423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14285663503393370584185845 1339280953443128492267423)
                    ·
                      rfl

theorem cell23_7824721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_7824721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824721 prefixEnd_7824721 := by exact prefixLift 7824721
  have htrace : WordTrace (prefixWord ++ tailWord_7824721) baseStart_7824721 baseEnd_7824721 := by
    simpa [prefixWord, tailWord_7824721, baseEnd_7824721] using wordTrace_append hprefix tailTrace_7824721
  have hstable : (prefixWord ++ tailWord_7824721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824721).length < 2 ^ (prefixWord ++ tailWord_7824721).sum := by decide
  have hdescent : baseEnd_7824721 < baseStart_7824721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824728 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_7824728 : Nat := 118140960795 + 7824728 * 2 ^ 59
def prefixEnd_7824728 : Nat := 4983230072969 + 3 ^ 40 * 7824728 * 2
def baseEnd_7824728 : Nat := 4017846454693966949414737

theorem tailTrace_7824728 : CollatzResearch.WordTrace tailWord_7824728 prefixEnd_7824728 4017846454693966949414737 := by
  unfold tailWord_7824728
  simp only [CollatzResearch.WordTrace]
  refine ⟨142695637998177143997341419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190260850664236191996455225 142695637998177143997341419)
  ·
    refine ⟨214043456997265715996012129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142695637998177143997341419 214043456997265715996012129)
    ·
      refine ⟨160532592747949286997009097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214043456997265715996012129 160532592747949286997009097)
      ·
        refine ⟨120399444560961965247756823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160532592747949286997009097 120399444560961965247756823)
        ·
          refine ⟨180599166841442947871635235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120399444560961965247756823 180599166841442947871635235)
          ·
            refine ⟨270898750262164421807452853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180599166841442947871635235 270898750262164421807452853)
            ·
              refine ⟨25396757837077914544448705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270898750262164421807452853 25396757837077914544448705)
              ·
                refine ⟨19047568377808435908336529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25396757837077914544448705 19047568377808435908336529)
                ·
                  refine ⟨14285676283356326931252397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19047568377808435908336529 14285676283356326931252397)
                  ·
                    refine ⟨5357128606258622599219649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14285676283356326931252397 5357128606258622599219649)
                    ·
                      refine ⟨4017846454693966949414737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357128606258622599219649 4017846454693966949414737)
                      ·
                        rfl

theorem cell23_7824728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_7824728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824728 prefixEnd_7824728 := by exact prefixLift 7824728
  have htrace : WordTrace (prefixWord ++ tailWord_7824728) baseStart_7824728 baseEnd_7824728 := by
    simpa [prefixWord, tailWord_7824728, baseEnd_7824728] using wordTrace_append hprefix tailTrace_7824728
  have hstable : (prefixWord ++ tailWord_7824728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824728).length < 2 ^ (prefixWord ++ tailWord_7824728).sum := by decide
  have hdescent : baseEnd_7824728 < baseStart_7824728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824741 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7824741 : Nat := 118140960795 + 7824741 * 2 ^ 59
def prefixEnd_7824741 : Nat := 4983230072969 + 3 ^ 40 * 7824741 * 2
def baseEnd_7824741 : Nat := 4017853129942475398552177

theorem tailTrace_7824741 : CollatzResearch.WordTrace tailWord_7824741 prefixEnd_7824741 4017853129942475398552177 := by
  unfold tailWord_7824741
  simp only [CollatzResearch.WordTrace]
  refine ⟨285391750145307191214906077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190261166763538127476604051 285391750145307191214906077)
  ·
    refine ⟨107021906304490196705589779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285391750145307191214906077 107021906304490196705589779)
    ·
      refine ⟨160532859456735295058384669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107021906304490196705589779 160532859456735295058384669)
      ·
        refine ⟨60199822296275735646894251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160532859456735295058384669 60199822296275735646894251)
        ·
          refine ⟨90299733444413603470341377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60199822296275735646894251 90299733444413603470341377)
          ·
            refine ⟨67724800083310202602756033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90299733444413603470341377 67724800083310202602756033)
            ·
              refine ⟨50793600062482651952067025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67724800083310202602756033 50793600062482651952067025)
              ·
                refine ⟨38095200046861988964050269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50793600062482651952067025 38095200046861988964050269)
                ·
                  refine ⟨14285700017573245861518851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38095200046861988964050269 14285700017573245861518851)
                  ·
                    refine ⟨21428550026359868792278277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14285700017573245861518851 21428550026359868792278277)
                    ·
                      refine ⟨4017853129942475398552177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21428550026359868792278277 4017853129942475398552177)
                      ·
                        rfl

theorem cell23_7824741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7824741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824741 prefixEnd_7824741 := by exact prefixLift 7824741
  have htrace : WordTrace (prefixWord ++ tailWord_7824741) baseStart_7824741 baseEnd_7824741 := by
    simpa [prefixWord, tailWord_7824741, baseEnd_7824741] using wordTrace_append hprefix tailTrace_7824741
  have hstable : (prefixWord ++ tailWord_7824741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824741).length < 2 ^ (prefixWord ++ tailWord_7824741).sum := by decide
  have hdescent : baseEnd_7824741 < baseStart_7824741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824764 : List Nat := [2, 2, 2, 1, 1, 1, 3, 11]
def baseStart_7824764 : Nat := 118140960795 + 7824764 * 2 ^ 59
def prefixEnd_7824764 : Nat := 4983230072969 + 3 ^ 40 * 7824764 * 2
def baseEnd_7824764 : Nat := 148809812592501066983873

theorem tailTrace_7824764 : CollatzResearch.WordTrace tailWord_7824764 prefixEnd_7824764 148809812592501066983873 := by
  unfold tailWord_7824764
  simp only [CollatzResearch.WordTrace]
  refine ⟨142696294512111933071496673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190261726016149244095328897 142696294512111933071496673)
  ·
    refine ⟨107022220884083949803622505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142696294512111933071496673 107022220884083949803622505)
    ·
      refine ⟨80266665663062962352716879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107022220884083949803622505 80266665663062962352716879)
      ·
        refine ⟨120399998494594443529075319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80266665663062962352716879 120399998494594443529075319)
        ·
          refine ⟨180599997741891665293612979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120399998494594443529075319 180599997741891665293612979)
          ·
            refine ⟨270899996612837497940419469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180599997741891665293612979 270899996612837497940419469)
            ·
              refine ⟨101587498729814061727657301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270899996612837497940419469 101587498729814061727657301)
              ·
                refine ⟨148809812592501066983873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101587498729814061727657301 148809812592501066983873)
                ·
                  rfl

theorem cell23_7824764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 11].length) (baseStart_7824764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824764 prefixEnd_7824764 := by exact prefixLift 7824764
  have htrace : WordTrace (prefixWord ++ tailWord_7824764) baseStart_7824764 baseEnd_7824764 := by
    simpa [prefixWord, tailWord_7824764, baseEnd_7824764] using wordTrace_append hprefix tailTrace_7824764
  have hstable : (prefixWord ++ tailWord_7824764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824764).length < 2 ^ (prefixWord ++ tailWord_7824764).sum := by decide
  have hdescent : baseEnd_7824764 < baseStart_7824764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824771 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_7824771 : Nat := 118140960795 + 7824771 * 2 ^ 59
def prefixEnd_7824771 : Nat := 4983230072969 + 3 ^ 40 * 7824771 * 2
def baseEnd_7824771 : Nat := 4017868534362110281177039

theorem tailTrace_7824771 : CollatzResearch.WordTrace tailWord_7824771 prefixEnd_7824771 4017868534362110281177039 := by
  unfold tailWord_7824771
  simp only [CollatzResearch.WordTrace]
  refine ⟨285392844335198506338498167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190261896223465670892332111 285392844335198506338498167)
  ·
    refine ⟨428089266502797759507747251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285392844335198506338498167 428089266502797759507747251)
    ·
      refine ⟨642133899754196639261620877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428089266502797759507747251 642133899754196639261620877)
      ·
        refine ⟨240800212407823739723107829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642133899754196639261620877 240800212407823739723107829)
        ·
          refine ⟨22575019913233475599041359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240800212407823739723107829 22575019913233475599041359)
          ·
            refine ⟨33862529869850213398562039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22575019913233475599041359 33862529869850213398562039)
            ·
              refine ⟨50793794804775320097843059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33862529869850213398562039 50793794804775320097843059)
              ·
                refine ⟨76190692207162980146764589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50793794804775320097843059 76190692207162980146764589)
                ·
                  refine ⟨28571509577686117555036721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76190692207162980146764589 28571509577686117555036721)
                  ·
                    refine ⟨21428632183264588166277541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28571509577686117555036721 21428632183264588166277541)
                    ·
                      refine ⟨4017868534362110281177039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21428632183264588166277541 4017868534362110281177039)
                      ·
                        rfl

theorem cell23_7824771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_7824771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824771 prefixEnd_7824771 := by exact prefixLift 7824771
  have htrace : WordTrace (prefixWord ++ tailWord_7824771) baseStart_7824771 baseEnd_7824771 := by
    simpa [prefixWord, tailWord_7824771, baseEnd_7824771] using wordTrace_append hprefix tailTrace_7824771
  have hstable : (prefixWord ++ tailWord_7824771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824771).length < 2 ^ (prefixWord ++ tailWord_7824771).sum := by decide
  have hdescent : baseEnd_7824771 < baseStart_7824771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824775 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_7824775 : Nat := 118140960795 + 7824775 * 2 ^ 59
def prefixEnd_7824775 : Nat := 4983230072969 + 3 ^ 40 * 7824775 * 2
def baseEnd_7824775 : Nat := 4017870588284728265527021

theorem tailTrace_7824775 : CollatzResearch.WordTrace tailWord_7824775 prefixEnd_7824775 4017870588284728265527021 := by
  unfold tailWord_7824775
  simp only [CollatzResearch.WordTrace]
  refine ⟨285392990227184015021643779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190261993484789343347762519 285392990227184015021643779)
  ·
    refine ⟨428089485340776022532465669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285392990227184015021643779 428089485340776022532465669)
    ·
      refine ⟨80266778501395504224837313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428089485340776022532465669 80266778501395504224837313)
      ·
        refine ⟨60200083876046628168627985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80266778501395504224837313 60200083876046628168627985)
        ·
          refine ⟨45150062907034971126470989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60200083876046628168627985 45150062907034971126470989)
          ·
            refine ⟨16931273590138114172426621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45150062907034971126470989 16931273590138114172426621)
            ·
              refine ⟨6349227596301792814659983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16931273590138114172426621 6349227596301792814659983)
              ·
                refine ⟨9523841394452689221989975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349227596301792814659983 9523841394452689221989975)
                ·
                  refine ⟨14285762091679033832984963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523841394452689221989975 14285762091679033832984963)
                  ·
                    refine ⟨21428643137518550749477445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14285762091679033832984963 21428643137518550749477445)
                    ·
                      refine ⟨4017870588284728265527021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21428643137518550749477445 4017870588284728265527021)
                      ·
                        rfl

theorem cell23_7824775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_7824775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824775 prefixEnd_7824775 := by exact prefixLift 7824775
  have htrace : WordTrace (prefixWord ++ tailWord_7824775) baseStart_7824775 baseEnd_7824775 := by
    simpa [prefixWord, tailWord_7824775, baseEnd_7824775] using wordTrace_append hprefix tailTrace_7824775
  have hstable : (prefixWord ++ tailWord_7824775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824775).length < 2 ^ (prefixWord ++ tailWord_7824775).sum := by decide
  have hdescent : baseEnd_7824775 < baseStart_7824775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824791 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7824791 : Nat := 118140960795 + 7824791 * 2 ^ 59
def prefixEnd_7824791 : Nat := 4983230072969 + 3 ^ 40 * 7824791 * 2
def baseEnd_7824791 : Nat := 4017878803975200202926947

theorem tailTrace_7824791 : CollatzResearch.WordTrace tailWord_7824791 prefixEnd_7824791 4017878803975200202926947 := by
  unfold tailWord_7824791
  simp only [CollatzResearch.WordTrace]
  refine ⟨285393573795126049754226227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190262382530084033169484151 285393573795126049754226227)
  ·
    refine ⟨428090360692689074631339341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285393573795126049754226227 428090360692689074631339341)
    ·
      refine ⟨160533885259758402986752253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428090360692689074631339341 160533885259758402986752253)
      ·
        refine ⟨60200206972409401120032095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160533885259758402986752253 60200206972409401120032095)
        ·
          refine ⟨90300310458614101680048143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60200206972409401120032095 90300310458614101680048143)
          ·
            refine ⟨135450465687921152520072215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90300310458614101680048143 135450465687921152520072215)
            ·
              refine ⟨203175698531881728780108323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135450465687921152520072215 203175698531881728780108323)
              ·
                refine ⟨304763547797822593170162485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203175698531881728780108323 304763547797822593170162485)
                ·
                  refine ⟨28571582606045868109702733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304763547797822593170162485 28571582606045868109702733)
                  ·
                    refine ⟨10714343477267200541138525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28571582606045868109702733 10714343477267200541138525)
                    ·
                      refine ⟨4017878803975200202926947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10714343477267200541138525 4017878803975200202926947)
                      ·
                        rfl

theorem cell23_7824791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7824791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824791 prefixEnd_7824791 := by exact prefixLift 7824791
  have htrace : WordTrace (prefixWord ++ tailWord_7824791) baseStart_7824791 baseEnd_7824791 := by
    simpa [prefixWord, tailWord_7824791, baseEnd_7824791] using wordTrace_append hprefix tailTrace_7824791
  have hstable : (prefixWord ++ tailWord_7824791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824791).length < 2 ^ (prefixWord ++ tailWord_7824791).sum := by decide
  have hdescent : baseEnd_7824791 < baseStart_7824791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824842 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_7824842 : Nat := 118140960795 + 7824842 * 2 ^ 59
def prefixEnd_7824842 : Nat := 4983230072969 + 3 ^ 40 * 7824842 * 2
def baseEnd_7824842 : Nat := 4017904991488579503389213

theorem tailTrace_7824842 : CollatzResearch.WordTrace tailWord_7824842 prefixEnd_7824842 4017904991488579503389213 := by
  unfold tailWord_7824842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71348858479485321366083195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190263622611960856976221853 71348858479485321366083195)
  ·
    refine ⟨107023287719227982049124793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71348858479485321366083195 107023287719227982049124793)
    ·
      refine ⟨80267465789420986536843595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107023287719227982049124793 80267465789420986536843595)
      ·
        refine ⟨120401198684131479805265393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80267465789420986536843595 120401198684131479805265393)
        ·
          refine ⟨90300899013098609853949045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120401198684131479805265393 90300899013098609853949045)
          ·
            refine ⟨8465709282477994673807723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90300899013098609853949045 8465709282477994673807723)
            ·
              refine ⟨12698563923716992010711585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465709282477994673807723 12698563923716992010711585)
              ·
                refine ⟨9523922942787744008033689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12698563923716992010711585 9523922942787744008033689)
                ·
                  refine ⟨7142942207090808006025267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9523922942787744008033689 7142942207090808006025267)
                  ·
                    refine ⟨10714413310636212009037901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7142942207090808006025267 10714413310636212009037901)
                    ·
                      refine ⟨4017904991488579503389213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10714413310636212009037901 4017904991488579503389213)
                      ·
                        rfl

theorem cell23_7824842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_7824842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824842 prefixEnd_7824842 := by exact prefixLift 7824842
  have htrace : WordTrace (prefixWord ++ tailWord_7824842) baseStart_7824842 baseEnd_7824842 := by
    simpa [prefixWord, tailWord_7824842, baseEnd_7824842] using wordTrace_append hprefix tailTrace_7824842
  have hstable : (prefixWord ++ tailWord_7824842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824842).length < 2 ^ (prefixWord ++ tailWord_7824842).sum := by decide
  have hdescent : baseEnd_7824842 < baseStart_7824842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824865 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_7824865 : Nat := 118140960795 + 7824865 * 2 ^ 59
def prefixEnd_7824865 : Nat := 4983230072969 + 3 ^ 40 * 7824865 * 2
def baseEnd_7824865 : Nat := 4017916801543632913401607

theorem tailTrace_7824865 : CollatzResearch.WordTrace tailWord_7824865 prefixEnd_7824865 4017916801543632913401607 := by
  unfold tailWord_7824865
  simp only [CollatzResearch.WordTrace]
  refine ⟨285396272796857960392420049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190264181864571973594946699 285396272796857960392420049)
  ·
    refine ⟨214047204597643470294315037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285396272796857960392420049 214047204597643470294315037)
    ·
      refine ⟨80267701724116301360368139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214047204597643470294315037 80267701724116301360368139)
      ·
        refine ⟨120401552586174452040552209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80267701724116301360368139 120401552586174452040552209)
        ·
          refine ⟨90301164439630839030414157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120401552586174452040552209 90301164439630839030414157)
          ·
            refine ⟨33862936664861564636405309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90301164439630839030414157 33862936664861564636405309)
            ·
              refine ⟨12698601249323086738651991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33862936664861564636405309 12698601249323086738651991)
              ·
                refine ⟨19047901873984630107977987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698601249323086738651991 19047901873984630107977987)
                ·
                  refine ⟨28571852810976945161966981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19047901873984630107977987 28571852810976945161966981)
                  ·
                    refine ⟨5357222402058177217868809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28571852810976945161966981 5357222402058177217868809)
                    ·
                      refine ⟨4017916801543632913401607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357222402058177217868809 4017916801543632913401607)
                      ·
                        rfl

theorem cell23_7824865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_7824865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824865 prefixEnd_7824865 := by exact prefixLift 7824865
  have htrace : WordTrace (prefixWord ++ tailWord_7824865) baseStart_7824865 baseEnd_7824865 := by
    simpa [prefixWord, tailWord_7824865, baseEnd_7824865] using wordTrace_append hprefix tailTrace_7824865
  have hstable : (prefixWord ++ tailWord_7824865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824865).length < 2 ^ (prefixWord ++ tailWord_7824865).sum := by decide
  have hdescent : baseEnd_7824865 < baseStart_7824865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824882 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7824882 : Nat := 118140960795 + 7824882 * 2 ^ 59
def prefixEnd_7824882 : Nat := 4983230072969 + 3 ^ 40 * 7824882 * 2
def baseEnd_7824882 : Nat := 4017925530714759346889029

theorem tailTrace_7824882 : CollatzResearch.WordTrace tailWord_7824882 prefixEnd_7824882 4017925530714759346889029 := by
  unfold tailWord_7824882
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349223209449093073947225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190264595225197581530525933 71349223209449093073947225)
  ·
    refine ⟨53511917407086819805460419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71349223209449093073947225 53511917407086819805460419)
    ·
      refine ⟨80267876110630229708190629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53511917407086819805460419 80267876110630229708190629)
      ·
        refine ⟨15050226770743168070285743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80267876110630229708190629 15050226770743168070285743)
        ·
          refine ⟨22575340156114752105428615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050226770743168070285743 22575340156114752105428615)
          ·
            refine ⟨33863010234172128158142923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22575340156114752105428615 33863010234172128158142923)
            ·
              refine ⟨50794515351258192237214385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33863010234172128158142923 50794515351258192237214385)
              ·
                refine ⟨38095886513443644177910789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50794515351258192237214385 38095886513443644177910789)
                ·
                  refine ⟨7142978721270683283358273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38095886513443644177910789 7142978721270683283358273)
                  ·
                    refine ⟨5357234040953012462518705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142978721270683283358273 5357234040953012462518705)
                    ·
                      refine ⟨4017925530714759346889029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357234040953012462518705 4017925530714759346889029)
                      ·
                        rfl

theorem cell23_7824882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7824882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824882 prefixEnd_7824882 := by exact prefixLift 7824882
  have htrace : WordTrace (prefixWord ++ tailWord_7824882) baseStart_7824882 baseEnd_7824882 := by
    simpa [prefixWord, tailWord_7824882, baseEnd_7824882] using wordTrace_append hprefix tailTrace_7824882
  have hstable : (prefixWord ++ tailWord_7824882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824882).length < 2 ^ (prefixWord ++ tailWord_7824882).sum := by decide
  have hdescent : baseEnd_7824882 < baseStart_7824882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824885 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7824885 : Nat := 118140960795 + 7824885 * 2 ^ 59
def prefixEnd_7824885 : Nat := 4983230072969 + 3 ^ 40 * 7824885 * 2
def baseEnd_7824885 : Nat := 4017927071156722835151515

theorem tailTrace_7824885 : CollatzResearch.WordTrace tailWord_7824885 prefixEnd_7824885 4017927071156722835151515 := by
  unfold tailWord_7824885
  simp only [CollatzResearch.WordTrace]
  refine ⟨285397002256785503808148109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190264668171190335872098739 285397002256785503808148109)
  ·
    refine ⟨107023875846294563928055541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285397002256785503808148109 107023875846294563928055541)
    ·
      refine ⟨10033488360590115368255207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107023875846294563928055541 10033488360590115368255207)
      ·
        refine ⟨15050232540885173052382811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033488360590115368255207 15050232540885173052382811)
        ·
          refine ⟨22575348811327759578574217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050232540885173052382811 22575348811327759578574217)
          ·
            refine ⟨16931511608495819683930663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22575348811327759578574217 16931511608495819683930663)
            ·
              refine ⟨25397267412743729525895995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931511608495819683930663 25397267412743729525895995)
              ·
                refine ⟨38095901119115594288843993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25397267412743729525895995 38095901119115594288843993)
                ·
                  refine ⟨28571925839336695716632995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38095901119115594288843993 28571925839336695716632995)
                  ·
                    refine ⟨42857888759005043574949493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28571925839336695716632995 42857888759005043574949493)
                    ·
                      refine ⟨4017927071156722835151515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42857888759005043574949493 4017927071156722835151515)
                      ·
                        rfl

theorem cell23_7824885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7824885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824885 prefixEnd_7824885 := by exact prefixLift 7824885
  have htrace : WordTrace (prefixWord ++ tailWord_7824885) baseStart_7824885 baseEnd_7824885 := by
    simpa [prefixWord, tailWord_7824885, baseEnd_7824885] using wordTrace_append hprefix tailTrace_7824885
  have hstable : (prefixWord ++ tailWord_7824885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824885).length < 2 ^ (prefixWord ++ tailWord_7824885).sum := by decide
  have hdescent : baseEnd_7824885 < baseStart_7824885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824905 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 5]
def baseStart_7824905 : Nat := 118140960795 + 7824905 * 2 ^ 59
def prefixEnd_7824905 : Nat := 4983230072969 + 3 ^ 40 * 7824905 * 2
def baseEnd_7824905 : Nat := 446437482307756972989047

theorem tailTrace_7824905 : CollatzResearch.WordTrace tailWord_7824905 prefixEnd_7824905 446437482307756972989047 := by
  unfold tailWord_7824905
  simp only [CollatzResearch.WordTrace]
  refine ⟨285397731716713047223876169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190265154477808698149250779 285397731716713047223876169)
  ·
    refine ⟨214048298787534785417907127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285397731716713047223876169 214048298787534785417907127)
    ·
      refine ⟨321072448181302178126860691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214048298787534785417907127 321072448181302178126860691)
      ·
        refine ⟨481608672271953267190291037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321072448181302178126860691 481608672271953267190291037)
        ·
          refine ⟨180603252101982475196359139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481608672271953267190291037 180603252101982475196359139)
          ·
            refine ⟨270904878152973712794538709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180603252101982475196359139 270904878152973712794538709)
            ·
              refine ⟨6349333081710321393622001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270904878152973712794538709 6349333081710321393622001)
              ·
                refine ⟨4761999811282741045216501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349333081710321393622001 4761999811282741045216501)
                ·
                  refine ⟨446437482307756972989047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761999811282741045216501 446437482307756972989047)
                  ·
                    rfl

theorem cell23_7824905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 5].length) (baseStart_7824905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824905 prefixEnd_7824905 := by exact prefixLift 7824905
  have htrace : WordTrace (prefixWord ++ tailWord_7824905) baseStart_7824905 baseEnd_7824905 := by
    simpa [prefixWord, tailWord_7824905, baseEnd_7824905] using wordTrace_append hprefix tailTrace_7824905
  have hstable : (prefixWord ++ tailWord_7824905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824905).length < 2 ^ (prefixWord ++ tailWord_7824905).sum := by decide
  have hdescent : baseEnd_7824905 < baseStart_7824905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824916 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7824916 : Nat := 118140960795 + 7824916 * 2 ^ 59
def prefixEnd_7824916 : Nat := 4983230072969 + 3 ^ 40 * 7824916 * 2
def baseEnd_7824916 : Nat := 4017942989057012213863873

theorem tailTrace_7824916 : CollatzResearch.WordTrace tailWord_7824916 prefixEnd_7824916 4017942989057012213863873 := by
  unfold tailWord_7824916
  simp only [CollatzResearch.WordTrace]
  refine ⟨142699066459836598051263301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190265421946448797401684401 142699066459836598051263301)
  ·
    refine ⟨26756074961219362134611869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142699066459836598051263301 26756074961219362134611869)
    ·
      refine ⟨10033528110457260800479451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26756074961219362134611869 10033528110457260800479451)
      ·
        refine ⟨15050292165685891200719177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033528110457260800479451 15050292165685891200719177)
        ·
          refine ⟨11287719124264418400539383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15050292165685891200719177 11287719124264418400539383)
          ·
            refine ⟨16931578686396627600809075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287719124264418400539383 16931578686396627600809075)
            ·
              refine ⟨25397368029594941401213613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931578686396627600809075 25397368029594941401213613)
              ·
                refine ⟨9524013011098103025455105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25397368029594941401213613 9524013011098103025455105)
                ·
                  refine ⟨7143009758323577269091329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524013011098103025455105 7143009758323577269091329)
                  ·
                    refine ⟨5357257318742682951818497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143009758323577269091329 5357257318742682951818497)
                    ·
                      refine ⟨4017942989057012213863873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357257318742682951818497 4017942989057012213863873)
                      ·
                        rfl

theorem cell23_7824916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7824916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824916 prefixEnd_7824916 := by exact prefixLift 7824916
  have htrace : WordTrace (prefixWord ++ tailWord_7824916) baseStart_7824916 baseEnd_7824916 := by
    simpa [prefixWord, tailWord_7824916, baseEnd_7824916] using wordTrace_append hprefix tailTrace_7824916
  have hstable : (prefixWord ++ tailWord_7824916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824916).length < 2 ^ (prefixWord ++ tailWord_7824916).sum := by decide
  have hdescent : baseEnd_7824916 < baseStart_7824916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_7825015 : Nat := 118140960795 + 7825015 * 2 ^ 59
def prefixEnd_7825015 : Nat := 4983230072969 + 3 ^ 40 * 7825015 * 2
def baseEnd_7825015 : Nat := 4017993823641807326525917

theorem tailTrace_7825015 : CollatzResearch.WordTrace tailWord_7825015 prefixEnd_7825015 4017993823641807326525917 := by
  unfold tailWord_7825015
  simp only [CollatzResearch.WordTrace]
  refine ⟨285401743746314536010380499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190267829164209690673586999 285401743746314536010380499)
  ·
    refine ⟨428102615619471804015570749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285401743746314536010380499 428102615619471804015570749)
    ·
      refine ⟨160538480857301926505839031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428102615619471804015570749 160538480857301926505839031)
      ·
        refine ⟨240807721285952889758758547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160538480857301926505839031 240807721285952889758758547)
        ·
          refine ⟨361211581928929334638137821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240807721285952889758758547 361211581928929334638137821)
          ·
            refine ⟨135454343223348500489301683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361211581928929334638137821 135454343223348500489301683)
            ·
              refine ⟨203181514835022750733952525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135454343223348500489301683 203181514835022750733952525)
              ·
                refine ⟨76193068063133531525232197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203181514835022750733952525 76193068063133531525232197)
                ·
                  refine ⟨14286200261837537160981037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76193068063133531525232197 14286200261837537160981037)
                  ·
                    refine ⟨5357325098189076435367889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14286200261837537160981037 5357325098189076435367889)
                    ·
                      refine ⟨4017993823641807326525917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357325098189076435367889 4017993823641807326525917)
                      ·
                        rfl

theorem cell23_7825015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_7825015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825015 prefixEnd_7825015 := by exact prefixLift 7825015
  have htrace : WordTrace (prefixWord ++ tailWord_7825015) baseStart_7825015 baseEnd_7825015 := by
    simpa [prefixWord, tailWord_7825015, baseEnd_7825015] using wordTrace_append hprefix tailTrace_7825015
  have hstable : (prefixWord ++ tailWord_7825015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825015).length < 2 ^ (prefixWord ++ tailWord_7825015).sum := by decide
  have hdescent : baseEnd_7825015 < baseStart_7825015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825056 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 1, 1, 3]
def baseStart_7825056 : Nat := 118140960795 + 7825056 * 2 ^ 59
def prefixEnd_7825056 : Nat := 4983230072969 + 3 ^ 40 * 7825056 * 2
def baseEnd_7825056 : Nat := 4018014876348641666113229

theorem tailTrace_7825056 : CollatzResearch.WordTrace tailWord_7825056 prefixEnd_7825056 4018014876348641666113229 := by
  unfold tailWord_7825056
  simp only [CollatzResearch.WordTrace]
  refine ⟨142701619569583000006311511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190268826092777333341748681 142701619569583000006311511)
  ·
    refine ⟨214052429354374500009467267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142701619569583000006311511 214052429354374500009467267)
    ·
      refine ⟨321078644031561750014200901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214052429354374500009467267 321078644031561750014200901)
      ·
        refine ⟨60202245755917828127662669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321078644031561750014200901 60202245755917828127662669)
        ·
          refine ⟨22575842158469185547873501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60202245755917828127662669 22575842158469185547873501)
          ·
            refine ⟨8465940809425944580452563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22575842158469185547873501 8465940809425944580452563)
            ·
              refine ⟨12698911214138916870678845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465940809425944580452563 12698911214138916870678845)
              ·
                refine ⟨4762091705302093826504567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12698911214138916870678845 4762091705302093826504567)
                ·
                  refine ⟨7143137557953140739756851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762091705302093826504567 7143137557953140739756851)
                  ·
                    refine ⟨10714706336929711109635277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143137557953140739756851 10714706336929711109635277)
                    ·
                      refine ⟨4018014876348641666113229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10714706336929711109635277 4018014876348641666113229)
                      ·
                        rfl

theorem cell23_7825056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_7825056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825056 prefixEnd_7825056 := by exact prefixLift 7825056
  have htrace : WordTrace (prefixWord ++ tailWord_7825056) baseStart_7825056 baseEnd_7825056 := by
    simpa [prefixWord, tailWord_7825056, baseEnd_7825056] using wordTrace_append hprefix tailTrace_7825056
  have hstable : (prefixWord ++ tailWord_7825056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825056).length < 2 ^ (prefixWord ++ tailWord_7825056).sum := by decide
  have hdescent : baseEnd_7825056 < baseStart_7825056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825079 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_7825079 : Nat := 118140960795 + 7825079 * 2 ^ 59
def prefixEnd_7825079 : Nat := 4983230072969 + 3 ^ 40 * 7825079 * 2
def baseEnd_7825079 : Nat := 4018026686403695076125623

theorem tailTrace_7825079 : CollatzResearch.WordTrace tailWord_7825079 prefixEnd_7825079 4018026686403695076125623 := by
  unfold tailWord_7825079
  simp only [CollatzResearch.WordTrace]
  refine ⟨285404078018082674940710291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190269385345388449960473527 285404078018082674940710291)
  ·
    refine ⟨428106117027124012411065437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285404078018082674940710291 428106117027124012411065437)
    ·
      refine ⟨160539793885171504654149539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428106117027124012411065437 160539793885171504654149539)
      ·
        refine ⟨240809690827757256981224309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160539793885171504654149539 240809690827757256981224309)
        ·
          refine ⟨22575908515102242841989779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240809690827757256981224309 22575908515102242841989779)
          ·
            refine ⟨33863862772653364262984669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22575908515102242841989779 33863862772653364262984669)
            ·
              refine ⟨12698948539745011598619251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33863862772653364262984669 12698948539745011598619251)
              ·
                refine ⟨19048422809617517397928877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698948539745011598619251 19048422809617517397928877)
                ·
                  refine ⟨7143158553606569024223329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19048422809617517397928877 7143158553606569024223329)
                  ·
                    refine ⟨5357368915204926768167497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143158553606569024223329 5357368915204926768167497)
                    ·
                      refine ⟨4018026686403695076125623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357368915204926768167497 4018026686403695076125623)
                      ·
                        rfl

theorem cell23_7825079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_7825079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825079 prefixEnd_7825079 := by exact prefixLift 7825079
  have htrace : WordTrace (prefixWord ++ tailWord_7825079) baseStart_7825079 baseEnd_7825079 := by
    simpa [prefixWord, tailWord_7825079, baseEnd_7825079] using wordTrace_append hprefix tailTrace_7825079
  have hstable : (prefixWord ++ tailWord_7825079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825079).length < 2 ^ (prefixWord ++ tailWord_7825079).sum := by decide
  have hdescent : baseEnd_7825079 < baseStart_7825079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825088 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_7825088 : Nat := 118140960795 + 7825088 * 2 ^ 59
def prefixEnd_7825088 : Nat := 4983230072969 + 3 ^ 40 * 7825088 * 2
def baseEnd_7825088 : Nat := 4018031307729585540913081

theorem tailTrace_7825088 : CollatzResearch.WordTrace tailWord_7825088 prefixEnd_7825088 4018031307729585540913081 := by
  unfold tailWord_7825088
  simp only [CollatzResearch.WordTrace]
  refine ⟨142702203137525034738893959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190269604183366712985191945 142702203137525034738893959)
  ·
    refine ⟨214053304706287552108340939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142702203137525034738893959 214053304706287552108340939)
    ·
      refine ⟨321079957059431328162511409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214053304706287552108340939 321079957059431328162511409)
      ·
        refine ⟨240809967794573496121883557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321079957059431328162511409 240809967794573496121883557)
        ·
          refine ⟨45151868961482530522853167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240809967794573496121883557 45151868961482530522853167)
          ·
            refine ⟨67727803442223795784279751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45151868961482530522853167 67727803442223795784279751)
            ·
              refine ⟨101591705163335693676419627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67727803442223795784279751 101591705163335693676419627)
              ·
                refine ⟨152387557745003540514629441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101591705163335693676419627 152387557745003540514629441)
                ·
                  refine ⟨114290668308752655385972081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152387557745003540514629441 114290668308752655385972081)
                  ·
                    refine ⟨85718001231564491539479061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114290668308752655385972081 85718001231564491539479061)
                    ·
                      refine ⟨4018031307729585540913081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85718001231564491539479061 4018031307729585540913081)
                      ·
                        rfl

theorem cell23_7825088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_7825088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825088 prefixEnd_7825088 := by exact prefixLift 7825088
  have htrace : WordTrace (prefixWord ++ tailWord_7825088) baseStart_7825088 baseEnd_7825088 := by
    simpa [prefixWord, tailWord_7825088, baseEnd_7825088] using wordTrace_append hprefix tailTrace_7825088
  have hstable : (prefixWord ++ tailWord_7825088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825088).length < 2 ^ (prefixWord ++ tailWord_7825088).sum := by decide
  have hdescent : baseEnd_7825088 < baseStart_7825088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825095 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_7825095 : Nat := 118140960795 + 7825095 * 2 ^ 59
def prefixEnd_7825095 : Nat := 4983230072969 + 3 ^ 40 * 7825095 * 2
def baseEnd_7825095 : Nat := 4018034902094167013525549

theorem tailTrace_7825095 : CollatzResearch.WordTrace tailWord_7825095 prefixEnd_7825095 4018034902094167013525549 := by
  unfold tailWord_7825095
  simp only [CollatzResearch.WordTrace]
  refine ⟨285404661586024709673292739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190269774390683139782195159 285404661586024709673292739)
  ·
    refine ⟨428106992379037064509939109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285404661586024709673292739 428106992379037064509939109)
    ·
      refine ⟨80270061071069449595613583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428106992379037064509939109 80270061071069449595613583)
      ·
        refine ⟨120405091606604174393420375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80270061071069449595613583 120405091606604174393420375)
        ·
          refine ⟨180607637409906261590130563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120405091606604174393420375 180607637409906261590130563)
          ·
            refine ⟨270911456114859392385195845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180607637409906261590130563 270911456114859392385195845)
            ·
              refine ⟨50795898021536136072224221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270911456114859392385195845 50795898021536136072224221)
              ·
                refine ⟨19048461758076051027084083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50795898021536136072224221 19048461758076051027084083)
                ·
                  refine ⟨28572692637114076540626125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19048461758076051027084083 28572692637114076540626125)
                  ·
                    refine ⟨10714759738917778702734797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28572692637114076540626125 10714759738917778702734797)
                    ·
                      refine ⟨4018034902094167013525549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10714759738917778702734797 4018034902094167013525549)
                      ·
                        rfl

theorem cell23_7825095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_7825095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825095 prefixEnd_7825095 := by exact prefixLift 7825095
  have htrace : WordTrace (prefixWord ++ tailWord_7825095) baseStart_7825095 baseEnd_7825095 := by
    simpa [prefixWord, tailWord_7825095, baseEnd_7825095] using wordTrace_append hprefix tailTrace_7825095
  have hstable : (prefixWord ++ tailWord_7825095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825095).length < 2 ^ (prefixWord ++ tailWord_7825095).sum := by decide
  have hdescent : baseEnd_7825095 < baseStart_7825095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825116 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7825116 : Nat := 118140960795 + 7825116 * 2 ^ 59
def prefixEnd_7825116 : Nat := 4983230072969 + 3 ^ 40 * 7825116 * 2
def baseEnd_7825116 : Nat := 4018045685187911431362953

theorem tailTrace_7825116 : CollatzResearch.WordTrace tailWord_7825116 prefixEnd_7825116 4018045685187911431362953 := by
  unfold tailWord_7825116
  simp only [CollatzResearch.WordTrace]
  refine ⟨142702713759474315129903601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190270285012632420173204801 142702713759474315129903601)
  ·
    refine ⟨107027035319605736347427701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142702713759474315129903601 107027035319605736347427701)
    ·
      refine ⟨10033784561213037782571347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107027035319605736347427701 10033784561213037782571347)
      ·
        refine ⟨15050676841819556673857021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033784561213037782571347 15050676841819556673857021)
        ·
          refine ⟨5644003815682333752696383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15050676841819556673857021 5644003815682333752696383)
          ·
            refine ⟨8466005723523500629044575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644003815682333752696383 8466005723523500629044575)
            ·
              refine ⟨12699008585285250943566863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8466005723523500629044575 12699008585285250943566863)
              ·
                refine ⟨19048512877927876415350295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699008585285250943566863 19048512877927876415350295)
                ·
                  refine ⟨28572769316891814623025443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19048512877927876415350295 28572769316891814623025443)
                  ·
                    refine ⟨42859153975337721934538165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28572769316891814623025443 42859153975337721934538165)
                    ·
                      refine ⟨4018045685187911431362953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42859153975337721934538165 4018045685187911431362953)
                      ·
                        rfl

theorem cell23_7825116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7825116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825116 prefixEnd_7825116 := by exact prefixLift 7825116
  have htrace : WordTrace (prefixWord ++ tailWord_7825116) baseStart_7825116 baseEnd_7825116 := by
    simpa [prefixWord, tailWord_7825116, baseEnd_7825116] using wordTrace_append hprefix tailTrace_7825116
  have hstable : (prefixWord ++ tailWord_7825116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825116).length < 2 ^ (prefixWord ++ tailWord_7825116).sum := by decide
  have hdescent : baseEnd_7825116 < baseStart_7825116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825192 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 7]
def baseStart_7825192 : Nat := 118140960795 + 7825192 * 2 ^ 59
def prefixEnd_7825192 : Nat := 4983230072969 + 3 ^ 40 * 7825192 * 2
def baseEnd_7825192 : Nat := 446453856635294792668067

theorem tailTrace_7825192 : CollatzResearch.WordTrace tailWord_7825192 prefixEnd_7825192 446453856635294792668067 := by
  unfold tailWord_7825192
  simp only [CollatzResearch.WordTrace]
  refine ⟨142704099733336647619786915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190272132977782196826382553 142704099733336647619786915)
  ·
    refine ⟨214056149600004971429680373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142704099733336647619786915 214056149600004971429680373)
    ·
      refine ⟨20067764025000466071532535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214056149600004971429680373 20067764025000466071532535)
      ·
        refine ⟨30101646037500699107298803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067764025000466071532535 30101646037500699107298803)
        ·
          refine ⟨45152469056251048660948205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30101646037500699107298803 45152469056251048660948205)
          ·
            refine ⟨16932175896094143247855577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45152469056251048660948205 16932175896094143247855577)
            ·
              refine ⟨12699131922070607435891683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16932175896094143247855577 12699131922070607435891683)
              ·
                refine ⟨19048697883105911153837525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699131922070607435891683 19048697883105911153837525)
                ·
                  refine ⟨446453856635294792668067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19048697883105911153837525 446453856635294792668067)
                  ·
                    rfl

theorem cell23_7825192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_7825192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825192 prefixEnd_7825192 := by exact prefixLift 7825192
  have htrace : WordTrace (prefixWord ++ tailWord_7825192) baseStart_7825192 baseEnd_7825192 := by
    simpa [prefixWord, tailWord_7825192, baseEnd_7825192] using wordTrace_append hprefix tailTrace_7825192
  have hstable : (prefixWord ++ tailWord_7825192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825192).length < 2 ^ (prefixWord ++ tailWord_7825192).sum := by decide
  have hdescent : baseEnd_7825192 < baseStart_7825192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825202 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_7825202 : Nat := 118140960795 + 7825202 * 2 ^ 59
def prefixEnd_7825202 : Nat := 4983230072969 + 3 ^ 40 * 7825202 * 2
def baseEnd_7825202 : Nat := 4018089844524198094887557

theorem tailTrace_7825202 : CollatzResearch.WordTrace tailWord_7825202 prefixEnd_7825202 4018089844524198094887557 := by
  unfold tailWord_7825202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71352141049159266736859465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190272376131091377964958573 71352141049159266736859465)
  ·
    refine ⟨53514105786869450052644599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71352141049159266736859465 53514105786869450052644599)
    ·
      refine ⟨80271158680304175078966899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53514105786869450052644599 80271158680304175078966899)
      ·
        refine ⟨120406738020456262618450349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80271158680304175078966899 120406738020456262618450349)
        ·
          refine ⟨45152526757671098481918881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120406738020456262618450349 45152526757671098481918881)
          ·
            refine ⟨33864395068253323861439161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45152526757671098481918881 33864395068253323861439161)
            ·
              refine ⟨25398296301189992896079371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33864395068253323861439161 25398296301189992896079371)
              ·
                refine ⟨38097444451784989344119057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25398296301189992896079371 38097444451784989344119057)
                ·
                  refine ⟨28573083338838742008089293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38097444451784989344119057 28573083338838742008089293)
                  ·
                    refine ⟨10714906252064528253033485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28573083338838742008089293 10714906252064528253033485)
                    ·
                      refine ⟨4018089844524198094887557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10714906252064528253033485 4018089844524198094887557)
                      ·
                        rfl

theorem cell23_7825202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_7825202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825202 prefixEnd_7825202 := by exact prefixLift 7825202
  have htrace : WordTrace (prefixWord ++ tailWord_7825202) baseStart_7825202 baseEnd_7825202 := by
    simpa [prefixWord, tailWord_7825202, baseEnd_7825202] using wordTrace_append hprefix tailTrace_7825202
  have hstable : (prefixWord ++ tailWord_7825202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825202).length < 2 ^ (prefixWord ++ tailWord_7825202).sum := by decide
  have hdescent : baseEnd_7825202 < baseStart_7825202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825203 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 2, 2, 2]
def baseStart_7825203 : Nat := 118140960795 + 7825203 * 2 ^ 59
def prefixEnd_7825203 : Nat := 4983230072969 + 3 ^ 40 * 7825203 * 2
def baseEnd_7825203 : Nat := 4018090358004852590975053

theorem tailTrace_7825203 : CollatzResearch.WordTrace tailWord_7825203 prefixEnd_7825203 4018090358004852590975053 := by
  unfold tailWord_7825203
  simp only [CollatzResearch.WordTrace]
  refine ⟨285408600669633444118224263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190272400446422296078816175 285408600669633444118224263)
  ·
    refine ⟨428112901004450166177336395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285408600669633444118224263 428112901004450166177336395)
    ·
      refine ⟨642169351506675249266004593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428112901004450166177336395 642169351506675249266004593)
      ·
        refine ⟨481627013630006436949503445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642169351506675249266004593 481627013630006436949503445)
        ·
          refine ⟨11288133131953275866003987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 481627013630006436949503445 11288133131953275866003987)
          ·
            refine ⟨16932199697929913799005981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288133131953275866003987 16932199697929913799005981)
            ·
              refine ⟨6349574886723717674627243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16932199697929913799005981 6349574886723717674627243)
              ·
                refine ⟨9524362330085576511940865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349574886723717674627243 9524362330085576511940865)
                ·
                  refine ⟨7143271747564182383955649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524362330085576511940865 7143271747564182383955649)
                  ·
                    refine ⟨5357453810673136787966737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143271747564182383955649 5357453810673136787966737)
                    ·
                      refine ⟨4018090358004852590975053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357453810673136787966737 4018090358004852590975053)
                      ·
                        rfl

theorem cell23_7825203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 2, 2].length) (baseStart_7825203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825203 prefixEnd_7825203 := by exact prefixLift 7825203
  have htrace : WordTrace (prefixWord ++ tailWord_7825203) baseStart_7825203 baseEnd_7825203 := by
    simpa [prefixWord, tailWord_7825203, baseEnd_7825203] using wordTrace_append hprefix tailTrace_7825203
  have hstable : (prefixWord ++ tailWord_7825203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825203).length < 2 ^ (prefixWord ++ tailWord_7825203).sum := by decide
  have hdescent : baseEnd_7825203 < baseStart_7825203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825212 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_7825212 : Nat := 118140960795 + 7825212 * 2 ^ 59
def prefixEnd_7825212 : Nat := 4983230072969 + 3 ^ 40 * 7825212 * 2
def baseEnd_7825212 : Nat := 4018094979330743055762511

theorem tailTrace_7825212 : CollatzResearch.WordTrace tailWord_7825212 prefixEnd_7825212 4018094979330743055762511 := by
  unfold tailWord_7825212
  simp only [CollatzResearch.WordTrace]
  refine ⟨142704464463300419327650945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190272619284400559103534593 142704464463300419327650945)
  ·
    refine ⟨107028348347475314495738209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142704464463300419327650945 107028348347475314495738209)
    ·
      refine ⟨80271261260606485871803657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107028348347475314495738209 80271261260606485871803657)
      ·
        refine ⟨60203445945454864403852743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80271261260606485871803657 60203445945454864403852743)
        ·
          refine ⟨90305168918182296605779115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60203445945454864403852743 90305168918182296605779115)
          ·
            refine ⟨135457753377273444908668673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90305168918182296605779115 135457753377273444908668673)
            ·
              refine ⟨101593315032955083681501505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135457753377273444908668673 101593315032955083681501505)
              ·
                refine ⟨76194986274716312761126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101593315032955083681501505 76194986274716312761126129)
                ·
                  refine ⟨57146239706037234570844597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76194986274716312761126129 57146239706037234570844597)
                  ·
                    refine ⟨5357459972440990741016681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57146239706037234570844597 5357459972440990741016681)
                    ·
                      refine ⟨4018094979330743055762511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357459972440990741016681 4018094979330743055762511)
                      ·
                        rfl

theorem cell23_7825212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_7825212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825212 prefixEnd_7825212 := by exact prefixLift 7825212
  have htrace : WordTrace (prefixWord ++ tailWord_7825212) baseStart_7825212 baseEnd_7825212 := by
    simpa [prefixWord, tailWord_7825212, baseEnd_7825212] using wordTrace_append hprefix tailTrace_7825212
  have hstable : (prefixWord ++ tailWord_7825212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825212).length < 2 ^ (prefixWord ++ tailWord_7825212).sum := by decide
  have hdescent : baseEnd_7825212 < baseStart_7825212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825225 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_7825225 : Nat := 118140960795 + 7825225 * 2 ^ 59
def prefixEnd_7825225 : Nat := 4983230072969 + 3 ^ 40 * 7825225 * 2
def baseEnd_7825225 : Nat := 4018101654579251504899951

theorem tailTrace_7825225 : CollatzResearch.WordTrace tailWord_7825225 prefixEnd_7825225 4018101654579251504899951 := by
  unfold tailWord_7825225
  simp only [CollatzResearch.WordTrace]
  refine ⟨285409403075553741875525129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190272935383702494583683419 285409403075553741875525129)
  ·
    refine ⟨214057052306665306406643847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285409403075553741875525129 214057052306665306406643847)
    ·
      refine ⟨321085578459997959609965771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214057052306665306406643847 321085578459997959609965771)
      ·
        refine ⟨481628367689996939414948657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321085578459997959609965771 481628367689996939414948657)
        ·
          refine ⟨361221275767497704561211493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481628367689996939414948657 361221275767497704561211493)
          ·
            refine ⟨67728989206405819605227155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361221275767497704561211493 67728989206405819605227155)
            ·
              refine ⟨101593483809608729407840733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67728989206405819605227155 101593483809608729407840733)
              ·
                refine ⟨38097556428603273527940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101593483809608729407840733 38097556428603273527940275)
                ·
                  refine ⟨57146334642904910291910413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38097556428603273527940275 57146334642904910291910413)
                  ·
                    refine ⟨21429875491089341359466405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57146334642904910291910413 21429875491089341359466405)
                    ·
                      refine ⟨4018101654579251504899951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21429875491089341359466405 4018101654579251504899951)
                      ·
                        rfl

theorem cell23_7825225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_7825225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825225 prefixEnd_7825225 := by exact prefixLift 7825225
  have htrace : WordTrace (prefixWord ++ tailWord_7825225) baseStart_7825225 baseEnd_7825225 := by
    simpa [prefixWord, tailWord_7825225, baseEnd_7825225] using wordTrace_append hprefix tailTrace_7825225
  have hstable : (prefixWord ++ tailWord_7825225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825225).length < 2 ^ (prefixWord ++ tailWord_7825225).sum := by decide
  have hdescent : baseEnd_7825225 < baseStart_7825225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825242 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_7825242 : Nat := 118140960795 + 7825242 * 2 ^ 59
def prefixEnd_7825242 : Nat := 4983230072969 + 3 ^ 40 * 7825242 * 2
def baseEnd_7825242 : Nat := 4018110383750377938387373

theorem tailTrace_7825242 : CollatzResearch.WordTrace tailWord_7825242 prefixEnd_7825242 4018110383750377938387373 := by
  unfold tailWord_7825242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71352505779123038444723495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190273348744328102519262653 71352505779123038444723495)
  ·
    refine ⟨107028758668684557667085243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71352505779123038444723495 107028758668684557667085243)
    ·
      refine ⟨160543138003026836500627865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107028758668684557667085243 160543138003026836500627865)
      ·
        refine ⟨120407353502270127375470899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160543138003026836500627865 120407353502270127375470899)
        ·
          refine ⟨180611030253405191063206349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120407353502270127375470899 180611030253405191063206349)
          ·
            refine ⟨67729136345026946648702381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180611030253405191063206349 67729136345026946648702381)
            ·
              refine ⟨25398426129385104993263393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67729136345026946648702381 25398426129385104993263393)
              ·
                refine ⟨19048819597038828744947545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25398426129385104993263393 19048819597038828744947545)
                ·
                  refine ⟨14286614697779121558710659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19048819597038828744947545 14286614697779121558710659)
                  ·
                    refine ⟨21429922046668682338065989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14286614697779121558710659 21429922046668682338065989)
                    ·
                      refine ⟨4018110383750377938387373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21429922046668682338065989 4018110383750377938387373)
                      ·
                        rfl

theorem cell23_7825242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_7825242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825242 prefixEnd_7825242 := by exact prefixLift 7825242
  have htrace : WordTrace (prefixWord ++ tailWord_7825242) baseStart_7825242 baseEnd_7825242 := by
    simpa [prefixWord, tailWord_7825242, baseEnd_7825242] using wordTrace_append hprefix tailTrace_7825242
  have hstable : (prefixWord ++ tailWord_7825242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825242).length < 2 ^ (prefixWord ++ tailWord_7825242).sum := by decide
  have hdescent : baseEnd_7825242 < baseStart_7825242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825303 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 1, 4]
def baseStart_7825303 : Nat := 118140960795 + 7825303 * 2 ^ 59
def prefixEnd_7825303 : Nat := 4983230072969 + 3 ^ 40 * 7825303 * 2
def baseEnd_7825303 : Nat := 1339380568690100733241531

theorem tailTrace_7825303 : CollatzResearch.WordTrace tailWord_7825303 prefixEnd_7825303 1339380568690100733241531 := by
  unfold tailWord_7825303
  simp only [CollatzResearch.WordTrace]
  refine ⟨285412247969271161196864563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190274831979514107464576375 285412247969271161196864563)
  ·
    refine ⟨428118371953906741795296845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285412247969271161196864563 428118371953906741795296845)
    ·
      refine ⟨160544389482715028173236317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428118371953906741795296845 160544389482715028173236317)
      ·
        refine ⟨60204146056018135564963619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160544389482715028173236317 60204146056018135564963619)
        ·
          refine ⟨90306219084027203347445429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60204146056018135564963619 90306219084027203347445429)
          ·
            refine ⟨8466208039127550313823009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90306219084027203347445429 8466208039127550313823009)
            ·
              refine ⟨6349656029345662735367257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8466208039127550313823009 6349656029345662735367257)
              ·
                refine ⟨4762242022009247051525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349656029345662735367257 4762242022009247051525443)
                ·
                  refine ⟨7143363033013870577288165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762242022009247051525443 7143363033013870577288165)
                  ·
                    refine ⟨1339380568690100733241531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7143363033013870577288165 1339380568690100733241531)
                    ·
                      rfl

theorem cell23_7825303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_7825303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825303 prefixEnd_7825303 := by exact prefixLift 7825303
  have htrace : WordTrace (prefixWord ++ tailWord_7825303) baseStart_7825303 baseEnd_7825303 := by
    simpa [prefixWord, tailWord_7825303, baseEnd_7825303] using wordTrace_append hprefix tailTrace_7825303
  have hstable : (prefixWord ++ tailWord_7825303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825303).length < 2 ^ (prefixWord ++ tailWord_7825303).sum := by decide
  have hdescent : baseEnd_7825303 < baseStart_7825303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825355 : List Nat := [1, 1, 1, 1, 3, 4, 12]
def baseStart_7825355 : Nat := 118140960795 + 7825355 * 2 ^ 59
def prefixEnd_7825355 : Nat := 4983230072969 + 3 ^ 40 * 7825355 * 2
def baseEnd_7825355 : Nat := 49607017371164641929313

theorem tailTrace_7825355 : CollatzResearch.WordTrace tailWord_7825355 prefixEnd_7825355 49607017371164641929313 := by
  unfold tailWord_7825355
  simp only [CollatzResearch.WordTrace]
  refine ⟨285414144565082774077757519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190276096376721849385171679 285414144565082774077757519)
  ·
    refine ⟨428121216847624161116636279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285414144565082774077757519 428121216847624161116636279)
    ·
      refine ⟨642181825271436241674954419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428121216847624161116636279 642181825271436241674954419)
      ·
        refine ⟨963272737907154362512431629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642181825271436241674954419 963272737907154362512431629)
        ·
          refine ⟨361227276715182885942161861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 963272737907154362512431629 361227276715182885942161861)
          ·
            refine ⟨67730114384096791114155349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361227276715182885942161861 67730114384096791114155349)
            ·
              refine ⟨49607017371164641929313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67730114384096791114155349 49607017371164641929313)
              ·
                rfl

theorem cell23_7825355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 12].length) (baseStart_7825355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825355 prefixEnd_7825355 := by exact prefixLift 7825355
  have htrace : WordTrace (prefixWord ++ tailWord_7825355) baseStart_7825355 baseEnd_7825355 := by
    simpa [prefixWord, tailWord_7825355, baseEnd_7825355] using wordTrace_append hprefix tailTrace_7825355
  have hstable : (prefixWord ++ tailWord_7825355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825355).length < 2 ^ (prefixWord ++ tailWord_7825355).sum := by decide
  have hdescent : baseEnd_7825355 < baseStart_7825355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825369 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_7825369 : Nat := 118140960795 + 7825369 * 2 ^ 59
def prefixEnd_7825369 : Nat := 4983230072969 + 3 ^ 40 * 7825369 * 2
def baseEnd_7825369 : Nat := 4018175595793498941499289

theorem tailTrace_7825369 : CollatzResearch.WordTrace tailWord_7825369 prefixEnd_7825369 4018175595793498941499289 := by
  unfold tailWord_7825369
  simp only [CollatzResearch.WordTrace]
  refine ⟨285414655187032054468767161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190276436791354702979178107 285414655187032054468767161)
  ·
    refine ⟨214060991390274040851575371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285414655187032054468767161 214060991390274040851575371)
    ·
      refine ⟨321091487085411061277363057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214060991390274040851575371 321091487085411061277363057)
      ·
        refine ⟨240818615314058295958022293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321091487085411061277363057 240818615314058295958022293)
        ·
          refine ⟨11288372592846482623032295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240818615314058295958022293 11288372592846482623032295)
          ·
            refine ⟨16932558889269723934548443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288372592846482623032295 16932558889269723934548443)
            ·
              refine ⟨25398838333904585901822665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932558889269723934548443 25398838333904585901822665)
              ·
                refine ⟨19049128750428439426366999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25398838333904585901822665 19049128750428439426366999)
                ·
                  refine ⟨28573693125642659139550499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19049128750428439426366999 28573693125642659139550499)
                  ·
                    refine ⟨42860539688463988709325749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28573693125642659139550499 42860539688463988709325749)
                    ·
                      refine ⟨4018175595793498941499289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42860539688463988709325749 4018175595793498941499289)
                      ·
                        rfl

theorem cell23_7825369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_7825369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825369 prefixEnd_7825369 := by exact prefixLift 7825369
  have htrace : WordTrace (prefixWord ++ tailWord_7825369) baseStart_7825369 baseEnd_7825369 := by
    simpa [prefixWord, tailWord_7825369, baseEnd_7825369] using wordTrace_append hprefix tailTrace_7825369
  have hstable : (prefixWord ++ tailWord_7825369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825369).length < 2 ^ (prefixWord ++ tailWord_7825369).sum := by decide
  have hdescent : baseEnd_7825369 < baseStart_7825369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825379 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7825379 : Nat := 118140960795 + 7825379 * 2 ^ 59
def prefixEnd_7825379 : Nat := 4983230072969 + 3 ^ 40 * 7825379 * 2
def baseEnd_7825379 : Nat := 4018180730600043902374243

theorem tailTrace_7825379 : CollatzResearch.WordTrace tailWord_7825379 prefixEnd_7825379 4018180730600043902374243 := by
  unfold tailWord_7825379
  simp only [CollatzResearch.WordTrace]
  refine ⟨285415019916995826176631191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190276679944663884117754127 285415019916995826176631191)
  ·
    refine ⟨428122529875493739264946787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285415019916995826176631191 428122529875493739264946787)
    ·
      refine ⟨642183794813240608897420181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428122529875493739264946787 642183794813240608897420181)
      ·
        refine ⟨30102365381870653542066571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 642183794813240608897420181 30102365381870653542066571)
        ·
          refine ⟨45153548072805980313099857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30102365381870653542066571 45153548072805980313099857)
          ·
            refine ⟨33865161054604485234824893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45153548072805980313099857 33865161054604485234824893)
            ·
              refine ⟨12699435395476681963059335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33865161054604485234824893 12699435395476681963059335)
              ·
                refine ⟨19049153093215022944589003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699435395476681963059335 19049153093215022944589003)
                ·
                  refine ⟨28573729639822534416883505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19049153093215022944589003 28573729639822534416883505)
                  ·
                    refine ⟨21430297229866900812662629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28573729639822534416883505 21430297229866900812662629)
                    ·
                      refine ⟨4018180730600043902374243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21430297229866900812662629 4018180730600043902374243)
                      ·
                        rfl

theorem cell23_7825379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7825379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825379 prefixEnd_7825379 := by exact prefixLift 7825379
  have htrace : WordTrace (prefixWord ++ tailWord_7825379) baseStart_7825379 baseEnd_7825379 := by
    simpa [prefixWord, tailWord_7825379, baseEnd_7825379] using wordTrace_append hprefix tailTrace_7825379
  have hstable : (prefixWord ++ tailWord_7825379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825379).length < 2 ^ (prefixWord ++ tailWord_7825379).sum := by decide
  have hdescent : baseEnd_7825379 < baseStart_7825379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825386 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_7825386 : Nat := 118140960795 + 7825386 * 2 ^ 59
def prefixEnd_7825386 : Nat := 4983230072969 + 3 ^ 40 * 7825386 * 2
def baseEnd_7825386 : Nat := 4018184324964625374986711

theorem tailTrace_7825386 : CollatzResearch.WordTrace tailWord_7825386 prefixEnd_7825386 4018184324964625374986711 := by
  unfold tailWord_7825386
  simp only [CollatzResearch.WordTrace]
  refine ⟨71353818806992616593034003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190276850151980310914757341 71353818806992616593034003)
  ·
    refine ⟨107030728210488924889551005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71353818806992616593034003 107030728210488924889551005)
    ·
      refine ⟨40136523078933346833581627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107030728210488924889551005 40136523078933346833581627)
      ·
        refine ⟨60204784618400020250372441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40136523078933346833581627 60204784618400020250372441)
        ·
          refine ⟨45153588463800015187779331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60204784618400020250372441 45153588463800015187779331)
          ·
            refine ⟨67730382695700022781668997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45153588463800015187779331 67730382695700022781668997)
            ·
              refine ⟨12699446755443754271562937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67730382695700022781668997 12699446755443754271562937)
              ·
                refine ⟨9524585066582815703672203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12699446755443754271562937 9524585066582815703672203)
                ·
                  refine ⟨14286877599874223555508305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524585066582815703672203 14286877599874223555508305)
                  ·
                    refine ⟨10715158199905667666631229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14286877599874223555508305 10715158199905667666631229)
                    ·
                      refine ⟨4018184324964625374986711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715158199905667666631229 4018184324964625374986711)
                      ·
                        rfl

theorem cell23_7825386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_7825386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825386 prefixEnd_7825386 := by exact prefixLift 7825386
  have htrace : WordTrace (prefixWord ++ tailWord_7825386) baseStart_7825386 baseEnd_7825386 := by
    simpa [prefixWord, tailWord_7825386, baseEnd_7825386] using wordTrace_append hprefix tailTrace_7825386
  have hstable : (prefixWord ++ tailWord_7825386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825386).length < 2 ^ (prefixWord ++ tailWord_7825386).sum := by decide
  have hdescent : baseEnd_7825386 < baseStart_7825386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825416 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_7825416 : Nat := 118140960795 + 7825416 * 2 ^ 59
def prefixEnd_7825416 : Nat := 4983230072969 + 3 ^ 40 * 7825416 * 2
def baseEnd_7825416 : Nat := 4018199729384260257611573

theorem tailTrace_7825416 : CollatzResearch.WordTrace tailWord_7825416 prefixEnd_7825416 4018199729384260257611573 := by
  unfold tailWord_7825416
  simp only [CollatzResearch.WordTrace]
  refine ⟨142708184708930890747864051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190277579611907854330485401 142708184708930890747864051)
  ·
    refine ⟨214062277063396336121796077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142708184708930890747864051 214062277063396336121796077)
    ·
      refine ⟨80273353898773626045673529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214062277063396336121796077 80273353898773626045673529)
      ·
        refine ⟨60205015424080219534255147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80273353898773626045673529 60205015424080219534255147)
        ·
          refine ⟨90307523136120329301382721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60205015424080219534255147 90307523136120329301382721)
          ·
            refine ⟨67730642352090246976037041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90307523136120329301382721 67730642352090246976037041)
            ·
              refine ⟨50797981764067685232027781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67730642352090246976037041 50797981764067685232027781)
              ·
                refine ⟨9524621580762690981005209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50797981764067685232027781 9524621580762690981005209)
                ·
                  refine ⟨7143466185572018235753907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524621580762690981005209 7143466185572018235753907)
                  ·
                    refine ⟨10715199278358027353630861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143466185572018235753907 10715199278358027353630861)
                    ·
                      refine ⟨4018199729384260257611573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715199278358027353630861 4018199729384260257611573)
                      ·
                        rfl

theorem cell23_7825416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_7825416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825416 prefixEnd_7825416 := by exact prefixLift 7825416
  have htrace : WordTrace (prefixWord ++ tailWord_7825416) baseStart_7825416 baseEnd_7825416 := by
    simpa [prefixWord, tailWord_7825416, baseEnd_7825416] using wordTrace_append hprefix tailTrace_7825416
  have hstable : (prefixWord ++ tailWord_7825416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825416).length < 2 ^ (prefixWord ++ tailWord_7825416).sum := by decide
  have hdescent : baseEnd_7825416 < baseStart_7825416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825432 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_7825432 : Nat := 118140960795 + 7825432 * 2 ^ 59
def prefixEnd_7825432 : Nat := 4983230072969 + 3 ^ 40 * 7825432 * 2
def baseEnd_7825432 : Nat := 1339402648358244065003833

theorem tailTrace_7825432 : CollatzResearch.WordTrace tailWord_7825432 prefixEnd_7825432 1339402648358244065003833 := by
  unfold tailWord_7825432
  simp only [CollatzResearch.WordTrace]
  refine ⟨142708476492901908114155275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190277968657202544152207033 142708476492901908114155275)
  ·
    refine ⟨214062714739352862171232913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142708476492901908114155275 214062714739352862171232913)
    ·
      refine ⟨160547036054514646628424685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214062714739352862171232913 160547036054514646628424685)
      ·
        refine ⟨60205138520442992485659257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160547036054514646628424685 60205138520442992485659257)
        ·
          refine ⟨45153853890332244364244443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60205138520442992485659257 45153853890332244364244443)
          ·
            refine ⟨67730780835498366546366665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45153853890332244364244443 67730780835498366546366665)
            ·
              refine ⟨50798085626623774909774999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67730780835498366546366665 50798085626623774909774999)
              ·
                refine ⟨76197128439935662364662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50798085626623774909774999 76197128439935662364662499)
                ·
                  refine ⟨114295692659903493546993749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76197128439935662364662499 114295692659903493546993749)
                  ·
                    refine ⟨1339402648358244065003833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114295692659903493546993749 1339402648358244065003833)
                    ·
                      rfl

theorem cell23_7825432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_7825432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825432 prefixEnd_7825432 := by exact prefixLift 7825432
  have htrace : WordTrace (prefixWord ++ tailWord_7825432) baseStart_7825432 baseEnd_7825432 := by
    simpa [prefixWord, tailWord_7825432, baseEnd_7825432] using wordTrace_append hprefix tailTrace_7825432
  have hstable : (prefixWord ++ tailWord_7825432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825432).length < 2 ^ (prefixWord ++ tailWord_7825432).sum := by decide
  have hdescent : baseEnd_7825432 < baseStart_7825432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825452 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_7825452 : Nat := 118140960795 + 7825452 * 2 ^ 59
def prefixEnd_7825452 : Nat := 4983230072969 + 3 ^ 40 * 7825452 * 2
def baseEnd_7825452 : Nat := 4018218214687822116761407

theorem tailTrace_7825452 : CollatzResearch.WordTrace tailWord_7825452 prefixEnd_7825452 4018218214687822116761407 := by
  unfold tailWord_7825452
  simp only [CollatzResearch.WordTrace]
  refine ⟨142708841222865679822019305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190278454963820906429359073 142708841222865679822019305)
  ·
    refine ⟨107031630917149259866514479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142708841222865679822019305 107031630917149259866514479)
    ·
      refine ⟨160547446375723889799771719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107031630917149259866514479 160547446375723889799771719)
      ·
        refine ⟨240821169563585834699657579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160547446375723889799771719 240821169563585834699657579)
        ·
          refine ⟨361231754345378752049486369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240821169563585834699657579 361231754345378752049486369)
          ·
            refine ⟨270923815759034064037114777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361231754345378752049486369 270923815759034064037114777)
            ·
              refine ⟨203192861819275548027836083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270923815759034064037114777 203192861819275548027836083)
              ·
                refine ⟨304789292728913322041754125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203192861819275548027836083 304789292728913322041754125)
                ·
                  refine ⟨114295984773342495765657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304789292728913322041754125 114295984773342495765657797)
                  ·
                    refine ⟨21430497145001717956060837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114295984773342495765657797 21430497145001717956060837)
                    ·
                      refine ⟨4018218214687822116761407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21430497145001717956060837 4018218214687822116761407)
                      ·
                        rfl

theorem cell23_7825452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_7825452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825452 prefixEnd_7825452 := by exact prefixLift 7825452
  have htrace : WordTrace (prefixWord ++ tailWord_7825452) baseStart_7825452 baseEnd_7825452 := by
    simpa [prefixWord, tailWord_7825452, baseEnd_7825452] using wordTrace_append hprefix tailTrace_7825452
  have hstable : (prefixWord ++ tailWord_7825452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825452).length < 2 ^ (prefixWord ++ tailWord_7825452).sum := by decide
  have hdescent : baseEnd_7825452 < baseStart_7825452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825456 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2]
def baseStart_7825456 : Nat := 118140960795 + 7825456 * 2 ^ 59
def prefixEnd_7825456 : Nat := 4983230072969 + 3 ^ 40 * 7825456 * 2
def baseEnd_7825456 : Nat := 4018220268610440101111389

theorem tailTrace_7825456 : CollatzResearch.WordTrace tailWord_7825456 prefixEnd_7825456 4018220268610440101111389 := by
  unfold tailWord_7825456
  simp only [CollatzResearch.WordTrace]
  refine ⟨142708914168858434163592111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190278552225144578884789481 142708914168858434163592111)
  ·
    refine ⟨214063371253287651245388167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142708914168858434163592111 214063371253287651245388167)
    ·
      refine ⟨321095056879931476868082251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214063371253287651245388167 321095056879931476868082251)
      ·
        refine ⟨481642585319897215302123377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321095056879931476868082251 481642585319897215302123377)
        ·
          refine ⟨361231938989922911476592533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481642585319897215302123377 361231938989922911476592533)
          ·
            refine ⟨16932747140152636475465275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361231938989922911476592533 16932747140152636475465275)
            ·
              refine ⟨25399120710228954713197913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932747140152636475465275 25399120710228954713197913)
              ·
                refine ⟨19049340532671716034898435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25399120710228954713197913 19049340532671716034898435)
                ·
                  refine ⟨28574010799007574052347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19049340532671716034898435 28574010799007574052347653)
                  ·
                    refine ⟨5357627024813920134815185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28574010799007574052347653 5357627024813920134815185)
                    ·
                      refine ⟨4018220268610440101111389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357627024813920134815185 4018220268610440101111389)
                      ·
                        rfl

theorem cell23_7825456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2].length) (baseStart_7825456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825456 prefixEnd_7825456 := by exact prefixLift 7825456
  have htrace : WordTrace (prefixWord ++ tailWord_7825456) baseStart_7825456 baseEnd_7825456 := by
    simpa [prefixWord, tailWord_7825456, baseEnd_7825456] using wordTrace_append hprefix tailTrace_7825456
  have hstable : (prefixWord ++ tailWord_7825456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825456).length < 2 ^ (prefixWord ++ tailWord_7825456).sum := by decide
  have hdescent : baseEnd_7825456 < baseStart_7825456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825469 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7825469 : Nat := 118140960795 + 7825469 * 2 ^ 59
def prefixEnd_7825469 : Nat := 4983230072969 + 3 ^ 40 * 7825469 * 2
def baseEnd_7825469 : Nat := 4018226943858948550248829

theorem tailTrace_7825469 : CollatzResearch.WordTrace tailWord_7825469 prefixEnd_7825469 4018226943858948550248829 := by
  unfold tailWord_7825469
  simp only [CollatzResearch.WordTrace]
  refine ⟨285418302486669771547407461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190278868324446514364938307 285418302486669771547407461)
  ·
    refine ⟨53515931716250582165138899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285418302486669771547407461 53515931716250582165138899)
    ·
      refine ⟨80273897574375873247708349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53515931716250582165138899 80273897574375873247708349)
      ·
        refine ⟨30102711590390952467890631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80273897574375873247708349 30102711590390952467890631)
        ·
          refine ⟨45154067385586428701835947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30102711590390952467890631 45154067385586428701835947)
          ·
            refine ⟨67731101078379643052753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45154067385586428701835947 67731101078379643052753921)
            ·
              refine ⟨50798325808784732289565441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67731101078379643052753921 50798325808784732289565441)
              ·
                refine ⟨38098744356588549217174081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50798325808784732289565441 38098744356588549217174081)
                ·
                  refine ⟨28574058267441411912880561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38098744356588549217174081 28574058267441411912880561)
                  ·
                    refine ⟨21430543700581058934660421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28574058267441411912880561 21430543700581058934660421)
                    ·
                      refine ⟨4018226943858948550248829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21430543700581058934660421 4018226943858948550248829)
                      ·
                        rfl

theorem cell23_7825469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7825469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825469 prefixEnd_7825469 := by exact prefixLift 7825469
  have htrace : WordTrace (prefixWord ++ tailWord_7825469) baseStart_7825469 baseEnd_7825469 := by
    simpa [prefixWord, tailWord_7825469, baseEnd_7825469] using wordTrace_append hprefix tailTrace_7825469
  have hstable : (prefixWord ++ tailWord_7825469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825469).length < 2 ^ (prefixWord ++ tailWord_7825469).sum := by decide
  have hdescent : baseEnd_7825469 < baseStart_7825469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_7825482 : Nat := 118140960795 + 7825482 * 2 ^ 59
def prefixEnd_7825482 : Nat := 4983230072969 + 3 ^ 40 * 7825482 * 2
def baseEnd_7825482 : Nat := 4018233619107456999386269

theorem tailTrace_7825482 : CollatzResearch.WordTrace tailWord_7825482 prefixEnd_7825482 4018233619107456999386269 := by
  unfold tailWord_7825482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71354694158905668691907675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190279184423748449845087133 71354694158905668691907675)
  ·
    refine ⟨107032041238358503037861513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71354694158905668691907675 107032041238358503037861513)
    ·
      refine ⟨80274030928768877278396135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107032041238358503037861513 80274030928768877278396135)
      ·
        refine ⟨120411046393153315917594203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80274030928768877278396135 120411046393153315917594203)
        ·
          refine ⟨180616569589729973876391305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120411046393153315917594203 180616569589729973876391305)
          ·
            refine ⟨135462427192297480407293479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180616569589729973876391305 135462427192297480407293479)
            ·
              refine ⟨203193640788446220610940219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135462427192297480407293479 203193640788446220610940219)
              ·
                refine ⟨304790461182669330916410329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203193640788446220610940219 304790461182669330916410329)
                ·
                  refine ⟨228592845887001998187307747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304790461182669330916410329 228592845887001998187307747)
                  ·
                    refine ⟨342889268830502997280961621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228592845887001998187307747 342889268830502997280961621)
                    ·
                      refine ⟨4018233619107456999386269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 342889268830502997280961621 4018233619107456999386269)
                      ·
                        rfl

theorem cell23_7825482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_7825482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825482 prefixEnd_7825482 := by exact prefixLift 7825482
  have htrace : WordTrace (prefixWord ++ tailWord_7825482) baseStart_7825482 baseEnd_7825482 := by
    simpa [prefixWord, tailWord_7825482, baseEnd_7825482] using wordTrace_append hprefix tailTrace_7825482
  have hstable : (prefixWord ++ tailWord_7825482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825482).length < 2 ^ (prefixWord ++ tailWord_7825482).sum := by decide
  have hdescent : baseEnd_7825482 < baseStart_7825482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825509 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_7825509 : Nat := 118140960795 + 7825509 * 2 ^ 59
def prefixEnd_7825509 : Nat := 4983230072969 + 3 ^ 40 * 7825509 * 2
def baseEnd_7825509 : Nat := 1339415827695042797916215

theorem tailTrace_7825509 : CollatzResearch.WordTrace tailWord_7825509 prefixEnd_7825509 1339415827695042797916215 := by
  unfold tailWord_7825509
  simp only [CollatzResearch.WordTrace]
  refine ⟨285419761406524858378863581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190279840937683238919242387 285419761406524858378863581)
  ·
    refine ⟨107032410527446821892073843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285419761406524858378863581 107032410527446821892073843)
    ·
      refine ⟨160548615791170232838110765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107032410527446821892073843 160548615791170232838110765)
      ·
        refine ⟨60205730921688837314291537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160548615791170232838110765 60205730921688837314291537)
        ·
          refine ⟨45154298191266627985718653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60205730921688837314291537 45154298191266627985718653)
          ·
            refine ⟨16932861821724985494644495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45154298191266627985718653 16932861821724985494644495)
            ·
              refine ⟨25399292732587478241966743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932861821724985494644495 25399292732587478241966743)
              ·
                refine ⟨38098939098881217362950115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25399292732587478241966743 38098939098881217362950115)
                ·
                  refine ⟨57148408648321826044425173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38098939098881217362950115 57148408648321826044425173)
                  ·
                    refine ⟨1339415827695042797916215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57148408648321826044425173 1339415827695042797916215)
                    ·
                      rfl

theorem cell23_7825509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_7825509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825509 prefixEnd_7825509 := by exact prefixLift 7825509
  have htrace : WordTrace (prefixWord ++ tailWord_7825509) baseStart_7825509 baseEnd_7825509 := by
    simpa [prefixWord, tailWord_7825509, baseEnd_7825509] using wordTrace_append hprefix tailTrace_7825509
  have hstable : (prefixWord ++ tailWord_7825509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825509).length < 2 ^ (prefixWord ++ tailWord_7825509).sum := by decide
  have hdescent : baseEnd_7825509 < baseStart_7825509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825569 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 8]
def baseStart_7825569 : Nat := 118140960795 + 7825569 * 2 ^ 59
def prefixEnd_7825569 : Nat := 4983230072969 + 3 ^ 40 * 7825569 * 2
def baseEnd_7825569 : Nat := 446475365769377573222041

theorem tailTrace_7825569 : CollatzResearch.WordTrace tailWord_7825569 prefixEnd_7825569 446475365769377573222041 := by
  unfold tailWord_7825569
  simp only [CollatzResearch.WordTrace]
  refine ⟨285421949786307488626047761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190281299857538325750698507 285421949786307488626047761)
  ·
    refine ⟨214066462339730616469535821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285421949786307488626047761 214066462339730616469535821)
    ·
      refine ⟨80274923377398981176075933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214066462339730616469535821 80274923377398981176075933)
      ·
        refine ⟨30103096266524617941028475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80274923377398981176075933 30103096266524617941028475)
        ·
          refine ⟨45154644399786926911542713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30103096266524617941028475 45154644399786926911542713)
          ·
            refine ⟨33865983299840195183657035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45154644399786926911542713 33865983299840195183657035)
            ·
              refine ⟨50798974949760292775485553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33865983299840195183657035 50798974949760292775485553)
              ·
                refine ⟨38099231212320219581614165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50798974949760292775485553 38099231212320219581614165)
                ·
                  refine ⟨446475365769377573222041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38099231212320219581614165 446475365769377573222041)
                  ·
                    rfl

theorem cell23_7825569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_7825569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825569 prefixEnd_7825569 := by exact prefixLift 7825569
  have htrace : WordTrace (prefixWord ++ tailWord_7825569) baseStart_7825569 baseEnd_7825569 := by
    simpa [prefixWord, tailWord_7825569, baseEnd_7825569] using wordTrace_append hprefix tailTrace_7825569
  have hstable : (prefixWord ++ tailWord_7825569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825569).length < 2 ^ (prefixWord ++ tailWord_7825569).sum := by decide
  have hdescent : baseEnd_7825569 < baseStart_7825569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825599 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 3, 5]
def baseStart_7825599 : Nat := 118140960795 + 7825599 * 2 ^ 59
def prefixEnd_7825599 : Nat := 4983230072969 + 3 ^ 40 * 7825599 * 2
def baseEnd_7825599 : Nat := 1339431232114677680541077

theorem tailTrace_7825599 : CollatzResearch.WordTrace tailWord_7825599 prefixEnd_7825599 1339431232114677680541077 := by
  unfold tailWord_7825599
  simp only [CollatzResearch.WordTrace]
  refine ⟨285423043976198803749639851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190282029317465869166426567 285423043976198803749639851)
  ·
    refine ⟨428134565964298205624459777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285423043976198803749639851 428134565964298205624459777)
    ·
      refine ⟨321100924473223654218344833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428134565964298205624459777 321100924473223654218344833)
      ·
        refine ⟨240825693354917740663758625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321100924473223654218344833 240825693354917740663758625)
        ·
          refine ⟨180619270016188305497818969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240825693354917740663758625 180619270016188305497818969)
          ·
            refine ⟨135464452512141229123364227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180619270016188305497818969 135464452512141229123364227)
            ·
              refine ⟨203196678768211843685046341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135464452512141229123364227 203196678768211843685046341)
              ·
                refine ⟨38099377269039720690946189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203196678768211843685046341 38099377269039720690946189)
                ·
                  refine ⟨14287266475889895259104821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38099377269039720690946189 14287266475889895259104821)
                  ·
                    refine ⟨1339431232114677680541077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14287266475889895259104821 1339431232114677680541077)
                    ·
                      rfl

theorem cell23_7825599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_7825599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825599 prefixEnd_7825599 := by exact prefixLift 7825599
  have htrace : WordTrace (prefixWord ++ tailWord_7825599) baseStart_7825599 baseEnd_7825599 := by
    simpa [prefixWord, tailWord_7825599, baseEnd_7825599] using wordTrace_append hprefix tailTrace_7825599
  have hstable : (prefixWord ++ tailWord_7825599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825599).length < 2 ^ (prefixWord ++ tailWord_7825599).sum := by decide
  have hdescent : baseEnd_7825599 < baseStart_7825599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825633 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_7825633 : Nat := 118140960795 + 7825633 * 2 ^ 59
def prefixEnd_7825633 : Nat := 4983230072969 + 3 ^ 40 * 7825633 * 2
def baseEnd_7825633 : Nat := 1339437051562095302866025

theorem tailTrace_7825633 : CollatzResearch.WordTrace tailWord_7825633 prefixEnd_7825633 1339437051562095302866025 := by
  unfold tailWord_7825633
  simp only [CollatzResearch.WordTrace]
  refine ⟨285424284058075627556377553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190282856038717085037585035 285424284058075627556377553)
  ·
    refine ⟨214068213043556720667283165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285424284058075627556377553 214068213043556720667283165)
    ·
      refine ⟨80275579891333770250231187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214068213043556720667283165 80275579891333770250231187)
      ·
        refine ⟨120413369837000655375346781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80275579891333770250231187 120413369837000655375346781)
        ·
          refine ⟨45155013688875245765755043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120413369837000655375346781 45155013688875245765755043)
          ·
            refine ⟨67732520533312868648632565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45155013688875245765755043 67732520533312868648632565)
            ·
              refine ⟨6349923799998081435809303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67732520533312868648632565 6349923799998081435809303)
              ·
                refine ⟨9524885699997122153713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349923799998081435809303 9524885699997122153713955)
                ·
                  refine ⟨14287328549995683230570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524885699997122153713955 14287328549995683230570933)
                  ·
                    refine ⟨1339437051562095302866025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14287328549995683230570933 1339437051562095302866025)
                    ·
                      rfl

theorem cell23_7825633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_7825633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825633 prefixEnd_7825633 := by exact prefixLift 7825633
  have htrace : WordTrace (prefixWord ++ tailWord_7825633) baseStart_7825633 baseEnd_7825633 := by
    simpa [prefixWord, tailWord_7825633, baseEnd_7825633] using wordTrace_append hprefix tailTrace_7825633
  have hstable : (prefixWord ++ tailWord_7825633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825633).length < 2 ^ (prefixWord ++ tailWord_7825633).sum := by decide
  have hdescent : baseEnd_7825633 < baseStart_7825633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825647 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 1, 1, 3]
def baseStart_7825647 : Nat := 118140960795 + 7825647 * 2 ^ 59
def prefixEnd_7825647 : Nat := 4983230072969 + 3 ^ 40 * 7825647 * 2
def baseEnd_7825647 : Nat := 4018318343415448853823011

theorem tailTrace_7825647 : CollatzResearch.WordTrace tailWord_7825647 prefixEnd_7825647 4018318343415448853823011 := by
  unfold tailWord_7825647
  simp only [CollatzResearch.WordTrace]
  refine ⟨285424794680024907947387195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190283196453349938631591463 285424794680024907947387195)
  ·
    refine ⟨428137192020037361921080793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285424794680024907947387195 428137192020037361921080793)
    ·
      refine ⟨321102894015028021440810595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428137192020037361921080793 321102894015028021440810595)
      ·
        refine ⟨481654341022542032161215893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321102894015028021440810595 481654341022542032161215893)
        ·
          refine ⟨22577547235431657757556995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 481654341022542032161215893 22577547235431657757556995)
          ·
            refine ⟨33866320853147486636335493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22577547235431657757556995 33866320853147486636335493)
            ·
              refine ⟨6349935159965153744312905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33866320853147486636335493 6349935159965153744312905)
              ·
                refine ⟨4762451369973865308234679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349935159965153744312905 4762451369973865308234679)
                ·
                  refine ⟨7143677054960797962352019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762451369973865308234679 7143677054960797962352019)
                  ·
                    refine ⟨10715515582441196943528029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143677054960797962352019 10715515582441196943528029)
                    ·
                      refine ⟨4018318343415448853823011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715515582441196943528029 4018318343415448853823011)
                      ·
                        rfl

theorem cell23_7825647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 1, 3].length) (baseStart_7825647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825647 prefixEnd_7825647 := by exact prefixLift 7825647
  have htrace : WordTrace (prefixWord ++ tailWord_7825647) baseStart_7825647 baseEnd_7825647 := by
    simpa [prefixWord, tailWord_7825647, baseEnd_7825647] using wordTrace_append hprefix tailTrace_7825647
  have hstable : (prefixWord ++ tailWord_7825647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825647).length < 2 ^ (prefixWord ++ tailWord_7825647).sum := by decide
  have hdescent : baseEnd_7825647 < baseStart_7825647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825649 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_7825649 : Nat := 118140960795 + 7825649 * 2 ^ 59
def prefixEnd_7825649 : Nat := 4983230072969 + 3 ^ 40 * 7825649 * 2
def baseEnd_7825649 : Nat := 4018319370376757845998001

theorem tailTrace_7825649 : CollatzResearch.WordTrace tailWord_7825649 prefixEnd_7825649 4018319370376757845998001 := by
  unfold tailWord_7825649
  simp only [CollatzResearch.WordTrace]
  refine ⟨285424867626017662288960001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190283245084011774859306667 285424867626017662288960001)
  ·
    refine ⟨214068650719513246716720001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285424867626017662288960001 214068650719513246716720001)
    ·
      refine ⟨160551488039634935037540001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214068650719513246716720001 160551488039634935037540001)
      ·
        refine ⟨120413616029726201278155001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160551488039634935037540001 120413616029726201278155001)
        ·
          refine ⟨90310212022294650958616251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120413616029726201278155001 90310212022294650958616251)
          ·
            refine ⟨135465318033441976437924377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90310212022294650958616251 135465318033441976437924377)
            ·
              refine ⟨101598988525081482328443283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135465318033441976437924377 101598988525081482328443283)
              ·
                refine ⟨152398482787622223492664925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101598988525081482328443283 152398482787622223492664925)
                ·
                  refine ⟨57149431045358333809749347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152398482787622223492664925 57149431045358333809749347)
                  ·
                    refine ⟨85724146568037500714624021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57149431045358333809749347 85724146568037500714624021)
                    ·
                      refine ⟨4018319370376757845998001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85724146568037500714624021 4018319370376757845998001)
                      ·
                        rfl

theorem cell23_7825649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_7825649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825649 prefixEnd_7825649 := by exact prefixLift 7825649
  have htrace : WordTrace (prefixWord ++ tailWord_7825649) baseStart_7825649 baseEnd_7825649 := by
    simpa [prefixWord, tailWord_7825649, baseEnd_7825649] using wordTrace_append hprefix tailTrace_7825649
  have hstable : (prefixWord ++ tailWord_7825649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825649).length < 2 ^ (prefixWord ++ tailWord_7825649).sum := by decide
  have hdescent : baseEnd_7825649 < baseStart_7825649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825676 : List Nat := [2, 2, 1, 2, 2, 2, 5, 7]
def baseStart_7825676 : Nat := 118140960795 + 7825676 * 2 ^ 59
def prefixEnd_7825676 : Nat := 4983230072969 + 3 ^ 40 * 7825676 * 2
def baseEnd_7825676 : Nat := 148827156827941823717051

theorem tailTrace_7825676 : CollatzResearch.WordTrace tailWord_7825676 prefixEnd_7825676 148827156827941823717051 := by
  unfold tailWord_7825676
  simp only [CollatzResearch.WordTrace]
  refine ⟨142712926198459922950096441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190283901597946563933461921 142712926198459922950096441)
  ·
    refine ⟨107034694648844942212572331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142712926198459922950096441 107034694648844942212572331)
    ·
      refine ⟨160552041973267413318858497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107034694648844942212572331 160552041973267413318858497)
      ·
        refine ⟨120414031479950559989143873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160552041973267413318858497 120414031479950559989143873)
        ·
          refine ⟨90310523609962919991857905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120414031479950559989143873 90310523609962919991857905)
          ·
            refine ⟨67732892707472189993893429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90310523609962919991857905 67732892707472189993893429)
            ·
              refine ⟨6349958691325517811927509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67732892707472189993893429 6349958691325517811927509)
              ·
                refine ⟨148827156827941823717051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6349958691325517811927509 148827156827941823717051)
                ·
                  rfl

theorem cell23_7825676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 7].length) (baseStart_7825676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825676 prefixEnd_7825676 := by exact prefixLift 7825676
  have htrace : WordTrace (prefixWord ++ tailWord_7825676) baseStart_7825676 baseEnd_7825676 := by
    simpa [prefixWord, tailWord_7825676, baseEnd_7825676] using wordTrace_append hprefix tailTrace_7825676
  have hstable : (prefixWord ++ tailWord_7825676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825676).length < 2 ^ (prefixWord ++ tailWord_7825676).sum := by decide
  have hdescent : baseEnd_7825676 < baseStart_7825676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825687 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7825687 : Nat := 118140960795 + 7825687 * 2 ^ 59
def prefixEnd_7825687 : Nat := 4983230072969 + 3 ^ 40 * 7825687 * 2
def baseEnd_7825687 : Nat := 4018338882641628697322827

theorem tailTrace_7825687 : CollatzResearch.WordTrace tailWord_7825687 prefixEnd_7825687 4018338882641628697322827 := by
  unfold tailWord_7825687
  simp only [CollatzResearch.WordTrace]
  refine ⟨285426253599879994778843315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190284169066586663185895543 285426253599879994778843315)
  ·
    refine ⟨428139380399819992168264973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285426253599879994778843315 428139380399819992168264973)
    ·
      refine ⟨160552267649932497063099365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428139380399819992168264973 160552267649932497063099365)
      ·
        refine ⟨30103550184362343199331131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160552267649932497063099365 30103550184362343199331131)
        ·
          refine ⟨45155325276543514798996697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30103550184362343199331131 45155325276543514798996697)
          ·
            refine ⟨33866493957407636099247523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45155325276543514798996697 33866493957407636099247523)
            ·
              refine ⟨50799740936111454148871285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33866493957407636099247523 50799740936111454148871285)
              ·
                refine ⟨4762475712760448826456683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50799740936111454148871285 4762475712760448826456683)
                ·
                  refine ⟨7143713569140673239685025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762475712760448826456683 7143713569140673239685025)
                  ·
                    refine ⟨5357785176855504929763769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143713569140673239685025 5357785176855504929763769)
                    ·
                      refine ⟨4018338882641628697322827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357785176855504929763769 4018338882641628697322827)
                      ·
                        rfl

theorem cell23_7825687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7825687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825687 prefixEnd_7825687 := by exact prefixLift 7825687
  have htrace : WordTrace (prefixWord ++ tailWord_7825687) baseStart_7825687 baseEnd_7825687 := by
    simpa [prefixWord, tailWord_7825687, baseEnd_7825687] using wordTrace_append hprefix tailTrace_7825687
  have hstable : (prefixWord ++ tailWord_7825687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825687).length < 2 ^ (prefixWord ++ tailWord_7825687).sum := by decide
  have hdescent : baseEnd_7825687 < baseStart_7825687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825690 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_7825690 : Nat := 118140960795 + 7825690 * 2 ^ 59
def prefixEnd_7825690 : Nat := 4983230072969 + 3 ^ 40 * 7825690 * 2
def baseEnd_7825690 : Nat := 4018340423083592185585313

theorem tailTrace_7825690 : CollatzResearch.WordTrace tailWord_7825690 prefixEnd_7825690 4018340423083592185585313 := by
  unfold tailWord_7825690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71356590754717281572800631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190284242012579417527468349 71356590754717281572800631)
  ·
    refine ⟨107034886132075922359200947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71356590754717281572800631 107034886132075922359200947)
    ·
      refine ⟨160552329198113883538801421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107034886132075922359200947 160552329198113883538801421)
      ·
        refine ⟨60207123449292706327050533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160552329198113883538801421 60207123449292706327050533)
        ·
          refine ⟨11288835646742382436321975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60207123449292706327050533 11288835646742382436321975)
          ·
            refine ⟨16933253470113573654482963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288835646742382436321975 16933253470113573654482963)
            ·
              refine ⟨25399880205170360481724445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16933253470113573654482963 25399880205170360481724445)
              ·
                refine ⟨9524955076938885180646667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25399880205170360481724445 9524955076938885180646667)
                ·
                  refine ⟨14287432615408327770970001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524955076938885180646667 14287432615408327770970001)
                  ·
                    refine ⟨10715574461556245828227501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14287432615408327770970001 10715574461556245828227501)
                    ·
                      refine ⟨4018340423083592185585313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715574461556245828227501 4018340423083592185585313)
                      ·
                        rfl

theorem cell23_7825690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_7825690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825690 prefixEnd_7825690 := by exact prefixLift 7825690
  have htrace : WordTrace (prefixWord ++ tailWord_7825690) baseStart_7825690 baseEnd_7825690 := by
    simpa [prefixWord, tailWord_7825690, baseEnd_7825690] using wordTrace_append hprefix tailTrace_7825690
  have hstable : (prefixWord ++ tailWord_7825690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825690).length < 2 ^ (prefixWord ++ tailWord_7825690).sum := by decide
  have hdescent : baseEnd_7825690 < baseStart_7825690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825746 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_7825746 : Nat := 118140960795 + 7825746 * 2 ^ 59
def prefixEnd_7825746 : Nat := 4983230072969 + 3 ^ 40 * 7825746 * 2
def baseEnd_7825746 : Nat := 4018369178000243966485055

theorem tailTrace_7825746 : CollatzResearch.WordTrace tailWord_7825746 prefixEnd_7825746 4018369178000243966485055 := by
  unfold tailWord_7825746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71357101376666561963810273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190285603671110831903494061 71357101376666561963810273)
  ·
    refine ⟨53517826032499921472857705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71357101376666561963810273 53517826032499921472857705)
    ·
      refine ⟨40138369524374941104643279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53517826032499921472857705 40138369524374941104643279)
      ·
        refine ⟨60207554286562411656964919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40138369524374941104643279 60207554286562411656964919)
        ·
          refine ⟨90311331429843617485447379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60207554286562411656964919 90311331429843617485447379)
          ·
            refine ⟨135466997144765426228171069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90311331429843617485447379 135466997144765426228171069)
            ·
              refine ⟨50800123929287034835564151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135466997144765426228171069 50800123929287034835564151)
              ·
                refine ⟨76200185893930552253346227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50800123929287034835564151 76200185893930552253346227)
                ·
                  refine ⟨114300278840895828380019341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76200185893930552253346227 114300278840895828380019341)
                  ·
                    refine ⟨42862604565335935642507253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114300278840895828380019341 42862604565335935642507253)
                    ·
                      refine ⟨4018369178000243966485055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42862604565335935642507253 4018369178000243966485055)
                      ·
                        rfl

theorem cell23_7825746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_7825746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825746 prefixEnd_7825746 := by exact prefixLift 7825746
  have htrace : WordTrace (prefixWord ++ tailWord_7825746) baseStart_7825746 baseEnd_7825746 := by
    simpa [prefixWord, tailWord_7825746, baseEnd_7825746] using wordTrace_append hprefix tailTrace_7825746
  have hstable : (prefixWord ++ tailWord_7825746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825746).length < 2 ^ (prefixWord ++ tailWord_7825746).sum := by decide
  have hdescent : baseEnd_7825746 < baseStart_7825746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825794 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7825794 : Nat := 118140960795 + 7825794 * 2 ^ 59
def prefixEnd_7825794 : Nat := 4983230072969 + 3 ^ 40 * 7825794 * 2
def baseEnd_7825794 : Nat := 4018393825071659778684835

theorem tailTrace_7825794 : CollatzResearch.WordTrace tailWord_7825794 prefixEnd_7825794 4018393825071659778684835 := by
  unfold tailWord_7825794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71357539052623088013247109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190286770806994901368658957 71357539052623088013247109)
  ·
    refine ⟨13379538572366829002483833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71357539052623088013247109 13379538572366829002483833)
    ·
      refine ⟨10034653929275121751862875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13379538572366829002483833 10034653929275121751862875)
      ·
        refine ⟨15051980893912682627794313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034653929275121751862875 15051980893912682627794313)
        ·
          refine ⟨11288985670434511970845735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15051980893912682627794313 11288985670434511970845735)
          ·
            refine ⟨16933478505651767956268603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288985670434511970845735 16933478505651767956268603)
            ·
              refine ⟨25400217758477651934402905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16933478505651767956268603 25400217758477651934402905)
              ·
                refine ⟨19050163318858238950802179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25400217758477651934402905 19050163318858238950802179)
                ·
                  refine ⟨28575244978287358426203269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19050163318858238950802179 28575244978287358426203269)
                  ·
                    refine ⟨5357858433428879704913113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28575244978287358426203269 5357858433428879704913113)
                    ·
                      refine ⟨4018393825071659778684835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357858433428879704913113 4018393825071659778684835)
                      ·
                        rfl

theorem cell23_7825794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7825794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825794 prefixEnd_7825794 := by exact prefixLift 7825794
  have htrace : WordTrace (prefixWord ++ tailWord_7825794) baseStart_7825794 baseEnd_7825794 := by
    simpa [prefixWord, tailWord_7825794, baseEnd_7825794] using wordTrace_append hprefix tailTrace_7825794
  have hstable : (prefixWord ++ tailWord_7825794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825794).length < 2 ^ (prefixWord ++ tailWord_7825794).sum := by decide
  have hdescent : baseEnd_7825794 < baseStart_7825794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825856 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 8]
def baseStart_7825856 : Nat := 118140960795 + 7825856 * 2 ^ 59
def prefixEnd_7825856 : Nat := 4983230072969 + 3 ^ 40 * 7825856 * 2
def baseEnd_7825856 : Nat := 446491740096915392901061

theorem tailTrace_7825856 : CollatzResearch.WordTrace tailWord_7825856 prefixEnd_7825856 446491740096915392901061 := by
  unfold tailWord_7825856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142716208768133868320872711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190288278357511824427830281 142716208768133868320872711)
  ·
    refine ⟨214074313152200802481309067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142716208768133868320872711 214074313152200802481309067)
    ·
      refine ⟨321111469728301203721963601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214074313152200802481309067 321111469728301203721963601)
      ·
        refine ⟨240833602296225902791472701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321111469728301203721963601 240833602296225902791472701)
        ·
          refine ⟨90312600861084713546802263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240833602296225902791472701 90312600861084713546802263)
          ·
            refine ⟨135468901291627070320203395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90312600861084713546802263 135468901291627070320203395)
            ·
              refine ⟨203203351937440605480305093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135468901291627070320203395 203203351937440605480305093)
              ·
                refine ⟨38100628488270113527557205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203203351937440605480305093 38100628488270113527557205)
                ·
                  refine ⟨446491740096915392901061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38100628488270113527557205 446491740096915392901061)
                  ·
                    rfl

theorem cell23_7825856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_7825856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825856 prefixEnd_7825856 := by exact prefixLift 7825856
  have htrace : WordTrace (prefixWord ++ tailWord_7825856) baseStart_7825856 baseEnd_7825856 := by
    simpa [prefixWord, tailWord_7825856, baseEnd_7825856] using wordTrace_append hprefix tailTrace_7825856
  have hstable : (prefixWord ++ tailWord_7825856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825856).length < 2 ^ (prefixWord ++ tailWord_7825856).sum := by decide
  have hdescent : baseEnd_7825856 < baseStart_7825856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825877 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_7825877 : Nat := 118140960795 + 7825877 * 2 ^ 59
def prefixEnd_7825877 : Nat := 4983230072969 + 3 ^ 40 * 7825877 * 2
def baseEnd_7825877 : Nat := 1339478814655327651315651

theorem tailTrace_7825877 : CollatzResearch.WordTrace tailWord_7825877 prefixEnd_7825877 1339478814655327651315651 := by
  unfold tailWord_7825877
  simp only [CollatzResearch.WordTrace]
  refine ⟨285433183469191657228259885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190288788979461104818839923 285433183469191657228259885)
  ·
    refine ⟨107037443800946871460597457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285433183469191657228259885 107037443800946871460597457)
    ·
      refine ⟨80278082850710153595448093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107037443800946871460597457 80278082850710153595448093)
      ·
        refine ⟨30104281069016307598293035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80278082850710153595448093 30104281069016307598293035)
        ·
          refine ⟨45156421603524461397439553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30104281069016307598293035 45156421603524461397439553)
          ·
            refine ⟨33867316202643346048079665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45156421603524461397439553 33867316202643346048079665)
            ·
              refine ⟨25400487151982509536059749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33867316202643346048079665 25400487151982509536059749)
              ·
                refine ⟨4762591340996720538011203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25400487151982509536059749 4762591340996720538011203)
                ·
                  refine ⟨7143887011495080807016805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762591340996720538011203 7143887011495080807016805)
                  ·
                    refine ⟨1339478814655327651315651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7143887011495080807016805 1339478814655327651315651)
                    ·
                      rfl

theorem cell23_7825877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_7825877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825877 prefixEnd_7825877 := by exact prefixLift 7825877
  have htrace : WordTrace (prefixWord ++ tailWord_7825877) baseStart_7825877 baseEnd_7825877 := by
    simpa [prefixWord, tailWord_7825877, baseEnd_7825877] using wordTrace_append hprefix tailTrace_7825877
  have hstable : (prefixWord ++ tailWord_7825877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825877).length < 2 ^ (prefixWord ++ tailWord_7825877).sum := by decide
  have hdescent : baseEnd_7825877 < baseStart_7825877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825900 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_7825900 : Nat := 118140960795 + 7825900 * 2 ^ 59
def prefixEnd_7825900 : Nat := 4983230072969 + 3 ^ 40 * 7825900 * 2
def baseEnd_7825900 : Nat := 4018448254021036363959347

theorem tailTrace_7825900 : CollatzResearch.WordTrace tailWord_7825900 prefixEnd_7825900 4018448254021036363959347 := by
  unfold tailWord_7825900
  simp only [CollatzResearch.WordTrace]
  refine ⟨142717011174054166078173577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190289348232072221437564769 142717011174054166078173577)
  ·
    refine ⟨107037758380540624558630183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142717011174054166078173577 107037758380540624558630183)
    ·
      refine ⟨160556637570810936837945275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107037758380540624558630183 160556637570810936837945275)
      ·
        refine ⟨240834956356216405256917913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160556637570810936837945275 240834956356216405256917913)
        ·
          refine ⟨180626217267162303942688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240834956356216405256917913 180626217267162303942688435)
          ·
            refine ⟨270939325900743455914032653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180626217267162303942688435 270939325900743455914032653)
            ·
              refine ⟨101602247212778795967762245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270939325900743455914032653 101602247212778795967762245)
              ·
                refine ⟨19050421352396024243955421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101602247212778795967762245 19050421352396024243955421)
                ·
                  refine ⟨7143908007148509091483283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19050421352396024243955421 7143908007148509091483283)
                  ·
                    refine ⟨10715862010722763637224925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143908007148509091483283 10715862010722763637224925)
                    ·
                      refine ⟨4018448254021036363959347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715862010722763637224925 4018448254021036363959347)
                      ·
                        rfl

theorem cell23_7825900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_7825900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825900 prefixEnd_7825900 := by exact prefixLift 7825900
  have htrace : WordTrace (prefixWord ++ tailWord_7825900) baseStart_7825900 baseEnd_7825900 := by
    simpa [prefixWord, tailWord_7825900, baseEnd_7825900] using wordTrace_append hprefix tailTrace_7825900
  have hstable : (prefixWord ++ tailWord_7825900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825900).length < 2 ^ (prefixWord ++ tailWord_7825900).sum := by decide
  have hdescent : baseEnd_7825900 < baseStart_7825900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825934 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7825934 : Nat := 118140960795 + 7825934 * 2 ^ 59
def prefixEnd_7825934 : Nat := 4983230072969 + 3 ^ 40 * 7825934 * 2
def baseEnd_7825934 : Nat := 4018465712363289230934191

theorem tailTrace_7825934 : CollatzResearch.WordTrace tailWord_7825934 prefixEnd_7825934 4018465712363289230934191 := by
  unfold tailWord_7825934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35679407803748144495385607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190290174953323437308723237 35679407803748144495385607)
  ·
    refine ⟨53519111705622216743078411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35679407803748144495385607 53519111705622216743078411)
    ·
      refine ⟨80278667558433325114617617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53519111705622216743078411 80278667558433325114617617)
      ·
        refine ⟨60209000668824993835963213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80278667558433325114617617 60209000668824993835963213)
        ·
          refine ⟨22578375250809372688486205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60209000668824993835963213 22578375250809372688486205)
          ·
            refine ⟨8466890719053514758182327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22578375250809372688486205 8466890719053514758182327)
            ·
              refine ⟨12700336078580272137273491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8466890719053514758182327 12700336078580272137273491)
              ·
                refine ⟨19050504117870408205910237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12700336078580272137273491 19050504117870408205910237)
                ·
                  refine ⟨7143939044201403077216339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19050504117870408205910237 7143939044201403077216339)
                  ·
                    refine ⟨10715908566302104615824509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143939044201403077216339 10715908566302104615824509)
                    ·
                      refine ⟨4018465712363289230934191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10715908566302104615824509 4018465712363289230934191)
                      ·
                        rfl

theorem cell23_7825934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7825934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825934 prefixEnd_7825934 := by exact prefixLift 7825934
  have htrace : WordTrace (prefixWord ++ tailWord_7825934) baseStart_7825934 baseEnd_7825934 := by
    simpa [prefixWord, tailWord_7825934, baseEnd_7825934] using wordTrace_append hprefix tailTrace_7825934
  have hstable : (prefixWord ++ tailWord_7825934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825934).length < 2 ^ (prefixWord ++ tailWord_7825934).sum := by decide
  have hdescent : baseEnd_7825934 < baseStart_7825934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825953 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7825953 : Nat := 118140960795 + 7825953 * 2 ^ 59
def prefixEnd_7825953 : Nat := 4983230072969 + 3 ^ 40 * 7825953 * 2
def baseEnd_7825953 : Nat := 4018475468495724656596603

theorem tailTrace_7825953 : CollatzResearch.WordTrace tailWord_7825953 prefixEnd_7825953 4018475468495724656596603 := by
  unfold tailWord_7825953
  simp only [CollatzResearch.WordTrace]
  refine ⟨285435955416916322208026513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190290636944610881472017675 285435955416916322208026513)
  ·
    refine ⟨214076966562687241656019885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285435955416916322208026513 214076966562687241656019885)
    ·
      refine ⟨80278862461007715621007457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214076966562687241656019885 80278862461007715621007457)
      ·
        refine ⟨60209146845755786715755593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80278862461007715621007457 60209146845755786715755593)
        ·
          refine ⟨45156860134316840036816695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60209146845755786715755593 45156860134316840036816695)
          ·
            refine ⟨67735290201475260055225043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45156860134316840036816695 67735290201475260055225043)
            ·
              refine ⟨101602935302212890082837565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67735290201475260055225043 101602935302212890082837565)
              ·
                refine ⟨38101100738329833781064087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101602935302212890082837565 38101100738329833781064087)
                ·
                  refine ⟨57151651107494750671596131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38101100738329833781064087 57151651107494750671596131)
                  ·
                    refine ⟨85727476661242126007394197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57151651107494750671596131 85727476661242126007394197)
                    ·
                      refine ⟨4018475468495724656596603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85727476661242126007394197 4018475468495724656596603)
                      ·
                        rfl

theorem cell23_7825953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7825953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825953 prefixEnd_7825953 := by exact prefixLift 7825953
  have htrace : WordTrace (prefixWord ++ tailWord_7825953) baseStart_7825953 baseEnd_7825953 := by
    simpa [prefixWord, tailWord_7825953, baseEnd_7825953] using wordTrace_append hprefix tailTrace_7825953
  have hstable : (prefixWord ++ tailWord_7825953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825953).length < 2 ^ (prefixWord ++ tailWord_7825953).sum := by decide
  have hdescent : baseEnd_7825953 < baseStart_7825953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825957 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_7825957 : Nat := 118140960795 + 7825957 * 2 ^ 59
def prefixEnd_7825957 : Nat := 4983230072969 + 3 ^ 40 * 7825957 * 2
def baseEnd_7825957 : Nat := 4018477522418342640946585

theorem tailTrace_7825957 : CollatzResearch.WordTrace tailWord_7825957 prefixEnd_7825957 4018477522418342640946585 := by
  unfold tailWord_7825957
  simp only [CollatzResearch.WordTrace]
  refine ⟨285436101308901830891172125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190290734205934553927448083 285436101308901830891172125)
  ·
    refine ⟨107038537990838186584189547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285436101308901830891172125 107038537990838186584189547)
    ·
      refine ⟨160557806986257279876284321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107038537990838186584189547 160557806986257279876284321)
      ·
        refine ⟨120418355239692959907213241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160557806986257279876284321 120418355239692959907213241)
        ·
          refine ⟨90313766429769719930409931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120418355239692959907213241 90313766429769719930409931)
          ·
            refine ⟨135470649644654579895614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90313766429769719930409931 135470649644654579895614897)
            ·
              refine ⟨101602987233490934921711173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135470649644654579895614897 101602987233490934921711173)
              ·
                refine ⟨19050560106279550297820845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101602987233490934921711173 19050560106279550297820845)
                ·
                  refine ⟨7143960039854831361682817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19050560106279550297820845 7143960039854831361682817)
                  ·
                    refine ⟨5357970029891123521262113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143960039854831361682817 5357970029891123521262113)
                    ·
                      refine ⟨4018477522418342640946585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357970029891123521262113 4018477522418342640946585)
                      ·
                        rfl

theorem cell23_7825957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_7825957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825957 prefixEnd_7825957 := by exact prefixLift 7825957
  have htrace : WordTrace (prefixWord ++ tailWord_7825957) baseStart_7825957 baseEnd_7825957 := by
    simpa [prefixWord, tailWord_7825957, baseEnd_7825957] using wordTrace_append hprefix tailTrace_7825957
  have hstable : (prefixWord ++ tailWord_7825957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825957).length < 2 ^ (prefixWord ++ tailWord_7825957).sum := by decide
  have hdescent : baseEnd_7825957 < baseStart_7825957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825991 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_7825991 : Nat := 118140960795 + 7825991 * 2 ^ 59
def prefixEnd_7825991 : Nat := 4983230072969 + 3 ^ 40 * 7825991 * 2
def baseEnd_7825991 : Nat := 4018494980760595507921429

theorem tailTrace_7825991 : CollatzResearch.WordTrace tailWord_7825991 prefixEnd_7825991 4018494980760595507921429 := by
  unfold tailWord_7825991
  simp only [CollatzResearch.WordTrace]
  refine ⟨285437341390778654697909827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190291560927185769798606551 285437341390778654697909827)
  ·
    refine ⟨428156012086167982046864741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285437341390778654697909827 428156012086167982046864741)
    ·
      refine ⟨80279252266156496633787139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428156012086167982046864741 80279252266156496633787139)
      ·
        refine ⟨120418878399234744950680709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80279252266156496633787139 120418878399234744950680709)
        ·
          refine ⟨22578539699856514678252633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120418878399234744950680709 22578539699856514678252633)
          ·
            refine ⟨16933904774892386008689475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22578539699856514678252633 16933904774892386008689475)
            ·
              refine ⟨25400857162338579013034213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16933904774892386008689475 25400857162338579013034213)
              ·
                refine ⟨4762660717938483564943915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25400857162338579013034213 4762660717938483564943915)
                ·
                  refine ⟨7143991076907725347415873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762660717938483564943915 7143991076907725347415873)
                  ·
                    refine ⟨5357993307680794010561905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143991076907725347415873 5357993307680794010561905)
                    ·
                      refine ⟨4018494980760595507921429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357993307680794010561905 4018494980760595507921429)
                      ·
                        rfl

theorem cell23_7825991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_7825991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825991 prefixEnd_7825991 := by exact prefixLift 7825991
  have htrace : WordTrace (prefixWord ++ tailWord_7825991) baseStart_7825991 baseEnd_7825991 := by
    simpa [prefixWord, tailWord_7825991, baseEnd_7825991] using wordTrace_append hprefix tailTrace_7825991
  have hstable : (prefixWord ++ tailWord_7825991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825991).length < 2 ^ (prefixWord ++ tailWord_7825991).sum := by decide
  have hdescent : baseEnd_7825991 < baseStart_7825991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7825997 : List Nat := [1, 6, 1, 1, 2, 3, 1, 8]
def baseStart_7825997 : Nat := 118140960795 + 7825997 * 2 ^ 59
def prefixEnd_7825997 : Nat := 4983230072969 + 3 ^ 40 * 7825997 * 2
def baseEnd_7825997 : Nat := 148833261542389721646163

theorem tailTrace_7825997 : CollatzResearch.WordTrace tailWord_7825997 prefixEnd_7825997 148833261542389721646163 := by
  unfold tailWord_7825997
  simp only [CollatzResearch.WordTrace]
  refine ⟨285437560228756917722628245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190291706819171278481752163 285437560228756917722628245)
  ·
    refine ⟨13379885635722980518248199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285437560228756917722628245 13379885635722980518248199)
    ·
      refine ⟨20069828453584470777372299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13379885635722980518248199 20069828453584470777372299)
      ·
        refine ⟨30104742680376706166058449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20069828453584470777372299 30104742680376706166058449)
        ·
          refine ⟨22578557010282529624543837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30104742680376706166058449 22578557010282529624543837)
          ·
            refine ⟨8466958878855948609203939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22578557010282529624543837 8466958878855948609203939)
            ·
              refine ⟨12700438318283922913805909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8466958878855948609203939 12700438318283922913805909)
              ·
                refine ⟨148833261542389721646163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12700438318283922913805909 148833261542389721646163)
                ·
                  rfl

theorem cell23_7825997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 8].length) (baseStart_7825997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7825997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7825997 prefixEnd_7825997 := by exact prefixLift 7825997
  have htrace : WordTrace (prefixWord ++ tailWord_7825997) baseStart_7825997 baseEnd_7825997 := by
    simpa [prefixWord, tailWord_7825997, baseEnd_7825997] using wordTrace_append hprefix tailTrace_7825997
  have hstable : (prefixWord ++ tailWord_7825997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7825997).length < 2 ^ (prefixWord ++ tailWord_7825997).sum := by decide
  have hdescent : baseEnd_7825997 < baseStart_7825997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7825997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826007 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_7826007 : Nat := 118140960795 + 7826007 * 2 ^ 59
def prefixEnd_7826007 : Nat := 4983230072969 + 3 ^ 40 * 7826007 * 2
def baseEnd_7826007 : Nat := 4018503196451067445321355

theorem tailTrace_7826007 : CollatzResearch.WordTrace tailWord_7826007 prefixEnd_7826007 4018503196451067445321355 := by
  unfold tailWord_7826007
  simp only [CollatzResearch.WordTrace]
  refine ⟨285437924958720689430492275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190291949972480459620328183 285437924958720689430492275)
  ·
    refine ⟨428156887438081034145738413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285437924958720689430492275 428156887438081034145738413)
    ·
      refine ⟨160558832789280387804651905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428156887438081034145738413 160558832789280387804651905)
      ·
        refine ⟨120419124591960290853488929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160558832789280387804651905 120419124591960290853488929)
        ·
          refine ⟨90314343443970218140116697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120419124591960290853488929 90314343443970218140116697)
          ·
            refine ⟨67735757582977663605087523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90314343443970218140116697 67735757582977663605087523)
            ·
              refine ⟨101603636374466495407631285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67735757582977663605087523 101603636374466495407631285)
              ·
                refine ⟨9525340910106233944465433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101603636374466495407631285 9525340910106233944465433)
                ·
                  refine ⟨7144005682579675458349075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9525340910106233944465433 7144005682579675458349075)
                  ·
                    refine ⟨10716008523869513187523613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7144005682579675458349075 10716008523869513187523613)
                    ·
                      refine ⟨4018503196451067445321355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10716008523869513187523613 4018503196451067445321355)
                      ·
                        rfl

theorem cell23_7826007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_7826007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826007 prefixEnd_7826007 := by exact prefixLift 7826007
  have htrace : WordTrace (prefixWord ++ tailWord_7826007) baseStart_7826007 baseEnd_7826007 := by
    simpa [prefixWord, tailWord_7826007, baseEnd_7826007] using wordTrace_append hprefix tailTrace_7826007
  have hstable : (prefixWord ++ tailWord_7826007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826007).length < 2 ^ (prefixWord ++ tailWord_7826007).sum := by decide
  have hdescent : baseEnd_7826007 < baseStart_7826007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826017 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_7826017 : Nat := 118140960795 + 7826017 * 2 ^ 59
def prefixEnd_7826017 : Nat := 4983230072969 + 3 ^ 40 * 7826017 * 2
def baseEnd_7826017 : Nat := 4018508331257612406196309

theorem tailTrace_7826017 : CollatzResearch.WordTrace tailWord_7826017 prefixEnd_7826017 4018508331257612406196309 := by
  unfold tailWord_7826017
  simp only [CollatzResearch.WordTrace]
  refine ⟨285438289688684461138356305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190292193125789640758904203 285438289688684461138356305)
  ·
    refine ⟨214078717266513345853767229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285438289688684461138356305 214078717266513345853767229)
    ·
      refine ⟨80279518974942504695162711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214078717266513345853767229 80279518974942504695162711)
      ·
        refine ⟨120419278462413757042744067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80279518974942504695162711 120419278462413757042744067)
        ·
          refine ⟨180628917693620635564116101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120419278462413757042744067 180628917693620635564116101)
          ·
            refine ⟨33867922067553869168271769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180628917693620635564116101 33867922067553869168271769)
            ·
              refine ⟨25400941550665401876203827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33867922067553869168271769 25400941550665401876203827)
              ·
                refine ⟨38101412325998102814305741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25400941550665401876203827 38101412325998102814305741)
                ·
                  refine ⟨14288029622249288555364653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38101412325998102814305741 14288029622249288555364653)
                  ·
                    refine ⟨5358011108343483208261745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14288029622249288555364653 5358011108343483208261745)
                    ·
                      refine ⟨4018508331257612406196309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358011108343483208261745 4018508331257612406196309)
                      ·
                        rfl

theorem cell23_7826017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_7826017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826017 prefixEnd_7826017 := by exact prefixLift 7826017
  have htrace : WordTrace (prefixWord ++ tailWord_7826017) baseStart_7826017 baseEnd_7826017 := by
    simpa [prefixWord, tailWord_7826017, baseEnd_7826017] using wordTrace_append hprefix tailTrace_7826017
  have hstable : (prefixWord ++ tailWord_7826017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826017).length < 2 ^ (prefixWord ++ tailWord_7826017).sum := by decide
  have hdescent : baseEnd_7826017 < baseStart_7826017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826023 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7826023 : Nat := 118140960795 + 7826023 * 2 ^ 59
def prefixEnd_7826023 : Nat := 4983230072969 + 3 ^ 40 * 7826023 * 2
def baseEnd_7826023 : Nat := 1339503804047179794240427

theorem tailTrace_7826023 : CollatzResearch.WordTrace tailWord_7826023 prefixEnd_7826023 1339503804047179794240427 := by
  unfold tailWord_7826023
  simp only [CollatzResearch.WordTrace]
  refine ⟨285438508526662724163074723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190292339017775149442049815 285438508526662724163074723)
  ·
    refine ⟨428157762789994086244612085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285438508526662724163074723 428157762789994086244612085)
    ·
      refine ⟨40139790261561945585432383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 428157762789994086244612085 40139790261561945585432383)
      ·
        refine ⟨60209685392342918378148575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40139790261561945585432383 60209685392342918378148575)
        ·
          refine ⟨90314528088514377567222863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60209685392342918378148575 90314528088514377567222863)
          ·
            refine ⟨135471792132771566350834295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90314528088514377567222863 135471792132771566350834295)
            ·
              refine ⟨203207688199157349526251443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135471792132771566350834295 203207688199157349526251443)
              ·
                refine ⟨304811532298736024289377165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203207688199157349526251443 304811532298736024289377165)
                ·
                  refine ⟨114304324612026009108516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304811532298736024289377165 114304324612026009108516437)
                  ·
                    refine ⟨1339503804047179794240427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114304324612026009108516437 1339503804047179794240427)
                    ·
                      rfl

theorem cell23_7826023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7826023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826023 prefixEnd_7826023 := by exact prefixLift 7826023
  have htrace : WordTrace (prefixWord ++ tailWord_7826023) baseStart_7826023 baseEnd_7826023 := by
    simpa [prefixWord, tailWord_7826023, baseEnd_7826023] using wordTrace_append hprefix tailTrace_7826023
  have hstable : (prefixWord ++ tailWord_7826023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826023).length < 2 ^ (prefixWord ++ tailWord_7826023).sum := by decide
  have hdescent : baseEnd_7826023 < baseStart_7826023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826137 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_7826137 : Nat := 118140960795 + 7826137 * 2 ^ 59
def prefixEnd_7826137 : Nat := 4983230072969 + 3 ^ 40 * 7826137 * 2
def baseEnd_7826137 : Nat := 4018569948936151936695757

theorem tailTrace_7826137 : CollatzResearch.WordTrace tailWord_7826137 prefixEnd_7826137 4018569948936151936695757 := by
  unfold tailWord_7826137
  simp only [CollatzResearch.WordTrace]
  refine ⟨285442666448249721632724665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190295110965499814421816443 285442666448249721632724665)
  ·
    refine ⟨214081999836187291224543499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285442666448249721632724665 214081999836187291224543499)
    ·
      refine ⟨321122999754280936836815249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214081999836187291224543499 321122999754280936836815249)
      ·
        refine ⟨240842249815710702627611437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321122999754280936836815249 240842249815710702627611437)
        ·
          refine ⟨90315843680891513485354289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240842249815710702627611437 90315843680891513485354289)
          ·
            refine ⟨67736882760668635114015717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90315843680891513485354289 67736882760668635114015717)
            ·
              refine ⟨12700665517625369083877947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67736882760668635114015717 12700665517625369083877947)
              ·
                refine ⟨19050998276438053625816921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12700665517625369083877947 19050998276438053625816921)
                ·
                  refine ⟨14288248707328540219362691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19050998276438053625816921 14288248707328540219362691)
                  ·
                    refine ⟨21432373060992810329044037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14288248707328540219362691 21432373060992810329044037)
                    ·
                      refine ⟨4018569948936151936695757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21432373060992810329044037 4018569948936151936695757)
                      ·
                        rfl

theorem cell23_7826137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_7826137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826137 prefixEnd_7826137 := by exact prefixLift 7826137
  have htrace : WordTrace (prefixWord ++ tailWord_7826137) baseStart_7826137 baseEnd_7826137 := by
    simpa [prefixWord, tailWord_7826137, baseEnd_7826137] using wordTrace_append hprefix tailTrace_7826137
  have hstable : (prefixWord ++ tailWord_7826137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826137).length < 2 ^ (prefixWord ++ tailWord_7826137).sum := by decide
  have hdescent : baseEnd_7826137 < baseStart_7826137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826200 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7826200 : Nat := 118140960795 + 7826200 * 2 ^ 59
def prefixEnd_7826200 : Nat := 4983230072969 + 3 ^ 40 * 7826200 * 2
def baseEnd_7826200 : Nat := 4018602298217385190207967

theorem tailTrace_7826200 : CollatzResearch.WordTrace tailWord_7826200 prefixEnd_7826200 4018602298217385190207967 := by
  unfold tailWord_7826200
  simp only [CollatzResearch.WordTrace]
  refine ⟨142722482123510741696134027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190296642831347655594845369 142722482123510741696134027)
  ·
    refine ⟨214083723185266112544201041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142722482123510741696134027 214083723185266112544201041)
    ·
      refine ⟨160562792388949584408150781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214083723185266112544201041 160562792388949584408150781)
      ·
        refine ⟨60211047145856094153056543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160562792388949584408150781 60211047145856094153056543)
        ·
          refine ⟨90316570718784141229584815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60211047145856094153056543 90316570718784141229584815)
          ·
            refine ⟨135474856078176211844377223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90316570718784141229584815 135474856078176211844377223)
            ·
              refine ⟨203212284117264317766565835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135474856078176211844377223 203212284117264317766565835)
              ·
                refine ⟨304818426175896476649848753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203212284117264317766565835 304818426175896476649848753)
                ·
                  refine ⟨228613819631922357487386565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304818426175896476649848753 228613819631922357487386565)
                  ·
                    refine ⟨42865091180985442028884981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228613819631922357487386565 42865091180985442028884981)
                    ·
                      refine ⟨4018602298217385190207967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42865091180985442028884981 4018602298217385190207967)
                      ·
                        rfl

theorem cell23_7826200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7826200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826200 prefixEnd_7826200 := by exact prefixLift 7826200
  have htrace : WordTrace (prefixWord ++ tailWord_7826200) baseStart_7826200 baseEnd_7826200 := by
    simpa [prefixWord, tailWord_7826200, baseEnd_7826200] using wordTrace_append hprefix tailTrace_7826200
  have hstable : (prefixWord ++ tailWord_7826200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826200).length < 2 ^ (prefixWord ++ tailWord_7826200).sum := by decide
  have hdescent : baseEnd_7826200 < baseStart_7826200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826327 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 6]
def baseStart_7826327 : Nat := 118140960795 + 7826327 * 2 ^ 59
def prefixEnd_7826327 : Nat := 4983230072969 + 3 ^ 40 * 7826327 * 2
def baseEnd_7826327 : Nat := 1339555836753502064439961

theorem tailTrace_7826327 : CollatzResearch.WordTrace tailWord_7826327 prefixEnd_7826327 1339555836753502064439961 := by
  unfold tailWord_7826327
  simp only [CollatzResearch.WordTrace]
  refine ⟨285449596317561384082141235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190299730878374256054760823 285449596317561384082141235)
  ·
    refine ⟨428174394476342076123211853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285449596317561384082141235 428174394476342076123211853)
    ·
      refine ⟨160565397928628278546204445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428174394476342076123211853 160565397928628278546204445)
      ·
        refine ⟨60212024223235604454826667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160565397928628278546204445 60212024223235604454826667)
        ·
          refine ⟨90318036334853406682240001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60212024223235604454826667 90318036334853406682240001)
          ·
            refine ⟨67738527251140055011680001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90318036334853406682240001 67738527251140055011680001)
            ·
              refine ⟨50803895438355041258760001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67738527251140055011680001 50803895438355041258760001)
              ·
                refine ⟨38102921578766280944070001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50803895438355041258760001 38102921578766280944070001)
                ·
                  refine ⟨28577191184074710708052501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38102921578766280944070001 28577191184074710708052501)
                  ·
                    refine ⟨1339555836753502064439961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28577191184074710708052501 1339555836753502064439961)
                    ·
                      rfl

theorem cell23_7826327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_7826327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826327 prefixEnd_7826327 := by exact prefixLift 7826327
  have htrace : WordTrace (prefixWord ++ tailWord_7826327) baseStart_7826327 baseEnd_7826327 := by
    simpa [prefixWord, tailWord_7826327, baseEnd_7826327] using wordTrace_append hprefix tailTrace_7826327
  have hstable : (prefixWord ++ tailWord_7826327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826327).length < 2 ^ (prefixWord ++ tailWord_7826327).sum := by decide
  have hdescent : baseEnd_7826327 < baseStart_7826327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826347 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_7826347 : Nat := 118140960795 + 7826347 * 2 ^ 59
def prefixEnd_7826347 : Nat := 4983230072969 + 3 ^ 40 * 7826347 * 2
def baseEnd_7826347 : Nat := 4018677779873596115069791

theorem tailTrace_7826347 : CollatzResearch.WordTrace tailWord_7826347 prefixEnd_7826347 4018677779873596115069791 := by
  unfold tailWord_7826347
  simp only [CollatzResearch.WordTrace]
  refine ⟨285450325777488927497869295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190300217184992618331912863 285450325777488927497869295)
  ·
    refine ⟨428175488666233391246803943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285450325777488927497869295 428175488666233391246803943)
    ·
      refine ⟨642263232999350086870205915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428175488666233391246803943 642263232999350086870205915)
      ·
        refine ⟨963394849499025130305308873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642263232999350086870205915 963394849499025130305308873)
        ·
          refine ⟨722546137124268847728981655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963394849499025130305308873 722546137124268847728981655)
          ·
            refine ⟨1083819205686403271593472483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722546137124268847728981655 1083819205686403271593472483)
            ·
              refine ⟨1625728808529604907390208725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083819205686403271593472483 1625728808529604907390208725)
              ·
                refine ⟨38103018949912615016958017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1625728808529604907390208725 38103018949912615016958017)
                ·
                  refine ⟨28577264212434461262718513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38103018949912615016958017 28577264212434461262718513)
                  ·
                    refine ⟨21432948159325845947038885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28577264212434461262718513 21432948159325845947038885)
                    ·
                      refine ⟨4018677779873596115069791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21432948159325845947038885 4018677779873596115069791)
                      ·
                        rfl

theorem cell23_7826347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_7826347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826347 prefixEnd_7826347 := by exact prefixLift 7826347
  have htrace : WordTrace (prefixWord ++ tailWord_7826347) baseStart_7826347 baseEnd_7826347 := by
    simpa [prefixWord, tailWord_7826347, baseEnd_7826347] using wordTrace_append hprefix tailTrace_7826347
  have hstable : (prefixWord ++ tailWord_7826347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826347).length < 2 ^ (prefixWord ++ tailWord_7826347).sum := by decide
  have hdescent : baseEnd_7826347 < baseStart_7826347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826424 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_7826424 : Nat := 118140960795 + 7826424 * 2 ^ 59
def prefixEnd_7826424 : Nat := 4983230072969 + 3 ^ 40 * 7826424 * 2
def baseEnd_7826424 : Nat := 4018717317883992313806937

theorem tailTrace_7826424 : CollatzResearch.WordTrace tailWord_7826424 prefixEnd_7826424 4018717317883992313806937 := by
  unfold tailWord_7826424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142726567099104984824211163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190302089465473313098948217 142726567099104984824211163)
  ·
    refine ⟨214089850648657477236316745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142726567099104984824211163 214089850648657477236316745)
    ·
      refine ⟨160567387986493107927237559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214089850648657477236316745 160567387986493107927237559)
      ·
        refine ⟨240851081979739661890856339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160567387986493107927237559 240851081979739661890856339)
        ·
          refine ⟨361276622969609492836284509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240851081979739661890856339 361276622969609492836284509)
          ·
            refine ⟨135478733613603559813606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361276622969609492836284509 135478733613603559813606691)
            ·
              refine ⟨203218100420405339720410037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135478733613603559813606691 203218100420405339720410037)
              ·
                refine ⟨19051696914413000598788441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203218100420405339720410037 19051696914413000598788441)
                ·
                  refine ⟨14288772685809750449091331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19051696914413000598788441 14288772685809750449091331)
                  ·
                    refine ⟨21433159028714625673636997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14288772685809750449091331 21433159028714625673636997)
                    ·
                      refine ⟨4018717317883992313806937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21433159028714625673636997 4018717317883992313806937)
                      ·
                        rfl

theorem cell23_7826424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_7826424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826424 prefixEnd_7826424 := by exact prefixLift 7826424
  have htrace : WordTrace (prefixWord ++ tailWord_7826424) baseStart_7826424 baseEnd_7826424 := by
    simpa [prefixWord, tailWord_7826424, baseEnd_7826424] using wordTrace_append hprefix tailTrace_7826424
  have hstable : (prefixWord ++ tailWord_7826424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826424).length < 2 ^ (prefixWord ++ tailWord_7826424).sum := by decide
  have hdescent : baseEnd_7826424 < baseStart_7826424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826427 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_7826427 : Nat := 118140960795 + 7826427 * 2 ^ 59
def prefixEnd_7826427 : Nat := 4983230072969 + 3 ^ 40 * 7826427 * 2
def baseEnd_7826427 : Nat := 4018718858325955802069423

theorem tailTrace_7826427 : CollatzResearch.WordTrace tailWord_7826427 prefixEnd_7826427 4018718858325955802069423 := by
  unfold tailWord_7826427
  simp only [CollatzResearch.WordTrace]
  refine ⟨285453243617199101160781535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190302162411466067440521023 285453243617199101160781535)
  ·
    refine ⟨428179865425798651741172303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285453243617199101160781535 428179865425798651741172303)
    ·
      refine ⟨642269798138697977611758455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428179865425798651741172303 642269798138697977611758455)
      ·
        refine ⟨963404697208046966417637683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642269798138697977611758455 963404697208046966417637683)
        ·
          refine ⟨1445107045812070449626456525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963404697208046966417637683 1445107045812070449626456525)
          ·
            refine ⟨541915142179526418609921197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1445107045812070449626456525 541915142179526418609921197)
            ·
              refine ⟨203218178317322406978720449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541915142179526418609921197 203218178317322406978720449)
              ·
                refine ⟨152413633737991805234040337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203218178317322406978720449 152413633737991805234040337)
                ·
                  refine ⟨114310225303493853925530253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152413633737991805234040337 114310225303493853925530253)
                  ·
                    refine ⟨42866334488810195222073845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114310225303493853925530253 42866334488810195222073845)
                    ·
                      refine ⟨4018718858325955802069423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42866334488810195222073845 4018718858325955802069423)
                      ·
                        rfl

theorem cell23_7826427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_7826427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826427 prefixEnd_7826427 := by exact prefixLift 7826427
  have htrace : WordTrace (prefixWord ++ tailWord_7826427) baseStart_7826427 baseEnd_7826427 := by
    simpa [prefixWord, tailWord_7826427, baseEnd_7826427] using wordTrace_append hprefix tailTrace_7826427
  have hstable : (prefixWord ++ tailWord_7826427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826427).length < 2 ^ (prefixWord ++ tailWord_7826427).sum := by decide
  have hdescent : baseEnd_7826427 < baseStart_7826427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826478 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7826478 : Nat := 118140960795 + 7826478 * 2 ^ 59
def prefixEnd_7826478 : Nat := 4983230072969 + 3 ^ 40 * 7826478 * 2
def baseEnd_7826478 : Nat := 4018745045839335102531689

theorem tailTrace_7826478 : CollatzResearch.WordTrace tailWord_7826478 prefixEnd_7826478 4018745045839335102531689 := by
  unfold tailWord_7826478
  simp only [CollatzResearch.WordTrace]
  refine ⟨35681887967501792108861011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190303402493342891247258725 35681887967501792108861011)
  ·
    refine ⟨53522831951252688163291517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35681887967501792108861011 53522831951252688163291517)
    ·
      refine ⟨20071061981719758061234319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53522831951252688163291517 20071061981719758061234319)
      ·
        refine ⟨30106592972579637091851479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20071061981719758061234319 30106592972579637091851479)
        ·
          refine ⟨45159889458869455637777219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30106592972579637091851479 45159889458869455637777219)
          ·
            refine ⟨67739834188304183456665829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45159889458869455637777219 67739834188304183456665829)
            ·
              refine ⟨12701218910307034398124843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67739834188304183456665829 12701218910307034398124843)
              ·
                refine ⟨19051828365460551597187265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12701218910307034398124843 19051828365460551597187265)
                ·
                  refine ⟨14288871274095413697890449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19051828365460551597187265 14288871274095413697890449)
                  ·
                    refine ⟨10716653455571560273417837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14288871274095413697890449 10716653455571560273417837)
                    ·
                      refine ⟨4018745045839335102531689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10716653455571560273417837 4018745045839335102531689)
                      ·
                        rfl

theorem cell23_7826478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7826478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826478 prefixEnd_7826478 := by exact prefixLift 7826478
  have htrace : WordTrace (prefixWord ++ tailWord_7826478) baseStart_7826478 baseEnd_7826478 := by
    simpa [prefixWord, tailWord_7826478, baseEnd_7826478] using wordTrace_append hprefix tailTrace_7826478
  have hstable : (prefixWord ++ tailWord_7826478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826478).length < 2 ^ (prefixWord ++ tailWord_7826478).sum := by decide
  have hdescent : baseEnd_7826478 < baseStart_7826478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826502 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_7826502 : Nat := 118140960795 + 7826502 * 2 ^ 59
def prefixEnd_7826502 : Nat := 4983230072969 + 3 ^ 40 * 7826502 * 2
def baseEnd_7826502 : Nat := 1339585789791681002877193

theorem tailTrace_7826502 : CollatzResearch.WordTrace tailWord_7826502 prefixEnd_7826502 1339585789791681002877193 := by
  unfold tailWord_7826502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920499346622730905305055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190303986061284925979841173 8920499346622730905305055)
  ·
    refine ⟨13380749019934096357957583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8920499346622730905305055 13380749019934096357957583)
    ·
      refine ⟨20071123529901144536936375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13380749019934096357957583 20071123529901144536936375)
      ·
        refine ⟨30106685294851716805404563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20071123529901144536936375 30106685294851716805404563)
        ·
          refine ⟨45160027942277575208106845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30106685294851716805404563 45160027942277575208106845)
          ·
            refine ⟨16935010478354090703040067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45160027942277575208106845 16935010478354090703040067)
            ·
              refine ⟨25402515717531136054560101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16935010478354090703040067 25402515717531136054560101)
              ·
                refine ⟨4762971697037088010230019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25402515717531136054560101 4762971697037088010230019)
                ·
                  refine ⟨7144457545555632015345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762971697037088010230019 7144457545555632015345029)
                  ·
                    refine ⟨1339585789791681002877193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144457545555632015345029 1339585789791681002877193)
                    ·
                      rfl

theorem cell23_7826502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_7826502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826502 prefixEnd_7826502 := by exact prefixLift 7826502
  have htrace : WordTrace (prefixWord ++ tailWord_7826502) baseStart_7826502 baseEnd_7826502 := by
    simpa [prefixWord, tailWord_7826502, baseEnd_7826502] using wordTrace_append hprefix tailTrace_7826502
  have hstable : (prefixWord ++ tailWord_7826502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826502).length < 2 ^ (prefixWord ++ tailWord_7826502).sum := by decide
  have hdescent : baseEnd_7826502 < baseStart_7826502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7826531 : Nat := 118140960795 + 7826531 * 2 ^ 59
def prefixEnd_7826531 : Nat := 4983230072969 + 3 ^ 40 * 7826531 * 2
def baseEnd_7826531 : Nat := 4018772260314023395168945

theorem tailTrace_7826531 : CollatzResearch.WordTrace tailWord_7826531 prefixEnd_7826531 4018772260314023395168945 := by
  unfold tailWord_7826531
  simp only [CollatzResearch.WordTrace]
  refine ⟨285457036808822326922567447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190304691205881551281711631 285457036808822326922567447)
  ·
    refine ⟨428185555213233490383851171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285457036808822326922567447 428185555213233490383851171)
    ·
      refine ⟨642278332819850235575776757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428185555213233490383851171 642278332819850235575776757)
      ·
        refine ⟨60213593701860959585229071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 642278332819850235575776757 60213593701860959585229071)
        ·
          refine ⟨90320390552791439377843607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60213593701860959585229071 90320390552791439377843607)
          ·
            refine ⟨135480585829187159066765411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90320390552791439377843607 135480585829187159066765411)
            ·
              refine ⟨203220878743780738600148117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135480585829187159066765411 203220878743780738600148117)
              ·
                refine ⟨9525978691114722121881943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203220878743780738600148117 9525978691114722121881943)
                ·
                  refine ⟨14288968036672083182822915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9525978691114722121881943 14288968036672083182822915)
                  ·
                    refine ⟨21433452055008124774234373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14288968036672083182822915 21433452055008124774234373)
                    ·
                      refine ⟨4018772260314023395168945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21433452055008124774234373 4018772260314023395168945)
                      ·
                        rfl

theorem cell23_7826531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7826531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826531 prefixEnd_7826531 := by exact prefixLift 7826531
  have htrace : WordTrace (prefixWord ++ tailWord_7826531) baseStart_7826531 baseEnd_7826531 := by
    simpa [prefixWord, tailWord_7826531, baseEnd_7826531] using wordTrace_append hprefix tailTrace_7826531
  have hstable : (prefixWord ++ tailWord_7826531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826531).length < 2 ^ (prefixWord ++ tailWord_7826531).sum := by decide
  have hdescent : baseEnd_7826531 < baseStart_7826531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826535 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_7826535 : Nat := 118140960795 + 7826535 * 2 ^ 59
def prefixEnd_7826535 : Nat := 4983230072969 + 3 ^ 40 * 7826535 * 2
def baseEnd_7826535 : Nat := 4018774314236641379518927

theorem tailTrace_7826535 : CollatzResearch.WordTrace tailWord_7826535 prefixEnd_7826535 4018774314236641379518927 := by
  unfold tailWord_7826535
  simp only [CollatzResearch.WordTrace]
  refine ⟨285457182700807835605713059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190304788467205223737142039 285457182700807835605713059)
  ·
    refine ⟨428185774051211753408569589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285457182700807835605713059 428185774051211753408569589)
    ·
      refine ⟨40142416317301101882053399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 428185774051211753408569589 40142416317301101882053399)
      ·
        refine ⟨60213624475951652823080099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40142416317301101882053399 60213624475951652823080099)
        ·
          refine ⟨90320436713927479234620149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60213624475951652823080099 90320436713927479234620149)
          ·
            refine ⟨8467540941930701178245639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90320436713927479234620149 8467540941930701178245639)
            ·
              refine ⟨12701311412896051767368459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467540941930701178245639 12701311412896051767368459)
              ·
                refine ⟨19051967119344077651052689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12701311412896051767368459 19051967119344077651052689)
                ·
                  refine ⟨14288975339508058238289517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19051967119344077651052689 14288975339508058238289517)
                  ·
                    refine ⟨5358365752315521839358569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14288975339508058238289517 5358365752315521839358569)
                    ·
                      refine ⟨4018774314236641379518927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358365752315521839358569 4018774314236641379518927)
                      ·
                        rfl

theorem cell23_7826535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_7826535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826535 prefixEnd_7826535 := by exact prefixLift 7826535
  have htrace : WordTrace (prefixWord ++ tailWord_7826535) baseStart_7826535 baseEnd_7826535 := by
    simpa [prefixWord, tailWord_7826535, baseEnd_7826535] using wordTrace_append hprefix tailTrace_7826535
  have hstable : (prefixWord ++ tailWord_7826535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826535).length < 2 ^ (prefixWord ++ tailWord_7826535).sum := by decide
  have hdescent : baseEnd_7826535 < baseStart_7826535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826541 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_7826541 : Nat := 118140960795 + 7826541 * 2 ^ 59
def prefixEnd_7826541 : Nat := 4983230072969 + 3 ^ 40 * 7826541 * 2
def baseEnd_7826541 : Nat := 1339592465040189452014633

theorem tailTrace_7826541 : CollatzResearch.WordTrace tailWord_7826541 prefixEnd_7826541 1339592465040189452014633 := by
  unfold tailWord_7826541
  simp only [CollatzResearch.WordTrace]
  refine ⟨285457401538786098630431477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190304934359190732420287651 285457401538786098630431477)
  ·
    refine ⟨26761631394261196746602951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285457401538786098630431477 26761631394261196746602951)
    ·
      refine ⟨40142447091391795119904427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26761631394261196746602951 40142447091391795119904427)
      ·
        refine ⟨60213670637087692679856641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40142447091391795119904427 60213670637087692679856641)
        ·
          refine ⟨45160252977815769509892481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60213670637087692679856641 45160252977815769509892481)
          ·
            refine ⟨33870189733361827132419361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45160252977815769509892481 33870189733361827132419361)
            ·
              refine ⟨25402642300021370349314521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33870189733361827132419361 25402642300021370349314521)
              ·
                refine ⟨19051981725016027761985891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25402642300021370349314521 19051981725016027761985891)
                ·
                  refine ⟨28577972587524041642978837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19051981725016027761985891 28577972587524041642978837)
                  ·
                    refine ⟨1339592465040189452014633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28577972587524041642978837 1339592465040189452014633)
                    ·
                      rfl

theorem cell23_7826541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_7826541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826541 prefixEnd_7826541 := by exact prefixLift 7826541
  have htrace : WordTrace (prefixWord ++ tailWord_7826541) baseStart_7826541 baseEnd_7826541 := by
    simpa [prefixWord, tailWord_7826541, baseEnd_7826541] using wordTrace_append hprefix tailTrace_7826541
  have hstable : (prefixWord ++ tailWord_7826541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826541).length < 2 ^ (prefixWord ++ tailWord_7826541).sum := by decide
  have hdescent : baseEnd_7826541 < baseStart_7826541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826542 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7826542 : Nat := 118140960795 + 7826542 * 2 ^ 59
def prefixEnd_7826542 : Nat := 4983230072969 + 3 ^ 40 * 7826542 * 2
def baseEnd_7826542 : Nat := 4018777908601222852131395

theorem tailTrace_7826542 : CollatzResearch.WordTrace tailWord_7826542 prefixEnd_7826542 4018777908601222852131395 := by
  unfold tailWord_7826542
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682179751472809475152235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190304958674521650534145253 35682179751472809475152235)
  ·
    refine ⟨53523269627209214212728353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35682179751472809475152235 53523269627209214212728353)
    ·
      refine ⟨40142452220406910659546265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53523269627209214212728353 40142452220406910659546265)
      ·
        refine ⟨30106839165305182994659699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40142452220406910659546265 30106839165305182994659699)
        ·
          refine ⟨45160258747957774491989549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30106839165305182994659699 45160258747957774491989549)
          ·
            refine ⟨16935097030484165434496081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45160258747957774491989549 16935097030484165434496081)
            ·
              refine ⟨12701322772863124075872061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16935097030484165434496081 12701322772863124075872061)
              ·
                refine ⟨4762996039823671528452023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12701322772863124075872061 4762996039823671528452023)
                ·
                  refine ⟨7144494059735507292678035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762996039823671528452023 7144494059735507292678035)
                  ·
                    refine ⟨10716741089603260939017053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7144494059735507292678035 10716741089603260939017053)
                    ·
                      refine ⟨4018777908601222852131395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10716741089603260939017053 4018777908601222852131395)
                      ·
                        rfl

theorem cell23_7826542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7826542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826542 prefixEnd_7826542 := by exact prefixLift 7826542
  have htrace : WordTrace (prefixWord ++ tailWord_7826542) baseStart_7826542 baseEnd_7826542 := by
    simpa [prefixWord, tailWord_7826542, baseEnd_7826542] using wordTrace_append hprefix tailTrace_7826542
  have hstable : (prefixWord ++ tailWord_7826542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826542).length < 2 ^ (prefixWord ++ tailWord_7826542).sum := by decide
  have hdescent : baseEnd_7826542 < baseStart_7826542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826568 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7826568 : Nat := 118140960795 + 7826568 * 2 ^ 59
def prefixEnd_7826568 : Nat := 4983230072969 + 3 ^ 40 * 7826568 * 2
def baseEnd_7826568 : Nat := 4018791259098239750406275

theorem tailTrace_7826568 : CollatzResearch.WordTrace tailWord_7826568 prefixEnd_7826568 4018791259098239750406275 := by
  unfold tailWord_7826568
  simp only [CollatzResearch.WordTrace]
  refine ⟨142729193154844141120832179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190305590873125521494442905 142729193154844141120832179)
  ·
    refine ⟨214093789732266211681248269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142729193154844141120832179 214093789732266211681248269)
    ·
      refine ⟨80285171149599829380468101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214093789732266211681248269 80285171149599829380468101)
      ·
        refine ⟨15053469590549968008837769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80285171149599829380468101 15053469590549968008837769)
        ·
          refine ⟨11290102192912476006628327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15053469590549968008837769 11290102192912476006628327)
          ·
            refine ⟨16935153289368714009942491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290102192912476006628327 16935153289368714009942491)
            ·
              refine ⟨25402729934053071014913737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16935153289368714009942491 25402729934053071014913737)
              ·
                refine ⟨19052047450539803261185303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25402729934053071014913737 19052047450539803261185303)
                ·
                  refine ⟨28578071175809704891777955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052047450539803261185303 28578071175809704891777955)
                  ·
                    refine ⟨42867106763714557337666933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28578071175809704891777955 42867106763714557337666933)
                    ·
                      refine ⟨4018791259098239750406275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42867106763714557337666933 4018791259098239750406275)
                      ·
                        rfl

theorem cell23_7826568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7826568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826568 prefixEnd_7826568 := by exact prefixLift 7826568
  have htrace : WordTrace (prefixWord ++ tailWord_7826568) baseStart_7826568 baseEnd_7826568 := by
    simpa [prefixWord, tailWord_7826568, baseEnd_7826568] using wordTrace_append hprefix tailTrace_7826568
  have hstable : (prefixWord ++ tailWord_7826568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826568).length < 2 ^ (prefixWord ++ tailWord_7826568).sum := by decide
  have hdescent : baseEnd_7826568 < baseStart_7826568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826578 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7826578 : Nat := 118140960795 + 7826578 * 2 ^ 59
def prefixEnd_7826578 : Nat := 4983230072969 + 3 ^ 40 * 7826578 * 2
def baseEnd_7826578 : Nat := 4018796393904784711281229

theorem tailTrace_7826578 : CollatzResearch.WordTrace tailWord_7826578 prefixEnd_7826578 4018796393904784711281229 := by
  unfold tailWord_7826578
  simp only [CollatzResearch.WordTrace]
  refine ⟨71364687759913013487382097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190305834026434702633018925 71364687759913013487382097)
  ·
    refine ⟨53523515819934760115536573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71364687759913013487382097 53523515819934760115536573)
    ·
      refine ⟨20071318432475535043326215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53523515819934760115536573 20071318432475535043326215)
      ·
        refine ⟨30106977648713302564989323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20071318432475535043326215 30106977648713302564989323)
        ·
          refine ⟨45160466473069953847483985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30106977648713302564989323 45160466473069953847483985)
          ·
            refine ⟨33870349854802465385612989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45160466473069953847483985 33870349854802465385612989)
            ·
              refine ⟨12701381195550924519604871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33870349854802465385612989 12701381195550924519604871)
              ·
                refine ⟨19052071793326386779407307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12701381195550924519604871 19052071793326386779407307)
                ·
                  refine ⟨28578107689989580169110961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052071793326386779407307 28578107689989580169110961)
                  ·
                    refine ⟨21433580767492185126833221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28578107689989580169110961 21433580767492185126833221)
                    ·
                      refine ⟨4018796393904784711281229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21433580767492185126833221 4018796393904784711281229)
                      ·
                        rfl

theorem cell23_7826578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7826578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826578 prefixEnd_7826578 := by exact prefixLift 7826578
  have htrace : WordTrace (prefixWord ++ tailWord_7826578) baseStart_7826578 baseEnd_7826578 := by
    simpa [prefixWord, tailWord_7826578, baseEnd_7826578] using wordTrace_append hprefix tailTrace_7826578
  have hstable : (prefixWord ++ tailWord_7826578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826578).length < 2 ^ (prefixWord ++ tailWord_7826578).sum := by decide
  have hdescent : baseEnd_7826578 < baseStart_7826578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826581 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_7826581 : Nat := 118140960795 + 7826581 * 2 ^ 59
def prefixEnd_7826581 : Nat := 4983230072969 + 3 ^ 40 * 7826581 * 2
def baseEnd_7826581 : Nat := 4018797934346748199543715

theorem tailTrace_7826581 : CollatzResearch.WordTrace tailWord_7826581 prefixEnd_7826581 4018797934346748199543715 := by
  unfold tailWord_7826581
  simp only [CollatzResearch.WordTrace]
  refine ⟨285458860458641185461887597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190305906972427456974591731 285458860458641185461887597)
  ·
    refine ⟨107047072671990444548207849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285458860458641185461887597 107047072671990444548207849)
    ·
      refine ⟨80285304503992833411155887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107047072671990444548207849 80285304503992833411155887)
      ·
        refine ⟨120427956755989250116733831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80285304503992833411155887 120427956755989250116733831)
        ·
          refine ⟨180641935133983875175100747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120427956755989250116733831 180641935133983875175100747)
          ·
            refine ⟨270962902700975812762651121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180641935133983875175100747 270962902700975812762651121)
            ·
              refine ⟨203222177025731859571988341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270962902700975812762651121 203222177025731859571988341)
              ·
                refine ⟨19052079096162361834873907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203222177025731859571988341 19052079096162361834873907)
                ·
                  refine ⟨28578118644243542752310861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052079096162361834873907 28578118644243542752310861)
                  ·
                    refine ⟨10716794491591328532116573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28578118644243542752310861 10716794491591328532116573)
                    ·
                      refine ⟨4018797934346748199543715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10716794491591328532116573 4018797934346748199543715)
                      ·
                        rfl

theorem cell23_7826581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_7826581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826581 prefixEnd_7826581 := by exact prefixLift 7826581
  have htrace : WordTrace (prefixWord ++ tailWord_7826581) baseStart_7826581 baseEnd_7826581 := by
    simpa [prefixWord, tailWord_7826581, baseEnd_7826581] using wordTrace_append hprefix tailTrace_7826581
  have hstable : (prefixWord ++ tailWord_7826581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826581).length < 2 ^ (prefixWord ++ tailWord_7826581).sum := by decide
  have hdescent : baseEnd_7826581 < baseStart_7826581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826588 : List Nat := [2, 2, 3, 2, 1, 4, 2, 7]
def baseStart_7826588 : Nat := 118140960795 + 7826588 * 2 ^ 59
def prefixEnd_7826588 : Nat := 4983230072969 + 3 ^ 40 * 7826588 * 2
def baseEnd_7826588 : Nat := 148844501063382580450229

theorem tailTrace_7826588 : CollatzResearch.WordTrace tailWord_7826588 prefixEnd_7826588 148844501063382580450229 := by
  unfold tailWord_7826588
  simp only [CollatzResearch.WordTrace]
  refine ⟨142729557884807912828696209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190306077179743883771594945 142729557884807912828696209)
  ·
    refine ⟨107047168413605934621522157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142729557884807912828696209 107047168413605934621522157)
    ·
      refine ⟨40142688155102225483070809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107047168413605934621522157 40142688155102225483070809)
      ·
        refine ⟨30107016116326669112303107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40142688155102225483070809 30107016116326669112303107)
        ·
          refine ⟨45160524174490003668454661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30107016116326669112303107 45160524174490003668454661)
          ·
            refine ⟨8467598282716875687835249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45160524174490003668454661 8467598282716875687835249)
            ·
              refine ⟨6350698712037656765876437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467598282716875687835249 6350698712037656765876437)
              ·
                refine ⟨148844501063382580450229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6350698712037656765876437 148844501063382580450229)
                ·
                  rfl

theorem cell23_7826588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 7].length) (baseStart_7826588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826588 prefixEnd_7826588 := by exact prefixLift 7826588
  have htrace : WordTrace (prefixWord ++ tailWord_7826588) baseStart_7826588 baseEnd_7826588 := by
    simpa [prefixWord, tailWord_7826588, baseEnd_7826588] using wordTrace_append hprefix tailTrace_7826588
  have hstable : (prefixWord ++ tailWord_7826588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826588).length < 2 ^ (prefixWord ++ tailWord_7826588).sum := by decide
  have hdescent : baseEnd_7826588 < baseStart_7826588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826599 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7826599 : Nat := 118140960795 + 7826599 * 2 ^ 59
def prefixEnd_7826599 : Nat := 4983230072969 + 3 ^ 40 * 7826599 * 2
def baseEnd_7826599 : Nat := 4018807176998529129118633

theorem tailTrace_7826599 : CollatzResearch.WordTrace tailWord_7826599 prefixEnd_7826599 4018807176998529129118633 := by
  unfold tailWord_7826599
  simp only [CollatzResearch.WordTrace]
  refine ⟨285459516972575974536042851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190306344648383983024028567 285459516972575974536042851)
  ·
    refine ⟨428189275458863961804064277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285459516972575974536042851 428189275458863961804064277)
    ·
      refine ⟨20071372287134248209565513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 428189275458863961804064277 20071372287134248209565513)
      ·
        refine ⟨15053529215350686157174135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20071372287134248209565513 15053529215350686157174135)
        ·
          refine ⟨22580293823026029235761203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053529215350686157174135 22580293823026029235761203)
          ·
            refine ⟨33870440734539043853641805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22580293823026029235761203 33870440734539043853641805)
            ·
              refine ⟨12701415275452141445115677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33870440734539043853641805 12701415275452141445115677)
              ·
                refine ⟨4763030728294553041918379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12701415275452141445115677 4763030728294553041918379)
                ·
                  refine ⟨7144546092441829562877569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763030728294553041918379 7144546092441829562877569)
                  ·
                    refine ⟨5358409569331372172158177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7144546092441829562877569 5358409569331372172158177)
                    ·
                      refine ⟨4018807176998529129118633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358409569331372172158177 4018807176998529129118633)
                      ·
                        rfl

theorem cell23_7826599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7826599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826599 prefixEnd_7826599 := by exact prefixLift 7826599
  have htrace : WordTrace (prefixWord ++ tailWord_7826599) baseStart_7826599 baseEnd_7826599 := by
    simpa [prefixWord, tailWord_7826599, baseEnd_7826599] using wordTrace_append hprefix tailTrace_7826599
  have hstable : (prefixWord ++ tailWord_7826599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826599).length < 2 ^ (prefixWord ++ tailWord_7826599).sum := by decide
  have hdescent : baseEnd_7826599 < baseStart_7826599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826626 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7826626 : Nat := 118140960795 + 7826626 * 2 ^ 59
def prefixEnd_7826626 : Nat := 4983230072969 + 3 ^ 40 * 7826626 * 2
def baseEnd_7826626 : Nat := 1339607013658733507827003

theorem tailTrace_7826626 : CollatzResearch.WordTrace tailWord_7826626 prefixEnd_7826626 1339607013658733507827003 := by
  unfold tailWord_7826626
  simp only [CollatzResearch.WordTrace]
  refine ⟨71365125435869539536818933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190307001162318772098183821 71365125435869539536818933)
  ·
    refine ⟨6690480509612769331576775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71365125435869539536818933 6690480509612769331576775)
    ·
      refine ⟨10035720764419153997365163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690480509612769331576775 10035720764419153997365163)
      ·
        refine ⟨15053581146628730996047745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035720764419153997365163 15053581146628730996047745)
        ·
          refine ⟨11290185859971548247035809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15053581146628730996047745 11290185859971548247035809)
          ·
            refine ⟨8467639394978661185276857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11290185859971548247035809 8467639394978661185276857)
            ·
              refine ⟨6350729546233995888957643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467639394978661185276857 6350729546233995888957643)
              ·
                refine ⟨9526094319350993833436465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350729546233995888957643 9526094319350993833436465)
                ·
                  refine ⟨7144570739513245375077349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526094319350993833436465 7144570739513245375077349)
                  ·
                    refine ⟨1339607013658733507827003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144570739513245375077349 1339607013658733507827003)
                    ·
                      rfl

theorem cell23_7826626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7826626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826626 prefixEnd_7826626 := by exact prefixLift 7826626
  have htrace : WordTrace (prefixWord ++ tailWord_7826626) baseStart_7826626 baseEnd_7826626 := by
    simpa [prefixWord, tailWord_7826626, baseEnd_7826626] using wordTrace_append hprefix tailTrace_7826626
  have hstable : (prefixWord ++ tailWord_7826626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826626).length < 2 ^ (prefixWord ++ tailWord_7826626).sum := by decide
  have hdescent : baseEnd_7826626 < baseStart_7826626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826698 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_7826698 : Nat := 118140960795 + 7826698 * 2 ^ 59
def prefixEnd_7826698 : Nat := 4983230072969 + 3 ^ 40 * 7826698 * 2
def baseEnd_7826698 : Nat := 4018858011583324241780677

theorem tailTrace_7826698 : CollatzResearch.WordTrace tailWord_7826698 prefixEnd_7826698 4018858011583324241780677 := by
  unfold tailWord_7826698
  simp only [CollatzResearch.WordTrace]
  refine ⟨71365781949804328610974187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190308751866144876295931165 71365781949804328610974187)
  ·
    refine ⟨107048672924706492916461281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71365781949804328610974187 107048672924706492916461281)
    ·
      refine ⟨80286504693529869687345961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107048672924706492916461281 80286504693529869687345961)
      ·
        refine ⟨60214878520147402265509471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80286504693529869687345961 60214878520147402265509471)
        ·
          refine ⟨90322317780221103398264207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60214878520147402265509471 90322317780221103398264207)
          ·
            refine ⟨135483476670331655097396311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90322317780221103398264207 135483476670331655097396311)
            ·
              refine ⟨203225215005497482646094467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135483476670331655097396311 203225215005497482646094467)
              ·
                refine ⟨304837822508246223969141701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203225215005497482646094467 304837822508246223969141701)
                ·
                  refine ⟨57157091720296166994214069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304837822508246223969141701 57157091720296166994214069)
                  ·
                    refine ⟨5358477348777765655707569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57157091720296166994214069 5358477348777765655707569)
                    ·
                      refine ⟨4018858011583324241780677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358477348777765655707569 4018858011583324241780677)
                      ·
                        rfl

theorem cell23_7826698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_7826698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826698 prefixEnd_7826698 := by exact prefixLift 7826698
  have htrace : WordTrace (prefixWord ++ tailWord_7826698) baseStart_7826698 baseEnd_7826698 := by
    simpa [prefixWord, tailWord_7826698, baseEnd_7826698] using wordTrace_append hprefix tailTrace_7826698
  have hstable : (prefixWord ++ tailWord_7826698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826698).length < 2 ^ (prefixWord ++ tailWord_7826698).sum := by decide
  have hdescent : baseEnd_7826698 < baseStart_7826698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3]
def baseStart_7826731 : Nat := 118140960795 + 7826731 * 2 ^ 59
def prefixEnd_7826731 : Nat := 4983230072969 + 3 ^ 40 * 7826731 * 2
def baseEnd_7826731 : Nat := 4018874956444922612668025

theorem tailTrace_7826731 : CollatzResearch.WordTrace tailWord_7826731 prefixEnd_7826731 4018874956444922612668025 := by
  unfold tailWord_7826731
  simp only [CollatzResearch.WordTrace]
  refine ⟨285464331408097761079848047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190309554272065174053232031 285464331408097761079848047)
  ·
    refine ⟨428196497112146641619772071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285464331408097761079848047 428196497112146641619772071)
    ·
      refine ⟨642294745668219962429658107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428196497112146641619772071 642294745668219962429658107)
      ·
        refine ⟨963442118502329943644487161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642294745668219962429658107 963442118502329943644487161)
        ·
          refine ⟨722581588876747457733365371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963442118502329943644487161 722581588876747457733365371)
          ·
            refine ⟨1083872383315121186600048057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722581588876747457733365371 1083872383315121186600048057)
            ·
              refine ⟨812904287486340889950036043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083872383315121186600048057 812904287486340889950036043)
              ·
                refine ⟨1219356431229511334925054065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812904287486340889950036043 1219356431229511334925054065)
                ·
                  refine ⟨914517323422133501193790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219356431229511334925054065 914517323422133501193790549)
                  ·
                    refine ⟨10716999883853126967114733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 914517323422133501193790549 10716999883853126967114733)
                    ·
                      refine ⟨4018874956444922612668025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10716999883853126967114733 4018874956444922612668025)
                      ·
                        rfl

theorem cell23_7826731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].length) (baseStart_7826731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826731 prefixEnd_7826731 := by exact prefixLift 7826731
  have htrace : WordTrace (prefixWord ++ tailWord_7826731) baseStart_7826731 baseEnd_7826731 := by
    simpa [prefixWord, tailWord_7826731, baseEnd_7826731] using wordTrace_append hprefix tailTrace_7826731
  have hstable : (prefixWord ++ tailWord_7826731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826731).length < 2 ^ (prefixWord ++ tailWord_7826731).sum := by decide
  have hdescent : baseEnd_7826731 < baseStart_7826731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826748 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_7826748 : Nat := 118140960795 + 7826748 * 2 ^ 59
def prefixEnd_7826748 : Nat := 4983230072969 + 3 ^ 40 * 7826748 * 2
def baseEnd_7826748 : Nat := 4018883685616049046155447

theorem tailTrace_7826748 : CollatzResearch.WordTrace tailWord_7826748 prefixEnd_7826748 4018883685616049046155447 := by
  unfold tailWord_7826748
  simp only [CollatzResearch.WordTrace]
  refine ⟨142732475724518086491608449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190309967632690781988811265 142732475724518086491608449)
  ·
    refine ⟨107049356793388564868706337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142732475724518086491608449 107049356793388564868706337)
    ·
      refine ⟨80287017595041423651529753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107049356793388564868706337 80287017595041423651529753)
      ·
        refine ⟨60215263196281067738647315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80287017595041423651529753 60215263196281067738647315)
        ·
          refine ⟨90322894794421601607970973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60215263196281067738647315 90322894794421601607970973)
          ·
            refine ⟨33871085547908100602989115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90322894794421601607970973 33871085547908100602989115)
            ·
              refine ⟨50806628321862150904483673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33871085547908100602989115 50806628321862150904483673)
              ·
                refine ⟨38104971241396613178362755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50806628321862150904483673 38104971241396613178362755)
                ·
                  refine ⟨57157456862094919767544133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38104971241396613178362755 57157456862094919767544133)
                  ·
                    refine ⟨10717023161642797456414525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57157456862094919767544133 10717023161642797456414525)
                    ·
                      refine ⟨4018883685616049046155447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10717023161642797456414525 4018883685616049046155447)
                      ·
                        rfl

theorem cell23_7826748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_7826748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826748 prefixEnd_7826748 := by exact prefixLift 7826748
  have htrace : WordTrace (prefixWord ++ tailWord_7826748) baseStart_7826748 baseEnd_7826748 := by
    simpa [prefixWord, tailWord_7826748, baseEnd_7826748] using wordTrace_append hprefix tailTrace_7826748
  have hstable : (prefixWord ++ tailWord_7826748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826748).length < 2 ^ (prefixWord ++ tailWord_7826748).sum := by decide
  have hdescent : baseEnd_7826748 < baseStart_7826748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826828 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_7826828 : Nat := 118140960795 + 7826828 * 2 ^ 59
def prefixEnd_7826828 : Nat := 4983230072969 + 3 ^ 40 * 7826828 * 2
def baseEnd_7826828 : Nat := 1339641588022802911051693

theorem tailTrace_7826828 : CollatzResearch.WordTrace tailWord_7826828 prefixEnd_7826828 1339641588022802911051693 := by
  unfold tailWord_7826828
  simp only [CollatzResearch.WordTrace]
  refine ⟨142733934644373173323064569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190311912859164231097419425 142733934644373173323064569)
  ·
    refine ⟨107050450983279879992298427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142733934644373173323064569 107050450983279879992298427)
    ·
      refine ⟨160575676474919819988447641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107050450983279879992298427 160575676474919819988447641)
      ·
        refine ⟨120431757356189864991335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160575676474919819988447641 120431757356189864991335731)
        ·
          refine ⟨180647636034284797487003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120431757356189864991335731 180647636034284797487003597)
          ·
            refine ⟨67742863512856799057626349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180647636034284797487003597 67742863512856799057626349)
            ·
              refine ⟨25403573817321299646609881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67742863512856799057626349 25403573817321299646609881)
              ·
                refine ⟨19052680362990974734957411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25403573817321299646609881 19052680362990974734957411)
                ·
                  refine ⟨28579020544486462102436117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052680362990974734957411 28579020544486462102436117)
                  ·
                    refine ⟨1339641588022802911051693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28579020544486462102436117 1339641588022802911051693)
                    ·
                      rfl

theorem cell23_7826828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_7826828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826828 prefixEnd_7826828 := by exact prefixLift 7826828
  have htrace : WordTrace (prefixWord ++ tailWord_7826828) baseStart_7826828 baseEnd_7826828 := by
    simpa [prefixWord, tailWord_7826828, baseEnd_7826828] using wordTrace_append hprefix tailTrace_7826828
  have hstable : (prefixWord ++ tailWord_7826828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826828).length < 2 ^ (prefixWord ++ tailWord_7826828).sum := by decide
  have hdescent : baseEnd_7826828 < baseStart_7826828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826831 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_7826831 : Nat := 118140960795 + 7826831 * 2 ^ 59
def prefixEnd_7826831 : Nat := 4983230072969 + 3 ^ 40 * 7826831 * 2
def baseEnd_7826831 : Nat := 4018926304510372221417565

theorem tailTrace_7826831 : CollatzResearch.WordTrace tailWord_7826831 prefixEnd_7826831 4018926304510372221417565 := by
  unfold tailWord_7826831
  simp only [CollatzResearch.WordTrace]
  refine ⟨285467978707735478158488347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190311985805156985438992231 285467978707735478158488347)
  ·
    refine ⟨428201968061603217237732521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285467978707735478158488347 428201968061603217237732521)
    ·
      refine ⟨321151476046202412928299391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428201968061603217237732521 321151476046202412928299391)
      ·
        refine ⟨481727214069303619392449087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321151476046202412928299391 481727214069303619392449087)
        ·
          refine ⟨722590821103955429088673631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481727214069303619392449087 722590821103955429088673631)
          ·
            refine ⟨1083886231655933143633010447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722590821103955429088673631 1083886231655933143633010447)
            ·
              refine ⟨1625829347483899715449515671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083886231655933143633010447 1625829347483899715449515671)
              ·
                refine ⟨2438744021225849573174273507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625829347483899715449515671 2438744021225849573174273507)
                ·
                  refine ⟨3658116031838774359761410261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438744021225849573174273507 3658116031838774359761410261)
                  ·
                    refine ⟨85737094496221274056908053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3658116031838774359761410261 85737094496221274056908053)
                    ·
                      refine ⟨4018926304510372221417565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85737094496221274056908053 4018926304510372221417565)
                      ·
                        rfl

theorem cell23_7826831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_7826831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826831 prefixEnd_7826831 := by exact prefixLift 7826831
  have htrace : WordTrace (prefixWord ++ tailWord_7826831) baseStart_7826831 baseEnd_7826831 := by
    simpa [prefixWord, tailWord_7826831, baseEnd_7826831] using wordTrace_append hprefix tailTrace_7826831
  have hstable : (prefixWord ++ tailWord_7826831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826831).length < 2 ^ (prefixWord ++ tailWord_7826831).sum := by decide
  have hdescent : baseEnd_7826831 < baseStart_7826831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826841 : List Nat := [1, 2, 1, 2, 1, 16]
def baseStart_7826841 : Nat := 118140960795 + 7826841 * 2 ^ 59
def prefixEnd_7826841 : Nat := 4983230072969 + 3 ^ 40 * 7826841 * 2
def baseEnd_7826841 : Nat := 16538812507477025441533

theorem tailTrace_7826841 : CollatzResearch.WordTrace tailWord_7826841 prefixEnd_7826841 16538812507477025441533 := by
  unfold tailWord_7826841
  simp only [CollatzResearch.WordTrace]
  refine ⟨285468343437699249866352377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190312228958466166577568251 285468343437699249866352377)
  ·
    refine ⟨214101257578274437399764283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285468343437699249866352377 214101257578274437399764283)
    ·
      refine ⟨321151886367411656099646425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214101257578274437399764283 321151886367411656099646425)
      ·
        refine ⟨240863914775558742074734819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321151886367411656099646425 240863914775558742074734819)
        ·
          refine ⟨361295872163338113112102229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240863914775558742074734819 361295872163338113112102229)
          ·
            refine ⟨16538812507477025441533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 361295872163338113112102229 16538812507477025441533)
            ·
              rfl

theorem cell23_7826841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 16].length) (baseStart_7826841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826841 prefixEnd_7826841 := by exact prefixLift 7826841
  have htrace : WordTrace (prefixWord ++ tailWord_7826841) baseStart_7826841 baseEnd_7826841 := by
    simpa [prefixWord, tailWord_7826841, baseEnd_7826841] using wordTrace_append hprefix tailTrace_7826841
  have hstable : (prefixWord ++ tailWord_7826841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826841).length < 2 ^ (prefixWord ++ tailWord_7826841).sum := by decide
  have hdescent : baseEnd_7826841 < baseStart_7826841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826848 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_7826848 : Nat := 118140960795 + 7826848 * 2 ^ 59
def prefixEnd_7826848 : Nat := 4983230072969 + 3 ^ 40 * 7826848 * 2
def baseEnd_7826848 : Nat := 4018935033681498654904987

theorem tailTrace_7826848 : CollatzResearch.WordTrace tailWord_7826848 prefixEnd_7826848 4018935033681498654904987 := by
  unfold tailWord_7826848
  simp only [CollatzResearch.WordTrace]
  refine ⟨142734299374336945030928599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190312399165782593374571465 142734299374336945030928599)
  ·
    refine ⟨214101449061505417546392899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142734299374336945030928599 214101449061505417546392899)
    ·
      refine ⟨321152173592258126319589349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214101449061505417546392899 321152173592258126319589349)
      ·
        refine ⟨60216032548548398684923003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321152173592258126319589349 60216032548548398684923003)
        ·
          refine ⟨90324048822822598027384505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60216032548548398684923003 90324048822822598027384505)
          ·
            refine ⟨67743036617116948520538379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90324048822822598027384505 67743036617116948520538379)
            ·
              refine ⟨101614554925675422780807569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67743036617116948520538379 101614554925675422780807569)
              ·
                refine ⟨76210916194256567085605677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101614554925675422780807569 76210916194256567085605677)
                ·
                  refine ⟨28579093572846212657102129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76210916194256567085605677 28579093572846212657102129)
                  ·
                    refine ⟨21434320179634659492826597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28579093572846212657102129 21434320179634659492826597)
                    ·
                      refine ⟨4018935033681498654904987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21434320179634659492826597 4018935033681498654904987)
                      ·
                        rfl

theorem cell23_7826848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_7826848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826848 prefixEnd_7826848 := by exact prefixLift 7826848
  have htrace : WordTrace (prefixWord ++ tailWord_7826848) baseStart_7826848 baseEnd_7826848 := by
    simpa [prefixWord, tailWord_7826848, baseEnd_7826848] using wordTrace_append hprefix tailTrace_7826848
  have hstable : (prefixWord ++ tailWord_7826848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826848).length < 2 ^ (prefixWord ++ tailWord_7826848).sum := by decide
  have hdescent : baseEnd_7826848 < baseStart_7826848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826852 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_7826852 : Nat := 118140960795 + 7826852 * 2 ^ 59
def prefixEnd_7826852 : Nat := 4983230072969 + 3 ^ 40 * 7826852 * 2
def baseEnd_7826852 : Nat := 4018937087604116639254969

theorem tailTrace_7826852 : CollatzResearch.WordTrace tailWord_7826852 prefixEnd_7826852 4018937087604116639254969 := by
  unfold tailWord_7826852
  simp only [CollatzResearch.WordTrace]
  refine ⟨142734372320329699372501405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190312496427106265830001873 142734372320329699372501405)
  ·
    refine ⟨53525389620123637264688027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142734372320329699372501405 53525389620123637264688027)
    ·
      refine ⟨80288084430185455897032041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53525389620123637264688027 80288084430185455897032041)
      ·
        refine ⟨60216063322639091922774031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80288084430185455897032041 60216063322639091922774031)
        ·
          refine ⟨90324094983958637884161047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60216063322639091922774031 90324094983958637884161047)
          ·
            refine ⟨135486142475937956826241571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90324094983958637884161047 135486142475937956826241571)
            ·
              refine ⟨203229213713906935239362357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135486142475937956826241571 203229213713906935239362357)
              ·
                refine ⟨19052738785678775178690221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203229213713906935239362357 19052738785678775178690221)
                ·
                  refine ⟨7144777044629540692008833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19052738785678775178690221 7144777044629540692008833)
                  ·
                    refine ⟨5358582783472155519006625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7144777044629540692008833 5358582783472155519006625)
                    ·
                      refine ⟨4018937087604116639254969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358582783472155519006625 4018937087604116639254969)
                      ·
                        rfl

theorem cell23_7826852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_7826852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826852 prefixEnd_7826852 := by exact prefixLift 7826852
  have htrace : WordTrace (prefixWord ++ tailWord_7826852) baseStart_7826852 baseEnd_7826852 := by
    simpa [prefixWord, tailWord_7826852, baseEnd_7826852] using wordTrace_append hprefix tailTrace_7826852
  have hstable : (prefixWord ++ tailWord_7826852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826852).length < 2 ^ (prefixWord ++ tailWord_7826852).sum := by decide
  have hdescent : baseEnd_7826852 < baseStart_7826852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826855 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7826855 : Nat := 118140960795 + 7826855 * 2 ^ 59
def prefixEnd_7826855 : Nat := 4983230072969 + 3 ^ 40 * 7826855 * 2
def baseEnd_7826855 : Nat := 4018938628046080127517455

theorem tailTrace_7826855 : CollatzResearch.WordTrace tailWord_7826855 prefixEnd_7826855 4018938628046080127517455 := by
  unfold tailWord_7826855
  simp only [CollatzResearch.WordTrace]
  refine ⟨285468854059648530257362019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190312569373099020171574679 285468854059648530257362019)
  ·
    refine ⟨428203281089472795386043029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285468854059648530257362019 428203281089472795386043029)
    ·
      refine ⟨20072028801069037283720767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 428203281089472795386043029 20072028801069037283720767)
      ·
        refine ⟨30108043201603555925581151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20072028801069037283720767 30108043201603555925581151)
        ·
          refine ⟨45162064802405333888371727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30108043201603555925581151 45162064802405333888371727)
          ·
            refine ⟨67743097203608000832557591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45162064802405333888371727 67743097203608000832557591)
            ·
              refine ⟨101614645805412001248836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67743097203608000832557591 101614645805412001248836387)
              ·
                refine ⟨152421968708118001873254581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101614645805412001248836387 152421968708118001873254581)
                ·
                  refine ⟨14289559566386062675617617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152421968708118001873254581 14289559566386062675617617)
                  ·
                    refine ⟨10717169674789547006713213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14289559566386062675617617 10717169674789547006713213)
                    ·
                      refine ⟨4018938628046080127517455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10717169674789547006713213 4018938628046080127517455)
                      ·
                        rfl

theorem cell23_7826855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7826855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826855 prefixEnd_7826855 := by exact prefixLift 7826855
  have htrace : WordTrace (prefixWord ++ tailWord_7826855) baseStart_7826855 baseEnd_7826855 := by
    simpa [prefixWord, tailWord_7826855, baseEnd_7826855] using wordTrace_append hprefix tailTrace_7826855
  have hstable : (prefixWord ++ tailWord_7826855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826855).length < 2 ^ (prefixWord ++ tailWord_7826855).sum := by decide
  have hdescent : baseEnd_7826855 < baseStart_7826855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826865 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7826865 : Nat := 118140960795 + 7826865 * 2 ^ 59
def prefixEnd_7826865 : Nat := 4983230072969 + 3 ^ 40 * 7826865 * 2
def baseEnd_7826865 : Nat := 4018943762852625088392409

theorem tailTrace_7826865 : CollatzResearch.WordTrace tailWord_7826865 prefixEnd_7826865 4018943762852625088392409 := by
  unfold tailWord_7826865
  simp only [CollatzResearch.WordTrace]
  refine ⟨285469218789612301965226049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190312812526408201310150699 285469218789612301965226049)
  ·
    refine ⟨214101914092209226473919537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285469218789612301965226049 214101914092209226473919537)
    ·
      refine ⟨160576435569156919855439653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214101914092209226473919537 160576435569156919855439653)
      ·
        refine ⟨30108081669216922472894935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160576435569156919855439653 30108081669216922472894935)
        ·
          refine ⟨45162122503825383709342403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30108081669216922472894935 45162122503825383709342403)
          ·
            refine ⟨67743183755738075564013605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45162122503825383709342403 67743183755738075564013605)
            ·
              refine ⟨12701846954200889168252551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67743183755738075564013605 12701846954200889168252551)
              ·
                refine ⟨19052770431301333752378827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12701846954200889168252551 19052770431301333752378827)
                ·
                  refine ⟨28579155646952000628568241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052770431301333752378827 28579155646952000628568241)
                  ·
                    refine ⟨21434366735214000471426181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28579155646952000628568241 21434366735214000471426181)
                    ·
                      refine ⟨4018943762852625088392409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21434366735214000471426181 4018943762852625088392409)
                      ·
                        rfl

theorem cell23_7826865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7826865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826865 prefixEnd_7826865 := by exact prefixLift 7826865
  have htrace : WordTrace (prefixWord ++ tailWord_7826865) baseStart_7826865 baseEnd_7826865 := by
    simpa [prefixWord, tailWord_7826865, baseEnd_7826865] using wordTrace_append hprefix tailTrace_7826865
  have hstable : (prefixWord ++ tailWord_7826865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826865).length < 2 ^ (prefixWord ++ tailWord_7826865).sum := by decide
  have hdescent : baseEnd_7826865 < baseStart_7826865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826869 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_7826869 : Nat := 118140960795 + 7826869 * 2 ^ 59
def prefixEnd_7826869 : Nat := 4983230072969 + 3 ^ 40 * 7826869 * 2
def baseEnd_7826869 : Nat := 4018945816775243072742391

theorem tailTrace_7826869 : CollatzResearch.WordTrace tailWord_7826869 prefixEnd_7826869 4018945816775243072742391 := by
  unfold tailWord_7826869
  simp only [CollatzResearch.WordTrace]
  refine ⟨285469364681597810648371661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190312909787731873765581107 285469364681597810648371661)
  ·
    refine ⟨107051011755599178993139373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285469364681597810648371661 107051011755599178993139373)
    ·
      refine ⟨40144129408349692122427265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107051011755599178993139373 40144129408349692122427265)
      ·
        refine ⟨30108097056262269091820449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40144129408349692122427265 30108097056262269091820449)
        ·
          refine ⟨22581072792196701818865337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30108097056262269091820449 22581072792196701818865337)
          ·
            refine ⟨16935804594147526364149003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22581072792196701818865337 16935804594147526364149003)
            ·
              refine ⟨25403706891221289546223505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16935804594147526364149003 25403706891221289546223505)
              ·
                refine ⟨19052780168415967159667629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25403706891221289546223505 19052780168415967159667629)
                ·
                  refine ⟨7144792563155987684875361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19052780168415967159667629 7144792563155987684875361)
                  ·
                    refine ⟨5358594422366990763656521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7144792563155987684875361 5358594422366990763656521)
                    ·
                      refine ⟨4018945816775243072742391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358594422366990763656521 4018945816775243072742391)
                      ·
                        rfl

theorem cell23_7826869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_7826869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826869 prefixEnd_7826869 := by exact prefixLift 7826869
  have htrace : WordTrace (prefixWord ++ tailWord_7826869) baseStart_7826869 baseEnd_7826869 := by
    simpa [prefixWord, tailWord_7826869, baseEnd_7826869] using wordTrace_append hprefix tailTrace_7826869
  have hstable : (prefixWord ++ tailWord_7826869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826869).length < 2 ^ (prefixWord ++ tailWord_7826869).sum := by decide
  have hdescent : baseEnd_7826869 < baseStart_7826869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826929 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_7826929 : Nat := 118140960795 + 7826929 * 2 ^ 59
def prefixEnd_7826929 : Nat := 4983230072969 + 3 ^ 40 * 7826929 * 2
def baseEnd_7826929 : Nat := 4018976625614512837992115

theorem tailTrace_7826929 : CollatzResearch.WordTrace tailWord_7826929 prefixEnd_7826929 4018976625614512837992115 := by
  unfold tailWord_7826929
  simp only [CollatzResearch.WordTrace]
  refine ⟨285471553061380440895555841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190314368707586960597037227 285471553061380440895555841)
  ·
    refine ⟨214103664796035330671666881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285471553061380440895555841 214103664796035330671666881)
    ·
      refine ⟨160577748597026498003750161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214103664796035330671666881 160577748597026498003750161)
      ·
        refine ⟨120433311447769873502812621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160577748597026498003750161 120433311447769873502812621)
        ·
          refine ⟨45162491792913702563554733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120433311447769873502812621 45162491792913702563554733)
          ·
            refine ⟨16935934422342638461333025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45162491792913702563554733 16935934422342638461333025)
            ·
              refine ⟨12701950816756978845999769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16935934422342638461333025 12701950816756978845999769)
              ·
                refine ⟨9526463112567734134499827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12701950816756978845999769 9526463112567734134499827)
                ·
                  refine ⟨14289694668851601201749741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526463112567734134499827 14289694668851601201749741)
                  ·
                    refine ⟨5358635500819350450656153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14289694668851601201749741 5358635500819350450656153)
                    ·
                      refine ⟨4018976625614512837992115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358635500819350450656153 4018976625614512837992115)
                      ·
                        rfl

theorem cell23_7826929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_7826929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826929 prefixEnd_7826929 := by exact prefixLift 7826929
  have htrace : WordTrace (prefixWord ++ tailWord_7826929) baseStart_7826929 baseEnd_7826929 := by
    simpa [prefixWord, tailWord_7826929, baseEnd_7826929] using wordTrace_append hprefix tailTrace_7826929
  have hstable : (prefixWord ++ tailWord_7826929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826929).length < 2 ^ (prefixWord ++ tailWord_7826929).sum := by decide
  have hdescent : baseEnd_7826929 < baseStart_7826929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826946 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7826946 : Nat := 118140960795 + 7826946 * 2 ^ 59
def prefixEnd_7826946 : Nat := 4983230072969 + 3 ^ 40 * 7826946 * 2
def baseEnd_7826946 : Nat := 4018985354785639271479537

theorem tailTrace_7826946 : CollatzResearch.WordTrace tailWord_7826946 prefixEnd_7826946 4018985354785639271479537 := by
  unfold tailWord_7826946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71368043275579713199731173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190314782068212568532616461 71368043275579713199731173)
  ·
    refine ⟨13381508114171196224949595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71368043275579713199731173 13381508114171196224949595)
    ·
      refine ⟨20072262171256794337424393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13381508114171196224949595 20072262171256794337424393)
      ·
        refine ⟨15054196628442595753068295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20072262171256794337424393 15054196628442595753068295)
        ·
          refine ⟨22581294942663893629602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054196628442595753068295 22581294942663893629602443)
          ·
            refine ⟨33871942413995840444403665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581294942663893629602443 33871942413995840444403665)
            ·
              refine ⟨25403956810496880333302749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33871942413995840444403665 25403956810496880333302749)
              ·
                refine ⟨9526483803936330124988531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25403956810496880333302749 9526483803936330124988531)
                ·
                  refine ⟨14289725705904495187482797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526483803936330124988531 14289725705904495187482797)
                  ·
                    refine ⟨5358647139714185695306049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14289725705904495187482797 5358647139714185695306049)
                    ·
                      refine ⟨4018985354785639271479537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358647139714185695306049 4018985354785639271479537)
                      ·
                        rfl

theorem cell23_7826946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7826946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826946 prefixEnd_7826946 := by exact prefixLift 7826946
  have htrace : WordTrace (prefixWord ++ tailWord_7826946) baseStart_7826946 baseEnd_7826946 := by
    simpa [prefixWord, tailWord_7826946, baseEnd_7826946] using wordTrace_append hprefix tailTrace_7826946
  have hstable : (prefixWord ++ tailWord_7826946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826946).length < 2 ^ (prefixWord ++ tailWord_7826946).sum := by decide
  have hdescent : baseEnd_7826946 < baseStart_7826946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826965 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 7]
def baseStart_7826965 : Nat := 118140960795 + 7826965 * 2 ^ 59
def prefixEnd_7826965 : Nat := 4983230072969 + 3 ^ 40 * 7826965 * 2
def baseEnd_7826965 : Nat := 446555012324230521904661

theorem tailTrace_7826965 : CollatzResearch.WordTrace tailWord_7826965 prefixEnd_7826965 446555012324230521904661 := by
  unfold tailWord_7826965
  simp only [CollatzResearch.WordTrace]
  refine ⟨285472866089250019043866349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190315244059500012695910899 285472866089250019043866349)
  ·
    refine ⟨107052324783468757141449881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285472866089250019043866349 107052324783468757141449881)
    ·
      refine ⟨80289243587601567856087411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107052324783468757141449881 80289243587601567856087411)
      ·
        refine ⟨120433865381402351784131117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80289243587601567856087411 120433865381402351784131117)
        ·
          refine ⟨45162699518025881919049169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120433865381402351784131117 45162699518025881919049169)
          ·
            refine ⟨33872024638519411439286877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45162699518025881919049169 33872024638519411439286877)
            ·
              refine ⟨12702009239444779289732579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33872024638519411439286877 12702009239444779289732579)
              ·
                refine ⟨19053013859167168934598869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702009239444779289732579 19053013859167168934598869)
                ·
                  refine ⟨446555012324230521904661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19053013859167168934598869 446555012324230521904661)
                  ·
                    rfl

theorem cell23_7826965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_7826965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826965 prefixEnd_7826965 := by exact prefixLift 7826965
  have htrace : WordTrace (prefixWord ++ tailWord_7826965) baseStart_7826965 baseEnd_7826965 := by
    simpa [prefixWord, tailWord_7826965, baseEnd_7826965] using wordTrace_append hprefix tailTrace_7826965
  have hstable : (prefixWord ++ tailWord_7826965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826965).length < 2 ^ (prefixWord ++ tailWord_7826965).sum := by decide
  have hdescent : baseEnd_7826965 < baseStart_7826965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826975 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_7826975 : Nat := 118140960795 + 7826975 * 2 ^ 59
def prefixEnd_7826975 : Nat := 4983230072969 + 3 ^ 40 * 7826975 * 2
def baseEnd_7826975 : Nat := 4019000245724619658016903

theorem tailTrace_7826975 : CollatzResearch.WordTrace tailWord_7826975 prefixEnd_7826975 4019000245724619658016903 := by
  unfold tailWord_7826975
  simp only [CollatzResearch.WordTrace]
  refine ⟨285473230819213790751730379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190315487212809193834486919 285473230819213790751730379)
  ·
    refine ⟨428209846228820686127595569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285473230819213790751730379 428209846228820686127595569)
    ·
      refine ⟨321157384671615514595696677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428209846228820686127595569 321157384671615514595696677)
      ·
        refine ⟨60217009625927908986693127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321157384671615514595696677 60217009625927908986693127)
        ·
          refine ⟨90325514438891863480039691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60217009625927908986693127 90325514438891863480039691)
          ·
            refine ⟨135488271658337795220059537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90325514438891863480039691 135488271658337795220059537)
            ·
              refine ⟨101616203743753346415044653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135488271658337795220059537 101616203743753346415044653)
              ·
                refine ⟨38106076403907504905641745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101616203743753346415044653 38106076403907504905641745)
                ·
                  refine ⟨28579557302930628679231309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38106076403907504905641745 28579557302930628679231309)
                  ·
                    refine ⟨10717333988598985754711741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28579557302930628679231309 10717333988598985754711741)
                    ·
                      refine ⟨4019000245724619658016903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10717333988598985754711741 4019000245724619658016903)
                      ·
                        rfl

theorem cell23_7826975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_7826975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826975 prefixEnd_7826975 := by exact prefixLift 7826975
  have htrace : WordTrace (prefixWord ++ tailWord_7826975) baseStart_7826975 baseEnd_7826975 := by
    simpa [prefixWord, tailWord_7826975, baseEnd_7826975] using wordTrace_append hprefix tailTrace_7826975
  have hstable : (prefixWord ++ tailWord_7826975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826975).length < 2 ^ (prefixWord ++ tailWord_7826975).sum := by decide
  have hdescent : baseEnd_7826975 < baseStart_7826975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826976 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7826976 : Nat := 118140960795 + 7826976 * 2 ^ 59
def prefixEnd_7826976 : Nat := 4983230072969 + 3 ^ 40 * 7826976 * 2
def baseEnd_7826976 : Nat := 4019000759205274154104399

theorem tailTrace_7826976 : CollatzResearch.WordTrace tailWord_7826976 prefixEnd_7826976 4019000759205274154104399 := by
  unfold tailWord_7826976
  simp only [CollatzResearch.WordTrace]
  refine ⟨142736633646105083961258391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190315511528140111948344521 142736633646105083961258391)
  ·
    refine ⟨214104950469157625941887587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142736633646105083961258391 214104950469157625941887587)
    ·
      refine ⟨321157425703736438912831381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214104950469157625941887587 321157425703736438912831381)
      ·
        refine ⟨15054254329862645574038971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321157425703736438912831381 15054254329862645574038971)
        ·
          refine ⟨22581381494793968361058457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054254329862645574038971 22581381494793968361058457)
          ·
            refine ⟨16936036121095476270793843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22581381494793968361058457 16936036121095476270793843)
            ·
              refine ⟨25404054181643214406190765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936036121095476270793843 25404054181643214406190765)
              ·
                refine ⟨9526520318116205402321537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25404054181643214406190765 9526520318116205402321537)
                ·
                  refine ⟨7144890238587154051741153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526520318116205402321537 7144890238587154051741153)
                  ·
                    refine ⟨5358667678940365538805865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7144890238587154051741153 5358667678940365538805865)
                    ·
                      refine ⟨4019000759205274154104399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358667678940365538805865 4019000759205274154104399)
                      ·
                        rfl

theorem cell23_7826976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7826976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826976 prefixEnd_7826976 := by exact prefixLift 7826976
  have htrace : WordTrace (prefixWord ++ tailWord_7826976) baseStart_7826976 baseEnd_7826976 := by
    simpa [prefixWord, tailWord_7826976, baseEnd_7826976] using wordTrace_append hprefix tailTrace_7826976
  have hstable : (prefixWord ++ tailWord_7826976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826976).length < 2 ^ (prefixWord ++ tailWord_7826976).sum := by decide
  have hdescent : baseEnd_7826976 < baseStart_7826976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7826995 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 2, 5]
def baseStart_7826995 : Nat := 118140960795 + 7826995 * 2 ^ 59
def prefixEnd_7826995 : Nat := 4983230072969 + 3 ^ 40 * 7826995 * 2
def baseEnd_7826995 : Nat := 1339670171779236526588937

theorem tailTrace_7826995 : CollatzResearch.WordTrace tailWord_7826995 prefixEnd_7826995 1339670171779236526588937 := by
  unfold tailWord_7826995
  simp only [CollatzResearch.WordTrace]
  refine ⟨285473960279141334167458439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190315973519427556111638959 285473960279141334167458439)
  ·
    refine ⟨428210940418712001251187659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285473960279141334167458439 428210940418712001251187659)
    ·
      refine ⟨642316410628068001876781489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428210940418712001251187659 642316410628068001876781489)
      ·
        refine ⟨481737307971051001407586117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642316410628068001876781489 481737307971051001407586117)
        ·
          refine ⟨90325745244572062763922397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481737307971051001407586117 90325745244572062763922397)
          ·
            refine ⟨33872154466714523536470899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90325745244572062763922397 33872154466714523536470899)
            ·
              refine ⟨50808231700071785304706349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33872154466714523536470899 50808231700071785304706349)
              ·
                refine ⟨19053086887526919489264881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50808231700071785304706349 19053086887526919489264881)
                ·
                  refine ⟨14289815165645189616948661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19053086887526919489264881 14289815165645189616948661)
                  ·
                    refine ⟨1339670171779236526588937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14289815165645189616948661 1339670171779236526588937)
                    ·
                      rfl

theorem cell23_7826995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].length) (baseStart_7826995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7826995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7826995 prefixEnd_7826995 := by exact prefixLift 7826995
  have htrace : WordTrace (prefixWord ++ tailWord_7826995) baseStart_7826995 baseEnd_7826995 := by
    simpa [prefixWord, tailWord_7826995, baseEnd_7826995] using wordTrace_append hprefix tailTrace_7826995
  have hstable : (prefixWord ++ tailWord_7826995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7826995).length < 2 ^ (prefixWord ++ tailWord_7826995).sum := by decide
  have hdescent : baseEnd_7826995 < baseStart_7826995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7826995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827062 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7827062 : Nat := 118140960795 + 7827062 * 2 ^ 59
def prefixEnd_7827062 : Nat := 4983230072969 + 3 ^ 40 * 7827062 * 2
def baseEnd_7827062 : Nat := 4019044918541560817629003

theorem tailTrace_7827062 : CollatzResearch.WordTrace tailWord_7827062 prefixEnd_7827062 4019044918541560817629003 := by
  unfold tailWord_7827062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842275248118662788134215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190317602646599069740098293 17842275248118662788134215)
  ·
    refine ⟨26763412872177994182201323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842275248118662788134215 26763412872177994182201323)
    ·
      refine ⟨40145119308266991273301985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26763412872177994182201323 40145119308266991273301985)
      ·
        refine ⟨30108839481200243454976489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40145119308266991273301985 30108839481200243454976489)
        ·
          refine ⟨22581629610900182591232367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30108839481200243454976489 22581629610900182591232367)
          ·
            refine ⟨33872444416350273886848551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581629610900182591232367 33872444416350273886848551)
            ·
              refine ⟨50808666624525410830272827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33872444416350273886848551 50808666624525410830272827)
              ·
                refine ⟨76212999936788116245409241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50808666624525410830272827 76212999936788116245409241)
                ·
                  refine ⟨57159749952591087184056931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76212999936788116245409241 57159749952591087184056931)
                  ·
                    refine ⟨85739624928886630776085397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57159749952591087184056931 85739624928886630776085397)
                    ·
                      refine ⟨4019044918541560817629003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85739624928886630776085397 4019044918541560817629003)
                      ·
                        rfl

theorem cell23_7827062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7827062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827062 prefixEnd_7827062 := by exact prefixLift 7827062
  have htrace : WordTrace (prefixWord ++ tailWord_7827062) baseStart_7827062 baseEnd_7827062 := by
    simpa [prefixWord, tailWord_7827062, baseEnd_7827062] using wordTrace_append hprefix tailTrace_7827062
  have hstable : (prefixWord ++ tailWord_7827062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827062).length < 2 ^ (prefixWord ++ tailWord_7827062).sum := by decide
  have hdescent : baseEnd_7827062 < baseStart_7827062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827133 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7827133 : Nat := 118140960795 + 7827133 * 2 ^ 59
def prefixEnd_7827133 : Nat := 4983230072969 + 3 ^ 40 * 7827133 * 2
def baseEnd_7827133 : Nat := 4019081375668030039841177

theorem tailTrace_7827133 : CollatzResearch.WordTrace tailWord_7827133 prefixEnd_7827133 4019081375668030039841177 := by
  unfold tailWord_7827133
  simp only [CollatzResearch.WordTrace]
  refine ⟨285478993552641383735982053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190319329035094255823988035 285478993552641383735982053)
  ·
    refine ⟨53527311291120259450496635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285478993552641383735982053 53527311291120259450496635)
    ·
      refine ⟨80290966936680389175744953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53527311291120259450496635 80290966936680389175744953)
      ·
        refine ⟨60218225202510291881808715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80290966936680389175744953 60218225202510291881808715)
        ·
          refine ⟨90327337803765437822713073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60218225202510291881808715 90327337803765437822713073)
          ·
            refine ⟨67745503352824078367034805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90327337803765437822713073 67745503352824078367034805)
            ·
              refine ⟨6351140939327257346909513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67745503352824078367034805 6351140939327257346909513)
              ·
                refine ⟨4763355704495443010182135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351140939327257346909513 4763355704495443010182135)
                ·
                  refine ⟨7145033556743164515273203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763355704495443010182135 7145033556743164515273203)
                  ·
                    refine ⟨10717550335114746772909805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145033556743164515273203 10717550335114746772909805)
                    ·
                      refine ⟨4019081375668030039841177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10717550335114746772909805 4019081375668030039841177)
                      ·
                        rfl

theorem cell23_7827133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7827133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827133 prefixEnd_7827133 := by exact prefixLift 7827133
  have htrace : WordTrace (prefixWord ++ tailWord_7827133) baseStart_7827133 baseEnd_7827133 := by
    simpa [prefixWord, tailWord_7827133, baseEnd_7827133] using wordTrace_append hprefix tailTrace_7827133
  have hstable : (prefixWord ++ tailWord_7827133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827133).length < 2 ^ (prefixWord ++ tailWord_7827133).sum := by decide
  have hdescent : baseEnd_7827133 < baseStart_7827133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827135 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_7827135 : Nat := 118140960795 + 7827135 * 2 ^ 59
def prefixEnd_7827135 : Nat := 4983230072969 + 3 ^ 40 * 7827135 * 2
def baseEnd_7827135 : Nat := 4019082402629339032016167

theorem tailTrace_7827135 : CollatzResearch.WordTrace tailWord_7827135 prefixEnd_7827135 4019082402629339032016167 := by
  unfold tailWord_7827135
  simp only [CollatzResearch.WordTrace]
  refine ⟨285479066498634138077554859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190319377665756092051703239 285479066498634138077554859)
  ·
    refine ⟨428218599747951207116332289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285479066498634138077554859 428218599747951207116332289)
    ·
      refine ⟨321163949810963405337249217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428218599747951207116332289 321163949810963405337249217)
      ·
        refine ⟨240872962358222554002936913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321163949810963405337249217 240872962358222554002936913)
        ·
          refine ⟨180654721768666915502202685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240872962358222554002936913 180654721768666915502202685)
          ·
            refine ⟨67745520663250093313326007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180654721768666915502202685 67745520663250093313326007)
            ·
              refine ⟨101618280994875139969989011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67745520663250093313326007 101618280994875139969989011)
              ·
                refine ⟨152427421492312709954983517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101618280994875139969989011 152427421492312709954983517)
                ·
                  refine ⟨57160283059617266233118819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152427421492312709954983517 57160283059617266233118819)
                  ·
                    refine ⟨85740424589425899349678229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57160283059617266233118819 85740424589425899349678229)
                    ·
                      refine ⟨4019082402629339032016167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85740424589425899349678229 4019082402629339032016167)
                      ·
                        rfl

theorem cell23_7827135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_7827135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827135 prefixEnd_7827135 := by exact prefixLift 7827135
  have htrace : WordTrace (prefixWord ++ tailWord_7827135) baseStart_7827135 baseEnd_7827135 := by
    simpa [prefixWord, tailWord_7827135, baseEnd_7827135] using wordTrace_append hprefix tailTrace_7827135
  have hstable : (prefixWord ++ tailWord_7827135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827135).length < 2 ^ (prefixWord ++ tailWord_7827135).sum := by decide
  have hdescent : baseEnd_7827135 < baseStart_7827135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827156 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7827156 : Nat := 118140960795 + 7827156 * 2 ^ 59
def prefixEnd_7827156 : Nat := 4983230072969 + 3 ^ 40 * 7827156 * 2
def baseEnd_7827156 : Nat := 4019093185723083449853571

theorem tailTrace_7827156 : CollatzResearch.WordTrace tailWord_7827156 prefixEnd_7827156 4019093185723083449853571 := by
  unfold tailWord_7827156
  simp only [CollatzResearch.WordTrace]
  refine ⟨142739916215779029332034661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190319888287705372442712881 142739916215779029332034661)
  ·
    refine ⟨26763734290458567999756499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142739916215779029332034661 26763734290458567999756499)
    ·
      refine ⟨40145601435687851999634749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26763734290458567999756499 40145601435687851999634749)
      ·
        refine ⟨15054600538382944499863031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40145601435687851999634749 15054600538382944499863031)
        ·
          refine ⟨22581900807574416749794547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054600538382944499863031 22581900807574416749794547)
          ·
            refine ⟨33872851211361625124691821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581900807574416749794547 33872851211361625124691821)
            ·
              refine ⟨12702319204260609421759433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33872851211361625124691821 12702319204260609421759433)
              ·
                refine ⟨9526739403195457066319575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702319204260609421759433 9526739403195457066319575)
                ·
                  refine ⟨14290109104793185599479363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526739403195457066319575 14290109104793185599479363)
                  ·
                    refine ⟨21435163657189778399219045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14290109104793185599479363 21435163657189778399219045)
                    ·
                      refine ⟨4019093185723083449853571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21435163657189778399219045 4019093185723083449853571)
                      ·
                        rfl

theorem cell23_7827156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7827156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827156 prefixEnd_7827156 := by exact prefixLift 7827156
  have htrace : WordTrace (prefixWord ++ tailWord_7827156) baseStart_7827156 baseEnd_7827156 := by
    simpa [prefixWord, tailWord_7827156, baseEnd_7827156] using wordTrace_append hprefix tailTrace_7827156
  have hstable : (prefixWord ++ tailWord_7827156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827156).length < 2 ^ (prefixWord ++ tailWord_7827156).sum := by decide
  have hdescent : baseEnd_7827156 < baseStart_7827156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827169 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_7827169 : Nat := 118140960795 + 7827169 * 2 ^ 59
def prefixEnd_7827169 : Nat := 4983230072969 + 3 ^ 40 * 7827169 * 2
def baseEnd_7827169 : Nat := 4019099860971591898991011

theorem tailTrace_7827169 : CollatzResearch.WordTrace tailWord_7827169 prefixEnd_7827169 4019099860971591898991011 := by
  unfold tailWord_7827169
  simp only [CollatzResearch.WordTrace]
  refine ⟨285480306580510961884292561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190320204387007307922861707 285480306580510961884292561)
  ·
    refine ⟨214110229935383221413219421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285480306580510961884292561 214110229935383221413219421)
    ·
      refine ⟨80291336225768708029957283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214110229935383221413219421 80291336225768708029957283)
      ·
        refine ⟨120437004338653062044935925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80291336225768708029957283 120437004338653062044935925)
        ·
          refine ⟨11290969156748724566712743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120437004338653062044935925 11290969156748724566712743)
          ·
            refine ⟨16936453735123086850069115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290969156748724566712743 16936453735123086850069115)
            ·
              refine ⟨25404680602684630275103673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936453735123086850069115 25404680602684630275103673)
              ·
                refine ⟨19053510452013472706327755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25404680602684630275103673 19053510452013472706327755)
                ·
                  refine ⟨28580265678020209059491633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19053510452013472706327755 28580265678020209059491633)
                  ·
                    refine ⟨21435199258515156794618725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28580265678020209059491633 21435199258515156794618725)
                    ·
                      refine ⟨4019099860971591898991011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21435199258515156794618725 4019099860971591898991011)
                      ·
                        rfl

theorem cell23_7827169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_7827169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827169 prefixEnd_7827169 := by exact prefixLift 7827169
  have htrace : WordTrace (prefixWord ++ tailWord_7827169) baseStart_7827169 baseEnd_7827169 := by
    simpa [prefixWord, tailWord_7827169, baseEnd_7827169] using wordTrace_append hprefix tailTrace_7827169
  have hstable : (prefixWord ++ tailWord_7827169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827169).length < 2 ^ (prefixWord ++ tailWord_7827169).sum := by decide
  have hdescent : baseEnd_7827169 < baseStart_7827169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827173 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7827173 : Nat := 118140960795 + 7827173 * 2 ^ 59
def prefixEnd_7827173 : Nat := 4983230072969 + 3 ^ 40 * 7827173 * 2
def baseEnd_7827173 : Nat := 4019101914894209883340993

theorem tailTrace_7827173 : CollatzResearch.WordTrace tailWord_7827173 prefixEnd_7827173 4019101914894209883340993 := by
  unfold tailWord_7827173
  simp only [CollatzResearch.WordTrace]
  refine ⟨285480452472496470567438173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190320301648330980378292115 285480452472496470567438173)
  ·
    refine ⟨107055169677186176462789315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285480452472496470567438173 107055169677186176462789315)
    ·
      refine ⟨160582754515779264694183973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107055169677186176462789315 160582754515779264694183973)
      ·
        refine ⟨30109266471708612130159495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160582754515779264694183973 30109266471708612130159495)
        ·
          refine ⟨45163899707562918195239243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30109266471708612130159495 45163899707562918195239243)
          ·
            refine ⟨67745849561344377292858865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45163899707562918195239243 67745849561344377292858865)
            ·
              refine ⟨50809387171008282969644149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67745849561344377292858865 50809387171008282969644149)
              ·
                refine ⟨4763380047282026528404139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50809387171008282969644149 4763380047282026528404139)
                ·
                  refine ⟨7145070070923039792606209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763380047282026528404139 7145070070923039792606209)
                  ·
                    refine ⟨5358802553192279844454657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145070070923039792606209 5358802553192279844454657)
                    ·
                      refine ⟨4019101914894209883340993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358802553192279844454657 4019101914894209883340993)
                      ·
                        rfl

theorem cell23_7827173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7827173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827173 prefixEnd_7827173 := by exact prefixLift 7827173
  have htrace : WordTrace (prefixWord ++ tailWord_7827173) baseStart_7827173 baseEnd_7827173 := by
    simpa [prefixWord, tailWord_7827173, baseEnd_7827173] using wordTrace_append hprefix tailTrace_7827173
  have hstable : (prefixWord ++ tailWord_7827173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827173).length < 2 ^ (prefixWord ++ tailWord_7827173).sum := by decide
  have hdescent : baseEnd_7827173 < baseStart_7827173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827190 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7827190 : Nat := 118140960795 + 7827190 * 2 ^ 59
def prefixEnd_7827190 : Nat := 4983230072969 + 3 ^ 40 * 7827190 * 2
def baseEnd_7827190 : Nat := 4019110644065336316828415

theorem tailTrace_7827190 : CollatzResearch.WordTrace tailWord_7827190 prefixEnd_7827190 4019110644065336316828415 := by
  unfold tailWord_7827190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842567032089680154425439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190320715008956588313871349 17842567032089680154425439)
  ·
    refine ⟨26763850548134520231638159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842567032089680154425439 26763850548134520231638159)
    ·
      refine ⟨40145775822201780347457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26763850548134520231638159 40145775822201780347457239)
      ·
        refine ⟨60218663733302670521185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40145775822201780347457239 60218663733302670521185859)
        ·
          refine ⟨90327995599954005781778789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60218663733302670521185859 90327995599954005781778789)
          ·
            refine ⟨16936499174991376084083523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90327995599954005781778789 16936499174991376084083523)
            ·
              refine ⟨25404748762487064126125285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936499174991376084083523 25404748762487064126125285)
              ·
                refine ⟨4763390392966324523648491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25404748762487064126125285 4763390392966324523648491)
                ·
                  refine ⟨7145085589449486785472737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763390392966324523648491 7145085589449486785472737)
                  ·
                    refine ⟨5358814192087115089104553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145085589449486785472737 5358814192087115089104553)
                    ·
                      refine ⟨4019110644065336316828415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358814192087115089104553 4019110644065336316828415)
                      ·
                        rfl

theorem cell23_7827190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7827190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827190 prefixEnd_7827190 := by exact prefixLift 7827190
  have htrace : WordTrace (prefixWord ++ tailWord_7827190) baseStart_7827190 baseEnd_7827190 := by
    simpa [prefixWord, tailWord_7827190, baseEnd_7827190] using wordTrace_append hprefix tailTrace_7827190
  have hstable : (prefixWord ++ tailWord_7827190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827190).length < 2 ^ (prefixWord ++ tailWord_7827190).sum := by decide
  have hdescent : baseEnd_7827190 < baseStart_7827190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827199 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 3, 3, 2]
def baseStart_7827199 : Nat := 118140960795 + 7827199 * 2 ^ 59
def prefixEnd_7827199 : Nat := 4983230072969 + 3 ^ 40 * 7827199 * 2
def baseEnd_7827199 : Nat := 4019115265391226781615873

theorem tailTrace_7827199 : CollatzResearch.WordTrace tailWord_7827199 prefixEnd_7827199 4019115265391226781615873 := by
  unfold tailWord_7827199
  simp only [CollatzResearch.WordTrace]
  refine ⟨285481400770402277007884651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190320933846934851338589767 285481400770402277007884651)
  ·
    refine ⟨428222101155603415511826977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285481400770402277007884651 428222101155603415511826977)
    ·
      refine ⟨321166575866702561633870233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428222101155603415511826977 321166575866702561633870233)
      ·
        refine ⟨240874931900026921225402675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321166575866702561633870233 240874931900026921225402675)
        ·
          refine ⟨361312397850040381838104013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240874931900026921225402675 361312397850040381838104013)
          ·
            refine ⟨135492149193765143189289005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361312397850040381838104013 135492149193765143189289005)
            ·
              refine ⟨50809555947661928695983377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135492149193765143189289005 50809555947661928695983377)
              ·
                refine ⟨38107166960746446521987533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50809555947661928695983377 38107166960746446521987533)
                ·
                  refine ⟨14290187610279917445745325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38107166960746446521987533 14290187610279917445745325)
                  ·
                    refine ⟨5358820353854969042154497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14290187610279917445745325 5358820353854969042154497)
                    ·
                      refine ⟨4019115265391226781615873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358820353854969042154497 4019115265391226781615873)
                      ·
                        rfl

theorem cell23_7827199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_7827199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827199 prefixEnd_7827199 := by exact prefixLift 7827199
  have htrace : WordTrace (prefixWord ++ tailWord_7827199) baseStart_7827199 baseEnd_7827199 := by
    simpa [prefixWord, tailWord_7827199, baseEnd_7827199] using wordTrace_append hprefix tailTrace_7827199
  have hstable : (prefixWord ++ tailWord_7827199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827199).length < 2 ^ (prefixWord ++ tailWord_7827199).sum := by decide
  have hdescent : baseEnd_7827199 < baseStart_7827199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827232 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7827232 : Nat := 118140960795 + 7827232 * 2 ^ 59
def prefixEnd_7827232 : Nat := 4983230072969 + 3 ^ 40 * 7827232 * 2
def baseEnd_7827232 : Nat := 4019132210252825152503221

theorem tailTrace_7827232 : CollatzResearch.WordTrace tailWord_7827232 prefixEnd_7827232 4019132210252825152503221 := by
  unfold tailWord_7827232
  simp only [CollatzResearch.WordTrace]
  refine ⟨142741302189641361821917975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190321736252855149095890633 142741302189641361821917975)
  ·
    refine ⟨214111953284462042732876963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142741302189641361821917975 214111953284462042732876963)
    ·
      refine ⟨321167929926693064099315445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214111953284462042732876963 321167929926693064099315445)
      ·
        refine ⟨30109493430627474759310823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321167929926693064099315445 30109493430627474759310823)
        ·
          refine ⟨45164240145941212138966235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30109493430627474759310823 45164240145941212138966235)
          ·
            refine ⟨67746360218911818208449353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45164240145941212138966235 67746360218911818208449353)
            ·
              refine ⟨50809770164183863656337015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67746360218911818208449353 50809770164183863656337015)
              ·
                refine ⟨76214655246275795484505523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50809770164183863656337015 76214655246275795484505523)
                ·
                  refine ⟨114321982869413693226758285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76214655246275795484505523 114321982869413693226758285)
                  ·
                    refine ⟨42870743576030134960034357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114321982869413693226758285 42870743576030134960034357)
                    ·
                      refine ⟨4019132210252825152503221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42870743576030134960034357 4019132210252825152503221)
                      ·
                        rfl

theorem cell23_7827232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7827232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827232 prefixEnd_7827232 := by exact prefixLift 7827232
  have htrace : WordTrace (prefixWord ++ tailWord_7827232) baseStart_7827232 baseEnd_7827232 := by
    simpa [prefixWord, tailWord_7827232, baseEnd_7827232] using wordTrace_append hprefix tailTrace_7827232
  have hstable : (prefixWord ++ tailWord_7827232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827232).length < 2 ^ (prefixWord ++ tailWord_7827232).sum := by decide
  have hdescent : baseEnd_7827232 < baseStart_7827232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827233 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7827233 : Nat := 118140960795 + 7827233 * 2 ^ 59
def prefixEnd_7827233 : Nat := 4983230072969 + 3 ^ 40 * 7827233 * 2
def baseEnd_7827233 : Nat := 4019132723733479648590717

theorem tailTrace_7827233 : CollatzResearch.WordTrace tailWord_7827233 prefixEnd_7827233 4019132723733479648590717 := by
  unfold tailWord_7827233
  simp only [CollatzResearch.WordTrace]
  refine ⟨285482640852279100814622353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190321760568186067209748235 285482640852279100814622353)
  ·
    refine ⟨214111980639209325610966765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285482640852279100814622353 214111980639209325610966765)
    ·
      refine ⟨80291992739703497104112537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214111980639209325610966765 80291992739703497104112537)
      ·
        refine ⟨60218994554777622828084403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80291992739703497104112537 60218994554777622828084403)
        ·
          refine ⟨90328491832166434242126605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60218994554777622828084403 90328491832166434242126605)
          ·
            refine ⟨33873184437062412840797477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90328491832166434242126605 33873184437062412840797477)
            ·
              refine ⟨6351222081949202407649527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33873184437062412840797477 6351222081949202407649527)
              ·
                refine ⟨9526833122923803611474291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351222081949202407649527 9526833122923803611474291)
                ·
                  refine ⟨14290249684385705417211437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526833122923803611474291 14290249684385705417211437)
                  ·
                    refine ⟨5358843631644639531454289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14290249684385705417211437 5358843631644639531454289)
                    ·
                      refine ⟨4019132723733479648590717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358843631644639531454289 4019132723733479648590717)
                      ·
                        rfl

theorem cell23_7827233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7827233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827233 prefixEnd_7827233 := by exact prefixLift 7827233
  have htrace : WordTrace (prefixWord ++ tailWord_7827233) baseStart_7827233 baseEnd_7827233 := by
    simpa [prefixWord, tailWord_7827233, baseEnd_7827233] using wordTrace_append hprefix tailTrace_7827233
  have hstable : (prefixWord ++ tailWord_7827233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827233).length < 2 ^ (prefixWord ++ tailWord_7827233).sum := by decide
  have hdescent : baseEnd_7827233 < baseStart_7827233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827263 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 4, 2]
def baseStart_7827263 : Nat := 118140960795 + 7827263 * 2 ^ 59
def prefixEnd_7827263 : Nat := 4983230072969 + 3 ^ 40 * 7827263 * 2
def baseEnd_7827263 : Nat := 4019148128153114531215579

theorem tailTrace_7827263 : CollatzResearch.WordTrace tailWord_7827263 prefixEnd_7827263 4019148128153114531215579 := by
  unfold tailWord_7827263
  simp only [CollatzResearch.WordTrace]
  refine ⟨285483735042170415938214443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190322490028113610625476295 285483735042170415938214443)
  ·
    refine ⟨428225602563255623907321665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285483735042170415938214443 428225602563255623907321665)
    ·
      refine ⟨321169201922441717930491249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428225602563255623907321665 321169201922441717930491249)
      ·
        refine ⟨240876901441831288447868437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321169201922441717930491249 240876901441831288447868437)
        ·
          refine ⟨11291104755085841645993833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240876901441831288447868437 11291104755085841645993833)
          ·
            refine ⟨8468328566314381234495375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11291104755085841645993833 8468328566314381234495375)
            ·
              refine ⟨12702492849471571851743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468328566314381234495375 12702492849471571851743063)
              ·
                refine ⟨19053739274207357777614595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702492849471571851743063 19053739274207357777614595)
                ·
                  refine ⟨28580608911311036666421893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19053739274207357777614595 28580608911311036666421893)
                  ·
                    refine ⟨5358864170870819374954105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28580608911311036666421893 5358864170870819374954105)
                    ·
                      refine ⟨4019148128153114531215579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5358864170870819374954105 4019148128153114531215579)
                      ·
                        rfl

theorem cell23_7827263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_7827263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827263 prefixEnd_7827263 := by exact prefixLift 7827263
  have htrace : WordTrace (prefixWord ++ tailWord_7827263) baseStart_7827263 baseEnd_7827263 := by
    simpa [prefixWord, tailWord_7827263, baseEnd_7827263] using wordTrace_append hprefix tailTrace_7827263
  have hstable : (prefixWord ++ tailWord_7827263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827263).length < 2 ^ (prefixWord ++ tailWord_7827263).sum := by decide
  have hdescent : baseEnd_7827263 < baseStart_7827263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827372 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_7827372 : Nat := 118140960795 + 7827372 * 2 ^ 59
def prefixEnd_7827372 : Nat := 4983230072969 + 3 ^ 40 * 7827372 * 2
def baseEnd_7827372 : Nat := 1339734699181484868250859

theorem tailTrace_7827372 : CollatzResearch.WordTrace tailWord_7827372 prefixEnd_7827372 1339734699181484868250859 := by
  unfold tailWord_7827372
  simp only [CollatzResearch.WordTrace]
  refine ⟨142743855299387763776966185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190325140399183685035954913 142743855299387763776966185)
  ·
    refine ⟨107057891474540822832724639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142743855299387763776966185 107057891474540822832724639)
    ·
      refine ⟨160586837211811234249086959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107057891474540822832724639 160586837211811234249086959)
      ·
        refine ⟨240880255817716851373630439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160586837211811234249086959 240880255817716851373630439)
        ·
          refine ⟨361320383726575277060445659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240880255817716851373630439 361320383726575277060445659)
          ·
            refine ⟨541980575589862915590668489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361320383726575277060445659 541980575589862915590668489)
            ·
              refine ⟨406485431692397186693001367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541980575589862915590668489 406485431692397186693001367)
              ·
                refine ⟨609728147538595780039502051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406485431692397186693001367 609728147538595780039502051)
                ·
                  refine ⟨914592221307893670059253077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609728147538595780039502051 914592221307893670059253077)
                  ·
                    refine ⟨1339734699181484868250859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 914592221307893670059253077 1339734699181484868250859)
                    ·
                      rfl

theorem cell23_7827372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_7827372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827372 prefixEnd_7827372 := by exact prefixLift 7827372
  have htrace : WordTrace (prefixWord ++ tailWord_7827372) baseStart_7827372 baseEnd_7827372 := by
    simpa [prefixWord, tailWord_7827372, baseEnd_7827372] using wordTrace_append hprefix tailTrace_7827372
  have hstable : (prefixWord ++ tailWord_7827372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827372).length < 2 ^ (prefixWord ++ tailWord_7827372).sum := by decide
  have hdescent : baseEnd_7827372 < baseStart_7827372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827380 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7827380 : Nat := 118140960795 + 7827380 * 2 ^ 59
def prefixEnd_7827380 : Nat := 4983230072969 + 3 ^ 40 * 7827380 * 2
def baseEnd_7827380 : Nat := 1339736068463230191150847

theorem tailTrace_7827380 : CollatzResearch.WordTrace tailWord_7827380 prefixEnd_7827380 1339736068463230191150847 := by
  unfold tailWord_7827380
  simp only [CollatzResearch.WordTrace]
  refine ⟨142744001191373272460111797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190325334921831029946815729 142744001191373272460111797)
  ·
    refine ⟨13382250111691244293135481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142744001191373272460111797 13382250111691244293135481)
    ·
      refine ⟨10036687583768433219851611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13382250111691244293135481 10036687583768433219851611)
      ·
        refine ⟨15055031375652649829777417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10036687583768433219851611 15055031375652649829777417)
        ·
          refine ⟨11291273531739487372333063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055031375652649829777417 11291273531739487372333063)
          ·
            refine ⟨16936910297609231058499595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291273531739487372333063 16936910297609231058499595)
            ·
              refine ⟨25405365446413846587749393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936910297609231058499595 25405365446413846587749393)
              ·
                refine ⟨19054024084810384940812045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25405365446413846587749393 19054024084810384940812045)
                ·
                  refine ⟨7145259031803894352804517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19054024084810384940812045 7145259031803894352804517)
                  ·
                    refine ⟨1339736068463230191150847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145259031803894352804517 1339736068463230191150847)
                    ·
                      rfl

theorem cell23_7827380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7827380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827380 prefixEnd_7827380 := by exact prefixLift 7827380
  have htrace : WordTrace (prefixWord ++ tailWord_7827380) baseStart_7827380 baseEnd_7827380 := by
    simpa [prefixWord, tailWord_7827380, baseEnd_7827380] using wordTrace_append hprefix tailTrace_7827380
  have hstable : (prefixWord ++ tailWord_7827380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827380).length < 2 ^ (prefixWord ++ tailWord_7827380).sum := by decide
  have hdescent : baseEnd_7827380 < baseStart_7827380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827406 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_7827406 : Nat := 118140960795 + 7827406 * 2 ^ 59
def prefixEnd_7827406 : Nat := 4983230072969 + 3 ^ 40 * 7827406 * 2
def baseEnd_7827406 : Nat := 1339740518628902490575807

theorem tailTrace_7827406 : CollatzResearch.WordTrace tailWord_7827406 prefixEnd_7827406 1339740518628902490575807 := by
  unfold tailWord_7827406
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686118835081543920083759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190325967120434900907113381 35686118835081543920083759)
  ·
    refine ⟨53529178252622315880125639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35686118835081543920083759 53529178252622315880125639)
    ·
      refine ⟨80293767378933473820188459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53529178252622315880125639 80293767378933473820188459)
      ·
        refine ⟨120440651068400210730282689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80293767378933473820188459 120440651068400210730282689)
        ·
          refine ⟨90330488301300158047712017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120440651068400210730282689 90330488301300158047712017)
          ·
            refine ⟨67747866225975118535784013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90330488301300158047712017 67747866225975118535784013)
            ·
              refine ⟨25405449834740669450919005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67747866225975118535784013 25405449834740669450919005)
              ·
                refine ⟨9527043688027751044094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25405449834740669450919005 9527043688027751044094627)
                ·
                  refine ⟨14290565532041626566141941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527043688027751044094627 14290565532041626566141941)
                  ·
                    refine ⟨1339740518628902490575807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14290565532041626566141941 1339740518628902490575807)
                    ·
                      rfl

theorem cell23_7827406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_7827406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827406 prefixEnd_7827406 := by exact prefixLift 7827406
  have htrace : WordTrace (prefixWord ++ tailWord_7827406) baseStart_7827406 baseEnd_7827406 := by
    simpa [prefixWord, tailWord_7827406, baseEnd_7827406] using wordTrace_append hprefix tailTrace_7827406
  have hstable : (prefixWord ++ tailWord_7827406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827406).length < 2 ^ (prefixWord ++ tailWord_7827406).sum := by decide
  have hdescent : baseEnd_7827406 < baseStart_7827406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827409 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_7827409 : Nat := 118140960795 + 7827409 * 2 ^ 59
def prefixEnd_7827409 : Nat := 4983230072969 + 3 ^ 40 * 7827409 * 2
def baseEnd_7827409 : Nat := 4019223096328670959989907

theorem tailTrace_7827409 : CollatzResearch.WordTrace tailWord_7827409 prefixEnd_7827409 4019223096328670959989907 := by
  unfold tailWord_7827409
  simp only [CollatzResearch.WordTrace]
  refine ⟨285489060099641482873029281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190326040066427655248686187 285489060099641482873029281)
  ·
    refine ⟨214116795074731112154771961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285489060099641482873029281 214116795074731112154771961)
    ·
      refine ⟨160587596306048334116078971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214116795074731112154771961 160587596306048334116078971)
      ·
        refine ⟨240881394459072501174118457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160587596306048334116078971 240881394459072501174118457)
        ·
          refine ⟨180661045844304375880588843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240881394459072501174118457 180661045844304375880588843)
          ·
            refine ⟨270991568766456563820883265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180661045844304375880588843 270991568766456563820883265)
            ·
              refine ⟨203243676574842422865662449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270991568766456563820883265 203243676574842422865662449)
              ·
                refine ⟨152432757431131817149246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203243676574842422865662449 152432757431131817149246837)
                ·
                  refine ⟨14290571009168607857741891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152432757431131817149246837 14290571009168607857741891)
                  ·
                    refine ⟨21435856513752911786612837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14290571009168607857741891 21435856513752911786612837)
                    ·
                      refine ⟨4019223096328670959989907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21435856513752911786612837 4019223096328670959989907)
                      ·
                        rfl

theorem cell23_7827409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_7827409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827409 prefixEnd_7827409 := by exact prefixLift 7827409
  have htrace : WordTrace (prefixWord ++ tailWord_7827409) baseStart_7827409 baseEnd_7827409 := by
    simpa [prefixWord, tailWord_7827409, baseEnd_7827409] using wordTrace_append hprefix tailTrace_7827409
  have hstable : (prefixWord ++ tailWord_7827409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827409).length < 2 ^ (prefixWord ++ tailWord_7827409).sum := by decide
  have hdescent : baseEnd_7827409 < baseStart_7827409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827410 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_7827410 : Nat := 118140960795 + 7827410 * 2 ^ 59
def prefixEnd_7827410 : Nat := 4983230072969 + 3 ^ 40 * 7827410 * 2
def baseEnd_7827410 : Nat := 446580401089925050675267

theorem tailTrace_7827410 : CollatzResearch.WordTrace tailWord_7827410 prefixEnd_7827410 446580401089925050675267 := by
  unfold tailWord_7827410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372274143159465010953921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190326064381758573362543789 71372274143159465010953921)
  ·
    refine ⟨53529205607369598758215441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71372274143159465010953921 53529205607369598758215441)
    ·
      refine ⟨40146904205527199068661581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53529205607369598758215441 40146904205527199068661581)
      ·
        refine ⟨15055089077072699650748093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40146904205527199068661581 15055089077072699650748093)
        ·
          refine ⟨5645658403902262369030535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15055089077072699650748093 5645658403902262369030535)
          ·
            refine ⟨8468487605853393553545803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645658403902262369030535 8468487605853393553545803)
            ·
              refine ⟨12702731408780090330318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468487605853393553545803 12702731408780090330318705)
              ·
                refine ⟨9527048556585067747739029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702731408780090330318705 9527048556585067747739029)
                ·
                  refine ⟨446580401089925050675267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9527048556585067747739029 446580401089925050675267)
                  ·
                    rfl

theorem cell23_7827410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_7827410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827410 prefixEnd_7827410 := by exact prefixLift 7827410
  have htrace : WordTrace (prefixWord ++ tailWord_7827410) baseStart_7827410 baseEnd_7827410 := by
    simpa [prefixWord, tailWord_7827410, baseEnd_7827410] using wordTrace_append hprefix tailTrace_7827410
  have hstable : (prefixWord ++ tailWord_7827410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827410).length < 2 ^ (prefixWord ++ tailWord_7827410).sum := by decide
  have hdescent : baseEnd_7827410 < baseStart_7827410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827436 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_7827436 : Nat := 118140960795 + 7827436 * 2 ^ 59
def prefixEnd_7827436 : Nat := 4983230072969 + 3 ^ 40 * 7827436 * 2
def baseEnd_7827436 : Nat := 1339745653435447451450761

theorem tailTrace_7827436 : CollatzResearch.WordTrace tailWord_7827436 prefixEnd_7827436 1339745653435447451450761 := by
  unfold tailWord_7827436
  simp only [CollatzResearch.WordTrace]
  refine ⟨142745022435271833242131081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190326696580362444322841441 142745022435271833242131081)
  ·
    refine ⟨107058766826453874931598311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142745022435271833242131081 107058766826453874931598311)
    ·
      refine ⟨160588150239680812397397467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107058766826453874931598311 160588150239680812397397467)
      ·
        refine ⟨240882225359521218596096201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160588150239680812397397467 240882225359521218596096201)
        ·
          refine ⟨180661669019640913947072151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240882225359521218596096201 180661669019640913947072151)
          ·
            refine ⟨270992503529461370920608227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180661669019640913947072151 270992503529461370920608227)
            ·
              refine ⟨406488755294192056380912341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270992503529461370920608227 406488755294192056380912341)
              ·
                refine ⟨9527080202207626321427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406488755294192056380912341 9527080202207626321427633)
                ·
                  refine ⟨7145310151655719741070725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527080202207626321427633 7145310151655719741070725)
                  ·
                    refine ⟨1339745653435447451450761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145310151655719741070725 1339745653435447451450761)
                    ·
                      rfl

theorem cell23_7827436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_7827436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827436 prefixEnd_7827436 := by exact prefixLift 7827436
  have htrace : WordTrace (prefixWord ++ tailWord_7827436) baseStart_7827436 baseEnd_7827436 := by
    simpa [prefixWord, tailWord_7827436, baseEnd_7827436] using wordTrace_append hprefix tailTrace_7827436
  have hstable : (prefixWord ++ tailWord_7827436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827436).length < 2 ^ (prefixWord ++ tailWord_7827436).sum := by decide
  have hdescent : baseEnd_7827436 < baseStart_7827436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827439 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_7827439 : Nat := 118140960795 + 7827439 * 2 ^ 59
def prefixEnd_7827439 : Nat := 4983230072969 + 3 ^ 40 * 7827439 * 2
def baseEnd_7827439 : Nat := 4019238500748305842614769

theorem tailTrace_7827439 : CollatzResearch.WordTrace tailWord_7827439 prefixEnd_7827439 4019238500748305842614769 := by
  unfold tailWord_7827439
  simp only [CollatzResearch.WordTrace]
  refine ⟨285490154289532797996621371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190326769526355198664414247 285490154289532797996621371)
  ·
    refine ⟨428235231434299196994932057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285490154289532797996621371 428235231434299196994932057)
    ·
      refine ⟨321176423575724397746199043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428235231434299196994932057 321176423575724397746199043)
      ·
        refine ⟨481764635363586596619298565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321176423575724397746199043 481764635363586596619298565)
        ·
          refine ⟨90330869130672486866118481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481764635363586596619298565 90330869130672486866118481)
          ·
            refine ⟨67748151848004365149588861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90330869130672486866118481 67748151848004365149588861)
            ·
              refine ⟨25405556943001636931095823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67748151848004365149588861 25405556943001636931095823)
              ·
                refine ⟨38108335414502455396643735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25405556943001636931095823 38108335414502455396643735)
                ·
                  refine ⟨57162503121753683094965603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38108335414502455396643735 57162503121753683094965603)
                  ·
                    refine ⟨85743754682630524642448405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57162503121753683094965603 85743754682630524642448405)
                    ·
                      refine ⟨4019238500748305842614769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85743754682630524642448405 4019238500748305842614769)
                      ·
                        rfl

theorem cell23_7827439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_7827439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827439 prefixEnd_7827439 := by exact prefixLift 7827439
  have htrace : WordTrace (prefixWord ++ tailWord_7827439) baseStart_7827439 baseEnd_7827439 := by
    simpa [prefixWord, tailWord_7827439, baseEnd_7827439] using wordTrace_append hprefix tailTrace_7827439
  have hstable : (prefixWord ++ tailWord_7827439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827439).length < 2 ^ (prefixWord ++ tailWord_7827439).sum := by decide
  have hdescent : baseEnd_7827439 < baseStart_7827439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827449 : List Nat := [1, 2, 1, 3, 1, 5, 1, 9]
def baseStart_7827449 : Nat := 118140960795 + 7827449 * 2 ^ 59
def prefixEnd_7827449 : Nat := 4983230072969 + 3 ^ 40 * 7827449 * 2
def baseEnd_7827449 : Nat := 148860875390920400129249

theorem tailTrace_7827449 : CollatzResearch.WordTrace tailWord_7827449 prefixEnd_7827449 148860875390920400129249 := by
  unfold tailWord_7827449
  simp only [CollatzResearch.WordTrace]
  refine ⟨285490519019496569704485401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190327012679664379802990267 285490519019496569704485401)
  ·
    refine ⟨214117889264622427278364051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285490519019496569704485401 214117889264622427278364051)
    ·
      refine ⟨321176833896933640917546077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214117889264622427278364051 321176833896933640917546077)
      ·
        refine ⟨120441312711350115344079779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321176833896933640917546077 120441312711350115344079779)
        ·
          refine ⟨180661969067025173016119669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120441312711350115344079779 180661969067025173016119669)
          ·
            refine ⟨16937059600033609970261219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180661969067025173016119669 16937059600033609970261219)
            ·
              refine ⟨25405589400050414955391829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16937059600033609970261219 25405589400050414955391829)
              ·
                refine ⟨148860875390920400129249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25405589400050414955391829 148860875390920400129249)
                ·
                  rfl

theorem cell23_7827449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 9].length) (baseStart_7827449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827449 prefixEnd_7827449 := by exact prefixLift 7827449
  have htrace : WordTrace (prefixWord ++ tailWord_7827449) baseStart_7827449 baseEnd_7827449 := by
    simpa [prefixWord, tailWord_7827449, baseEnd_7827449] using wordTrace_append hprefix tailTrace_7827449
  have hstable : (prefixWord ++ tailWord_7827449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827449).length < 2 ^ (prefixWord ++ tailWord_7827449).sum := by decide
  have hdescent : baseEnd_7827449 < baseStart_7827449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827454 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7827454 : Nat := 118140960795 + 7827454 * 2 ^ 59
def prefixEnd_7827454 : Nat := 4983230072969 + 3 ^ 40 * 7827454 * 2
def baseEnd_7827454 : Nat := 4019246202958123283927201

theorem tailTrace_7827454 : CollatzResearch.WordTrace tailWord_7827454 prefixEnd_7827454 4019246202958123283927201 := by
  unfold tailWord_7827454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686337673059806944802177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190327134256318970372278277 35686337673059806944802177)
  ·
    refine ⟨26764753254794855208601633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35686337673059806944802177 26764753254794855208601633)
    ·
      refine ⟨20073564941096141406451225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26764753254794855208601633 20073564941096141406451225)
      ·
        refine ⟨15055173705822106054838419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20073564941096141406451225 15055173705822106054838419)
        ·
          refine ⟨22582760558733159082257629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055173705822106054838419 22582760558733159082257629)
          ·
            refine ⟨8468535209524934655846611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22582760558733159082257629 8468535209524934655846611)
            ·
              refine ⟨12702802814287401983769917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468535209524934655846611 12702802814287401983769917)
              ·
                refine ⟨4763551055357775743913719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12702802814287401983769917 4763551055357775743913719)
                ·
                  refine ⟨7145326583036663615870579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763551055357775743913719 7145326583036663615870579)
                  ·
                    refine ⟨10717989874554995423805869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145326583036663615870579 10717989874554995423805869)
                    ·
                      refine ⟨4019246202958123283927201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10717989874554995423805869 4019246202958123283927201)
                      ·
                        rfl

theorem cell23_7827454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7827454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827454 prefixEnd_7827454 := by exact prefixLift 7827454
  have htrace : WordTrace (prefixWord ++ tailWord_7827454) baseStart_7827454 baseEnd_7827454 := by
    simpa [prefixWord, tailWord_7827454, baseEnd_7827454] using wordTrace_append hprefix tailTrace_7827454
  have hstable : (prefixWord ++ tailWord_7827454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827454).length < 2 ^ (prefixWord ++ tailWord_7827454).sum := by decide
  have hdescent : baseEnd_7827454 < baseStart_7827454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827463 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7827463 : Nat := 118140960795 + 7827463 * 2 ^ 59
def prefixEnd_7827463 : Nat := 4983230072969 + 3 ^ 40 * 7827463 * 2
def baseEnd_7827463 : Nat := 4019250824284013748714659

theorem tailTrace_7827463 : CollatzResearch.WordTrace tailWord_7827463 prefixEnd_7827463 4019250824284013748714659 := by
  unfold tailWord_7827463
  simp only [CollatzResearch.WordTrace]
  refine ⟨285491029641445850095495043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190327353094297233396996695 285491029641445850095495043)
  ·
    refine ⟨428236544462168775143242565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285491029641445850095495043 428236544462168775143242565)
    ·
      refine ⟨80294352086656645339357981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428236544462168775143242565 80294352086656645339357981)
      ·
        refine ⟨30110382032496242002259243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80294352086656645339357981 30110382032496242002259243)
        ·
          refine ⟨45165573048744363003388865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30110382032496242002259243 45165573048744363003388865)
          ·
            refine ⟨33874179786558272252541649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45165573048744363003388865 33874179786558272252541649)
            ·
              refine ⟨25405634839918704189406237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33874179786558272252541649 25405634839918704189406237)
              ·
                refine ⟨9527113064969514071027339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25405634839918704189406237 9527113064969514071027339)
                ·
                  refine ⟨14290669597454271106541009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527113064969514071027339 14290669597454271106541009)
                  ·
                    refine ⟨10718002198090703329905757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14290669597454271106541009 10718002198090703329905757)
                    ·
                      refine ⟨4019250824284013748714659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718002198090703329905757 4019250824284013748714659)
                      ·
                        rfl

theorem cell23_7827463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7827463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827463 prefixEnd_7827463 := by exact prefixLift 7827463
  have htrace : WordTrace (prefixWord ++ tailWord_7827463) baseStart_7827463 baseEnd_7827463 := by
    simpa [prefixWord, tailWord_7827463, baseEnd_7827463] using wordTrace_append hprefix tailTrace_7827463
  have hstable : (prefixWord ++ tailWord_7827463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827463).length < 2 ^ (prefixWord ++ tailWord_7827463).sum := by decide
  have hdescent : baseEnd_7827463 < baseStart_7827463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827466 : List Nat := [3, 1, 2, 2, 4, 2, 9]
def baseStart_7827466 : Nat := 118140960795 + 7827466 * 2 ^ 59
def prefixEnd_7827466 : Nat := 4983230072969 + 3 ^ 40 * 7827466 * 2
def baseEnd_7827466 : Nat := 49620399564518237493545

theorem tailTrace_7827466 : CollatzResearch.WordTrace tailWord_7827466 prefixEnd_7827466 49620399564518237493545 := by
  unfold tailWord_7827466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372784765108745401963563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190327426040289987738569501 71372784765108745401963563)
  ·
    refine ⟨107059177147663118102945345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71372784765108745401963563 107059177147663118102945345)
    ·
      refine ⟨80294382860747338577209009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107059177147663118102945345 80294382860747338577209009)
      ·
        refine ⟨60220787145560503932906757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80294382860747338577209009 60220787145560503932906757)
        ·
          refine ⟨11291397589792594487420017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60220787145560503932906757 11291397589792594487420017)
          ·
            refine ⟨8468548192344445865565013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11291397589792594487420017 8468548192344445865565013)
            ·
              refine ⟨49620399564518237493545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8468548192344445865565013 49620399564518237493545)
              ·
                rfl

theorem cell23_7827466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 9].length) (baseStart_7827466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827466 prefixEnd_7827466 := by exact prefixLift 7827466
  have htrace : WordTrace (prefixWord ++ tailWord_7827466) baseStart_7827466 baseEnd_7827466 := by
    simpa [prefixWord, tailWord_7827466, baseEnd_7827466] using wordTrace_append hprefix tailTrace_7827466
  have hstable : (prefixWord ++ tailWord_7827466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827466).length < 2 ^ (prefixWord ++ tailWord_7827466).sum := by decide
  have hdescent : baseEnd_7827466 < baseStart_7827466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827477 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_7827477 : Nat := 118140960795 + 7827477 * 2 ^ 59
def prefixEnd_7827477 : Nat := 4983230072969 + 3 ^ 40 * 7827477 * 2
def baseEnd_7827477 : Nat := 4019258013013176693939595

theorem tailTrace_7827477 : CollatzResearch.WordTrace tailWord_7827477 prefixEnd_7827477 4019258013013176693939595 := by
  unfold tailWord_7827477
  simp only [CollatzResearch.WordTrace]
  refine ⟨285491540263395130486504685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190327693508930086991003123 285491540263395130486504685)
  ·
    refine ⟨107059327598773173932439257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285491540263395130486504685 107059327598773173932439257)
    ·
      refine ⟨80294495699079880449329443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107059327598773173932439257 80294495699079880449329443)
      ·
        refine ⟨120441743548619820673994165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80294495699079880449329443 120441743548619820673994165)
        ·
          refine ⟨11291413457683108188186953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120441743548619820673994165 11291413457683108188186953)
          ·
            refine ⟨8468560093262331141140215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11291413457683108188186953 8468560093262331141140215)
            ·
              refine ⟨12702840139893496711710323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468560093262331141140215 12702840139893496711710323)
              ·
                refine ⟨19054260209840245067565485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702840139893496711710323 19054260209840245067565485)
                ·
                  refine ⟨7145347578690091900337057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19054260209840245067565485 7145347578690091900337057)
                  ·
                    refine ⟨5359010684017568925252793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145347578690091900337057 5359010684017568925252793)
                    ·
                      refine ⟨4019258013013176693939595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359010684017568925252793 4019258013013176693939595)
                      ·
                        rfl

theorem cell23_7827477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_7827477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827477 prefixEnd_7827477 := by exact prefixLift 7827477
  have htrace : WordTrace (prefixWord ++ tailWord_7827477) baseStart_7827477 baseEnd_7827477 := by
    simpa [prefixWord, tailWord_7827477, baseEnd_7827477] using wordTrace_append hprefix tailTrace_7827477
  have hstable : (prefixWord ++ tailWord_7827477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827477).length < 2 ^ (prefixWord ++ tailWord_7827477).sum := by decide
  have hdescent : baseEnd_7827477 < baseStart_7827477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827499 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_7827499 : Nat := 118140960795 + 7827499 * 2 ^ 59
def prefixEnd_7827499 : Nat := 4983230072969 + 3 ^ 40 * 7827499 * 2
def baseEnd_7827499 : Nat := 4019269309587575607864493

theorem tailTrace_7827499 : CollatzResearch.WordTrace tailWord_7827499 prefixEnd_7827499 4019269309587575607864493 := by
  unfold tailWord_7827499
  simp only [CollatzResearch.WordTrace]
  refine ⟨285492342669315428243805551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190328228446210285495870367 285492342669315428243805551)
  ·
    refine ⟨428238514003973142365708327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285492342669315428243805551 428238514003973142365708327)
    ·
      refine ⟨642357771005959713548562491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428238514003973142365708327 642357771005959713548562491)
      ·
        refine ⟨963536656508939570322843737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642357771005959713548562491 963536656508939570322843737)
        ·
          refine ⟨722652492381704677742132803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963536656508939570322843737 722652492381704677742132803)
          ·
            refine ⟨1083978738572557016613199205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722652492381704677742132803 1083978738572557016613199205)
            ·
              refine ⟨203246013482354440614974851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1083978738572557016613199205 203246013482354440614974851)
              ·
                refine ⟨304869020223531660922462277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203246013482354440614974851 304869020223531660922462277)
                ·
                  refine ⟨57162941291912186422961677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304869020223531660922462277 57162941291912186422961677)
                  ·
                    refine ⟨21436102984467069908610629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57162941291912186422961677 21436102984467069908610629)
                    ·
                      refine ⟨4019269309587575607864493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21436102984467069908610629 4019269309587575607864493)
                      ·
                        rfl

theorem cell23_7827499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_7827499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827499 prefixEnd_7827499 := by exact prefixLift 7827499
  have htrace : WordTrace (prefixWord ++ tailWord_7827499) baseStart_7827499 baseEnd_7827499 := by
    simpa [prefixWord, tailWord_7827499, baseEnd_7827499] using wordTrace_append hprefix tailTrace_7827499
  have hstable : (prefixWord ++ tailWord_7827499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827499).length < 2 ^ (prefixWord ++ tailWord_7827499).sum := by decide
  have hdescent : baseEnd_7827499 < baseStart_7827499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827503 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 1, 3, 2]
def baseStart_7827503 : Nat := 118140960795 + 7827503 * 2 ^ 59
def prefixEnd_7827503 : Nat := 4983230072969 + 3 ^ 40 * 7827503 * 2
def baseEnd_7827503 : Nat := 4019271363510193592214475

theorem tailTrace_7827503 : CollatzResearch.WordTrace tailWord_7827503 prefixEnd_7827503 4019271363510193592214475 := by
  unfold tailWord_7827503
  simp only [CollatzResearch.WordTrace]
  refine ⟨285492488561300936926951163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190328325707533957951300775 285492488561300936926951163)
  ·
    refine ⟨428238732841951405390426745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285492488561300936926951163 428238732841951405390426745)
    ·
      refine ⟨321179049631463554042820059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428238732841951405390426745 321179049631463554042820059)
      ·
        refine ⟨481768574447195331064230089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321179049631463554042820059 481768574447195331064230089)
        ·
          refine ⟨361326430835396498298172567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481768574447195331064230089 361326430835396498298172567)
          ·
            refine ⟨541989646253094747447258851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361326430835396498298172567 541989646253094747447258851)
            ·
              refine ⟨812984469379642121170888277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541989646253094747447258851 812984469379642121170888277)
              ·
                refine ⟨9527161750542681107471347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 812984469379642121170888277 9527161750542681107471347)
                ·
                  refine ⟨14290742625814021661207021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527161750542681107471347 14290742625814021661207021)
                  ·
                    refine ⟨5359028484680258122952633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14290742625814021661207021 5359028484680258122952633)
                    ·
                      refine ⟨4019271363510193592214475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359028484680258122952633 4019271363510193592214475)
                      ·
                        rfl

theorem cell23_7827503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3, 2].length) (baseStart_7827503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827503 prefixEnd_7827503 := by exact prefixLift 7827503
  have htrace : WordTrace (prefixWord ++ tailWord_7827503) baseStart_7827503 baseEnd_7827503 := by
    simpa [prefixWord, tailWord_7827503, baseEnd_7827503] using wordTrace_append hprefix tailTrace_7827503
  have hstable : (prefixWord ++ tailWord_7827503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827503).length < 2 ^ (prefixWord ++ tailWord_7827503).sum := by decide
  have hdescent : baseEnd_7827503 < baseStart_7827503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827546 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_7827546 : Nat := 118140960795 + 7827546 * 2 ^ 59
def prefixEnd_7827546 : Nat := 4983230072969 + 3 ^ 40 * 7827546 * 2
def baseEnd_7827546 : Nat := 4019293443178336923976777

theorem tailTrace_7827546 : CollatzResearch.WordTrace tailWord_7827546 prefixEnd_7827546 4019293443178336923976777 := by
  unfold tailWord_7827546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71373514225036288817691623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190329371266763436847177661 71373514225036288817691623)
  ·
    refine ⟨107060271337554433226537435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71373514225036288817691623 107060271337554433226537435)
    ·
      refine ⟨160590407006331649839806153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107060271337554433226537435 160590407006331649839806153)
      ·
        refine ⟨120442805254748737379854615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160590407006331649839806153 120442805254748737379854615)
        ·
          refine ⟨180664207882123106069781923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120442805254748737379854615 180664207882123106069781923)
          ·
            refine ⟨270996311823184659104672885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180664207882123106069781923 270996311823184659104672885)
            ·
              refine ⟨25405904233423561791063083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270996311823184659104672885 25405904233423561791063083)
              ·
                refine ⟨38108856350135342686594625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25405904233423561791063083 38108856350135342686594625)
                ·
                  refine ⟨28581642262601507014945969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38108856350135342686594625 28581642262601507014945969)
                  ·
                    refine ⟨21436231696951130261209477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28581642262601507014945969 21436231696951130261209477)
                    ·
                      refine ⟨4019293443178336923976777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21436231696951130261209477 4019293443178336923976777)
                      ·
                        rfl

theorem cell23_7827546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_7827546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827546 prefixEnd_7827546 := by exact prefixLift 7827546
  have htrace : WordTrace (prefixWord ++ tailWord_7827546) baseStart_7827546 baseEnd_7827546 := by
    simpa [prefixWord, tailWord_7827546, baseEnd_7827546] using wordTrace_append hprefix tailTrace_7827546
  have hstable : (prefixWord ++ tailWord_7827546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827546).length < 2 ^ (prefixWord ++ tailWord_7827546).sum := by decide
  have hdescent : baseEnd_7827546 < baseStart_7827546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827643 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3]
def baseStart_7827643 : Nat := 118140960795 + 7827643 * 2 ^ 59
def prefixEnd_7827643 : Nat := 4983230072969 + 3 ^ 40 * 7827643 * 2
def baseEnd_7827643 : Nat := 4019343250801823044463831

theorem tailTrace_7827643 : CollatzResearch.WordTrace tailWord_7827643 prefixEnd_7827643 4019343250801823044463831 := by
  unfold tailWord_7827643
  simp only [CollatzResearch.WordTrace]
  refine ⟨285497594780793740837047583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190331729853862493891365055 285497594780793740837047583)
  ·
    refine ⟨428246392171190611255571375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285497594780793740837047583 428246392171190611255571375)
    ·
      refine ⟨642369588256785916883357063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428246392171190611255571375 642369588256785916883357063)
      ·
        refine ⟨963554382385178875325035595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642369588256785916883357063 963554382385178875325035595)
        ·
          refine ⟨1445331573577768312987553393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963554382385178875325035595 1445331573577768312987553393)
          ·
            refine ⟨1083998680183326234740665045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445331573577768312987553393 1083998680183326234740665045)
            ·
              refine ⟨25406219066796708626734337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1083998680183326234740665045 25406219066796708626734337)
              ·
                refine ⟨19054664300097531470050753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25406219066796708626734337 19054664300097531470050753)
                ·
                  refine ⟨14290998225073148602538065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19054664300097531470050753 14290998225073148602538065)
                  ·
                    refine ⟨10718248668804861451903549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14290998225073148602538065 10718248668804861451903549)
                    ·
                      refine ⟨4019343250801823044463831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718248668804861451903549 4019343250801823044463831)
                      ·
                        rfl

theorem cell23_7827643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].length) (baseStart_7827643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827643 prefixEnd_7827643 := by exact prefixLift 7827643
  have htrace : WordTrace (prefixWord ++ tailWord_7827643) baseStart_7827643 baseEnd_7827643 := by
    simpa [prefixWord, tailWord_7827643, baseEnd_7827643] using wordTrace_append hprefix tailTrace_7827643
  have hstable : (prefixWord ++ tailWord_7827643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827643).length < 2 ^ (prefixWord ++ tailWord_7827643).sum := by decide
  have hdescent : baseEnd_7827643 < baseStart_7827643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827677 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7827677 : Nat := 118140960795 + 7827677 * 2 ^ 59
def prefixEnd_7827677 : Nat := 4983230072969 + 3 ^ 40 * 7827677 * 2
def baseEnd_7827677 : Nat := 4019360709144075911438675

theorem tailTrace_7827677 : CollatzResearch.WordTrace tailWord_7827677 prefixEnd_7827677 4019360709144075911438675 := by
  unfold tailWord_7827677
  simp only [CollatzResearch.WordTrace]
  refine ⟨285498834862670564643785285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190332556575113709762523523 285498834862670564643785285)
  ·
    refine ⟨53531031536750730870709741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285498834862670564643785285 53531031536750730870709741)
    ·
      refine ⟨20074136826281524076516153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53531031536750730870709741 20074136826281524076516153)
      ·
        refine ⟨15055602619711143057387115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20074136826281524076516153 15055602619711143057387115)
        ·
          refine ⟨22583403929566714586080673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055602619711143057387115 22583403929566714586080673)
          ·
            refine ⟨16937552947175035939560505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22583403929566714586080673 16937552947175035939560505)
            ·
              refine ⟨12703164710381276954670379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16937552947175035939560505 12703164710381276954670379)
              ·
                refine ⟨19054747065571915432005569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703164710381276954670379 19054747065571915432005569)
                ·
                  refine ⟨14291060299178936574004177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19054747065571915432005569 14291060299178936574004177)
                  ·
                    refine ⟨10718295224384202430503133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14291060299178936574004177 10718295224384202430503133)
                    ·
                      refine ⟨4019360709144075911438675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718295224384202430503133 4019360709144075911438675)
                      ·
                        rfl

theorem cell23_7827677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7827677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827677 prefixEnd_7827677 := by exact prefixLift 7827677
  have htrace : WordTrace (prefixWord ++ tailWord_7827677) baseStart_7827677 baseEnd_7827677 := by
    simpa [prefixWord, tailWord_7827677, baseEnd_7827677] using wordTrace_append hprefix tailTrace_7827677
  have hstable : (prefixWord ++ tailWord_7827677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827677).length < 2 ^ (prefixWord ++ tailWord_7827677).sum := by decide
  have hdescent : baseEnd_7827677 < baseStart_7827677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827713 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7827713 : Nat := 118140960795 + 7827713 * 2 ^ 59
def prefixEnd_7827713 : Nat := 4983230072969 + 3 ^ 40 * 7827713 * 2
def baseEnd_7827713 : Nat := 4019379194447637770588509

theorem tailTrace_7827713 : CollatzResearch.WordTrace tailWord_7827713 prefixEnd_7827713 4019379194447637770588509 := by
  unfold tailWord_7827713
  simp only [CollatzResearch.WordTrace]
  refine ⟨285500147890540142792095793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190333431927026761861397195 285500147890540142792095793)
  ·
    refine ⟨214125110917905107094071845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285500147890540142792095793 214125110917905107094071845)
    ·
      refine ⟨40148458297107207580138471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214125110917905107094071845 40148458297107207580138471)
      ·
        refine ⟨60222687445660811370207707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40148458297107207580138471 60222687445660811370207707)
        ·
          refine ⟨90334031168491217055311561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60222687445660811370207707 90334031168491217055311561)
          ·
            refine ⟨67750523376368412791483671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90334031168491217055311561 67750523376368412791483671)
            ·
              refine ⟨101625785064552619187225507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67750523376368412791483671 101625785064552619187225507)
              ·
                refine ⟨152438677596828928780838261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101625785064552619187225507 152438677596828928780838261)
                ·
                  refine ⟨14291126024702712073203587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152438677596828928780838261 14291126024702712073203587)
                  ·
                    refine ⟨21436689037054068109805381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14291126024702712073203587 21436689037054068109805381)
                    ·
                      refine ⟨4019379194447637770588509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21436689037054068109805381 4019379194447637770588509)
                      ·
                        rfl

theorem cell23_7827713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7827713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827713 prefixEnd_7827713 := by exact prefixLift 7827713
  have htrace : WordTrace (prefixWord ++ tailWord_7827713) baseStart_7827713 baseEnd_7827713 := by
    simpa [prefixWord, tailWord_7827713, baseEnd_7827713] using wordTrace_append hprefix tailTrace_7827713
  have hstable : (prefixWord ++ tailWord_7827713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827713).length < 2 ^ (prefixWord ++ tailWord_7827713).sum := by decide
  have hdescent : baseEnd_7827713 < baseStart_7827713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827723 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 6]
def baseStart_7827723 : Nat := 118140960795 + 7827723 * 2 ^ 59
def prefixEnd_7827723 : Nat := 4983230072969 + 3 ^ 40 * 7827723 * 2
def baseEnd_7827723 : Nat := 1339794776418060910487821

theorem tailTrace_7827723 : CollatzResearch.WordTrace tailWord_7827723 prefixEnd_7827723 1339794776418060910487821 := by
  unfold tailWord_7827723
  simp only [CollatzResearch.WordTrace]
  refine ⟨285500512620503914499959823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190333675080335942999973215 285500512620503914499959823)
  ·
    refine ⟨428250768930755871749939735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285500512620503914499959823 428250768930755871749939735)
    ·
      refine ⟨642376153396133807624909603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428250768930755871749939735 642376153396133807624909603)
      ·
        refine ⟨963564230094200711437364405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642376153396133807624909603 963564230094200711437364405)
        ·
          refine ⟨90334146571331316697252913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 963564230094200711437364405 90334146571331316697252913)
          ·
            refine ⟨67750609928498487522939685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90334146571331316697252913 67750609928498487522939685)
            ·
              refine ⟨12703239361593466410551191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67750609928498487522939685 12703239361593466410551191)
              ·
                refine ⟨19054859042390199615826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703239361593466410551191 19054859042390199615826787)
                ·
                  refine ⟨28582288563585299423740181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19054859042390199615826787 28582288563585299423740181)
                  ·
                    refine ⟨1339794776418060910487821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28582288563585299423740181 1339794776418060910487821)
                    ·
                      rfl

theorem cell23_7827723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].length) (baseStart_7827723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827723 prefixEnd_7827723 := by exact prefixLift 7827723
  have htrace : WordTrace (prefixWord ++ tailWord_7827723) baseStart_7827723 baseEnd_7827723 := by
    simpa [prefixWord, tailWord_7827723, baseEnd_7827723] using wordTrace_append hprefix tailTrace_7827723
  have hstable : (prefixWord ++ tailWord_7827723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827723).length < 2 ^ (prefixWord ++ tailWord_7827723).sum := by decide
  have hdescent : baseEnd_7827723 < baseStart_7827723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827741 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7827741 : Nat := 118140960795 + 7827741 * 2 ^ 59
def prefixEnd_7827741 : Nat := 4983230072969 + 3 ^ 40 * 7827741 * 2
def baseEnd_7827741 : Nat := 4019393571905963661038381

theorem tailTrace_7827741 : CollatzResearch.WordTrace tailWord_7827741 prefixEnd_7827741 4019393571905963661038381 := by
  unfold tailWord_7827741
  simp only [CollatzResearch.WordTrace]
  refine ⟨285501169134438703574115077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190334112756292469049410051 285501169134438703574115077)
  ·
    refine ⟨53531469212707256920146577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285501169134438703574115077 53531469212707256920146577)
    ·
      refine ⟨40148601909530442690109933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53531469212707256920146577 40148601909530442690109933)
      ·
        refine ⟨15055725716073916008791225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40148601909530442690109933 15055725716073916008791225)
        ·
          refine ⟨11291794287055437006593419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055725716073916008791225 11291794287055437006593419)
          ·
            refine ⟨16937691430583155509890129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291794287055437006593419 16937691430583155509890129)
            ·
              refine ⟨12703268572937366632417597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16937691430583155509890129 12703268572937366632417597)
              ·
                refine ⟨4763725714851512487156599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12703268572937366632417597 4763725714851512487156599)
                ·
                  refine ⟨7145588572277268730734899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763725714851512487156599 7145588572277268730734899)
                  ·
                    refine ⟨10718382858415903096102349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145588572277268730734899 10718382858415903096102349)
                    ·
                      refine ⟨4019393571905963661038381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718382858415903096102349 4019393571905963661038381)
                      ·
                        rfl

theorem cell23_7827741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7827741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827741 prefixEnd_7827741 := by exact prefixLift 7827741
  have htrace : WordTrace (prefixWord ++ tailWord_7827741) baseStart_7827741 baseEnd_7827741 := by
    simpa [prefixWord, tailWord_7827741, baseEnd_7827741] using wordTrace_append hprefix tailTrace_7827741
  have hstable : (prefixWord ++ tailWord_7827741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827741).length < 2 ^ (prefixWord ++ tailWord_7827741).sum := by decide
  have hdescent : baseEnd_7827741 < baseStart_7827741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827764 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_7827764 : Nat := 118140960795 + 7827764 * 2 ^ 59
def prefixEnd_7827764 : Nat := 4983230072969 + 3 ^ 40 * 7827764 * 2
def baseEnd_7827764 : Nat := 4019405381961017071050775

theorem tailTrace_7827764 : CollatzResearch.WordTrace tailWord_7827764 prefixEnd_7827764 4019405381961017071050775 := by
  unfold tailWord_7827764
  simp only [CollatzResearch.WordTrace]
  refine ⟨142751004006677689251101173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190334672008903585668134897 142751004006677689251101173)
  ·
    refine ⟨13382906625626033367290735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142751004006677689251101173 13382906625626033367290735)
    ·
      refine ⟨20074359938439050050936103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382906625626033367290735 20074359938439050050936103)
      ·
        refine ⟨30111539907658575076404155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20074359938439050050936103 30111539907658575076404155)
        ·
          refine ⟨45167309861487862614606233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111539907658575076404155 45167309861487862614606233)
          ·
            refine ⟨33875482396115896960954675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45167309861487862614606233 33875482396115896960954675)
            ·
              refine ⟨50813223594173845441432013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875482396115896960954675 50813223594173845441432013)
              ·
                refine ⟨19054958847815192040537005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50813223594173845441432013 19054958847815192040537005)
                ·
                  refine ⟨7145609567930697015201377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19054958847815192040537005 7145609567930697015201377)
                  ·
                    refine ⟨5359207175948022761401033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145609567930697015201377 5359207175948022761401033)
                    ·
                      refine ⟨4019405381961017071050775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359207175948022761401033 4019405381961017071050775)
                      ·
                        rfl

theorem cell23_7827764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_7827764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827764 prefixEnd_7827764 := by exact prefixLift 7827764
  have htrace : WordTrace (prefixWord ++ tailWord_7827764) baseStart_7827764 baseEnd_7827764 := by
    simpa [prefixWord, tailWord_7827764, baseEnd_7827764] using wordTrace_append hprefix tailTrace_7827764
  have hstable : (prefixWord ++ tailWord_7827764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827764).length < 2 ^ (prefixWord ++ tailWord_7827764).sum := by decide
  have hdescent : baseEnd_7827764 < baseStart_7827764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827774 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7827774 : Nat := 118140960795 + 7827774 * 2 ^ 59
def prefixEnd_7827774 : Nat := 4983230072969 + 3 ^ 40 * 7827774 * 2
def baseEnd_7827774 : Nat := 1339803505589187343975243

theorem tailTrace_7827774 : CollatzResearch.WordTrace tailWord_7827774 prefixEnd_7827774 1339803505589187343975243 := by
  unfold tailWord_7827774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687796592914893776258297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190334915162212766806710917 35687796592914893776258297)
  ·
    refine ⟨26765847444686170332193723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35687796592914893776258297 26765847444686170332193723)
    ·
      refine ⟨40148771167029255498290585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26765847444686170332193723 40148771167029255498290585)
      ·
        refine ⟨30111578375271941623717939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40148771167029255498290585 30111578375271941623717939)
        ·
          refine ⟨45167367562907912435576909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111578375271941623717939 45167367562907912435576909)
          ·
            refine ⟨16937762836090467163341341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45167367562907912435576909 16937762836090467163341341)
            ·
              refine ⟨6351661063533925186253003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16937762836090467163341341 6351661063533925186253003)
              ·
                refine ⟨9527491595300887779379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351661063533925186253003 9527491595300887779379505)
                ·
                  refine ⟨7145618696475665834534629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527491595300887779379505 7145618696475665834534629)
                  ·
                    refine ⟨1339803505589187343975243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145618696475665834534629 1339803505589187343975243)
                    ·
                      rfl

theorem cell23_7827774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7827774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827774 prefixEnd_7827774 := by exact prefixLift 7827774
  have htrace : WordTrace (prefixWord ++ tailWord_7827774) baseStart_7827774 baseEnd_7827774 := by
    simpa [prefixWord, tailWord_7827774, baseEnd_7827774] using wordTrace_append hprefix tailTrace_7827774
  have hstable : (prefixWord ++ tailWord_7827774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827774).length < 2 ^ (prefixWord ++ tailWord_7827774).sum := by decide
  have hdescent : baseEnd_7827774 < baseStart_7827774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827793 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_7827793 : Nat := 118140960795 + 7827793 * 2 ^ 59
def prefixEnd_7827793 : Nat := 4983230072969 + 3 ^ 40 * 7827793 * 2
def baseEnd_7827793 : Nat := 4019420272899997457588141

theorem tailTrace_7827793 : CollatzResearch.WordTrace tailWord_7827793 prefixEnd_7827793 4019420272899997457588141 := by
  unfold tailWord_7827793
  simp only [CollatzResearch.WordTrace]
  refine ⟨285503065730250316455008033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190335377153500210970005355 285503065730250316455008033)
  ·
    refine ⟨214127299297687737341256025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285503065730250316455008033 214127299297687737341256025)
    ·
      refine ⟨160595474473265803005942019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214127299297687737341256025 160595474473265803005942019)
      ·
        refine ⟨240893211709898704508913029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160595474473265803005942019 240893211709898704508913029)
        ·
          refine ⟨45167477195606007095421193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240893211709898704508913029 45167477195606007095421193)
          ·
            refine ⟨33875607896704505321565895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45167477195606007095421193 33875607896704505321565895)
            ·
              refine ⟨50813411845056757982348843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875607896704505321565895 50813411845056757982348843)
              ·
                refine ⟨76220117767585136973523265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50813411845056757982348843 76220117767585136973523265)
                ·
                  refine ⟨57165088325688852730142449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76220117767585136973523265 57165088325688852730142449)
                  ·
                    refine ⟨42873816244266639547606837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57165088325688852730142449 42873816244266639547606837)
                    ·
                      refine ⟨4019420272899997457588141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42873816244266639547606837 4019420272899997457588141)
                      ·
                        rfl

theorem cell23_7827793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_7827793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827793 prefixEnd_7827793 := by exact prefixLift 7827793
  have htrace : WordTrace (prefixWord ++ tailWord_7827793) baseStart_7827793 baseEnd_7827793 := by
    simpa [prefixWord, tailWord_7827793, baseEnd_7827793] using wordTrace_append hprefix tailTrace_7827793
  have hstable : (prefixWord ++ tailWord_7827793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827793).length < 2 ^ (prefixWord ++ tailWord_7827793).sum := by decide
  have hdescent : baseEnd_7827793 < baseStart_7827793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827807 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 1, 3, 2]
def baseStart_7827807 : Nat := 118140960795 + 7827807 * 2 ^ 59
def prefixEnd_7827807 : Nat := 4983230072969 + 3 ^ 40 * 7827807 * 2
def baseEnd_7827807 : Nat := 4019427461629160402813077

theorem tailTrace_7827807 : CollatzResearch.WordTrace tailWord_7827807 prefixEnd_7827807 4019427461629160402813077 := by
  unfold tailWord_7827807
  simp only [CollatzResearch.WordTrace]
  refine ⟨285503576352199596846017675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190335717568133064564011783 285503576352199596846017675)
  ·
    refine ⟨428255364528299395269026513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285503576352199596846017675 428255364528299395269026513)
    ·
      refine ⟨321191523396224546451769885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428255364528299395269026513 321191523396224546451769885)
      ·
        refine ⟨120446821273584204919413707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321191523396224546451769885 120446821273584204919413707)
        ·
          refine ⟨180670231910376307379120561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120446821273584204919413707 180670231910376307379120561)
          ·
            refine ⟨135502673932782230534340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180670231910376307379120561 135502673932782230534340421)
            ·
              refine ⟨25406751362396668225188829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135502673932782230534340421 25406751362396668225188829)
              ·
                refine ⟨9527531760898750584445811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25406751362396668225188829 9527531760898750584445811)
                ·
                  refine ⟨14291297641348125876668717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527531760898750584445811 14291297641348125876668717)
                  ·
                    refine ⟨5359236615505547203750769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14291297641348125876668717 5359236615505547203750769)
                    ·
                      refine ⟨4019427461629160402813077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359236615505547203750769 4019427461629160402813077)
                      ·
                        rfl

theorem cell23_7827807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_7827807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827807 prefixEnd_7827807 := by exact prefixLift 7827807
  have htrace : WordTrace (prefixWord ++ tailWord_7827807) baseStart_7827807 baseEnd_7827807 := by
    simpa [prefixWord, tailWord_7827807, baseEnd_7827807] using wordTrace_append hprefix tailTrace_7827807
  have hstable : (prefixWord ++ tailWord_7827807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827807).length < 2 ^ (prefixWord ++ tailWord_7827807).sum := by decide
  have hdescent : baseEnd_7827807 < baseStart_7827807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827833 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7827833 : Nat := 118140960795 + 7827833 * 2 ^ 59
def prefixEnd_7827833 : Nat := 4983230072969 + 3 ^ 40 * 7827833 * 2
def baseEnd_7827833 : Nat := 4019440812126177301087957

theorem tailTrace_7827833 : CollatzResearch.WordTrace tailWord_7827833 prefixEnd_7827833 4019440812126177301087957 := by
  unfold tailWord_7827833
  simp only [CollatzResearch.WordTrace]
  refine ⟨285504524650105403286464153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190336349766736935524309435 285504524650105403286464153)
  ·
    refine ⟨214128393487579052464848115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285504524650105403286464153 214128393487579052464848115)
    ·
      refine ⟨321192590231368578697272173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214128393487579052464848115 321192590231368578697272173)
      ·
        refine ⟨120447221336763217011477065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321192590231368578697272173 120447221336763217011477065)
        ·
          refine ⟨90335416002572412758607799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120447221336763217011477065 90335416002572412758607799)
          ·
            refine ⟨135503124003858619137911699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90335416002572412758607799 135503124003858619137911699)
            ·
              refine ⟨203254686005787928706867549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135503124003858619137911699 203254686005787928706867549)
              ·
                refine ⟨76220507252170473265075331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203254686005787928706867549 76220507252170473265075331)
                ·
                  refine ⟨114330760878255709897612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76220507252170473265075331 114330760878255709897612997)
                  ·
                    refine ⟨21437017664672945605802437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114330760878255709897612997 21437017664672945605802437)
                    ·
                      refine ⟨4019440812126177301087957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21437017664672945605802437 4019440812126177301087957)
                      ·
                        rfl

theorem cell23_7827833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7827833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827833 prefixEnd_7827833 := by exact prefixLift 7827833
  have htrace : WordTrace (prefixWord ++ tailWord_7827833) baseStart_7827833 baseEnd_7827833 := by
    simpa [prefixWord, tailWord_7827833, baseEnd_7827833] using wordTrace_append hprefix tailTrace_7827833
  have hstable : (prefixWord ++ tailWord_7827833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827833).length < 2 ^ (prefixWord ++ tailWord_7827833).sum := by decide
  have hdescent : baseEnd_7827833 < baseStart_7827833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827841 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7827841 : Nat := 118140960795 + 7827841 * 2 ^ 59
def prefixEnd_7827841 : Nat := 4983230072969 + 3 ^ 40 * 7827841 * 2
def baseEnd_7827841 : Nat := 4019444919971413269787921

theorem tailTrace_7827841 : CollatzResearch.WordTrace tailWord_7827841 prefixEnd_7827841 4019444919971413269787921 := by
  unfold tailWord_7827841
  simp only [CollatzResearch.WordTrace]
  refine ⟨285504816434076420652755377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190336544289384280435170251 285504816434076420652755377)
  ·
    refine ⟨214128612325557315489566533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285504816434076420652755377 214128612325557315489566533)
    ·
      refine ⟨40149114811041996654293725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214128612325557315489566533 40149114811041996654293725)
      ·
        refine ⟨15055918054140748745360147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40149114811041996654293725 15055918054140748745360147)
        ·
          refine ⟨22583877081211123118040221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055918054140748745360147 22583877081211123118040221)
          ·
            refine ⟨8468953905454171169265083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22583877081211123118040221 8468953905454171169265083)
            ·
              refine ⟨12703430858181256753897625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468953905454171169265083 12703430858181256753897625)
              ·
                refine ⟨9527573143635942565423219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703430858181256753897625 9527573143635942565423219)
                ·
                  refine ⟨14291359715453913848134829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527573143635942565423219 14291359715453913848134829)
                  ·
                    refine ⟨5359259893295217693050561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14291359715453913848134829 5359259893295217693050561)
                    ·
                      refine ⟨4019444919971413269787921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359259893295217693050561 4019444919971413269787921)
                      ·
                        rfl

theorem cell23_7827841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7827841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827841 prefixEnd_7827841 := by exact prefixLift 7827841
  have htrace : WordTrace (prefixWord ++ tailWord_7827841) baseStart_7827841 baseEnd_7827841 := by
    simpa [prefixWord, tailWord_7827841, baseEnd_7827841] using wordTrace_append hprefix tailTrace_7827841
  have hstable : (prefixWord ++ tailWord_7827841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827841).length < 2 ^ (prefixWord ++ tailWord_7827841).sum := by decide
  have hdescent : baseEnd_7827841 < baseStart_7827841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827854 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7827854 : Nat := 118140960795 + 7827854 * 2 ^ 59
def prefixEnd_7827854 : Nat := 4983230072969 + 3 ^ 40 * 7827854 * 2
def baseEnd_7827854 : Nat := 4019451595219921718925361

theorem tailTrace_7827854 : CollatzResearch.WordTrace tailWord_7827854 prefixEnd_7827854 4019451595219921718925361 := by
  unfold tailWord_7827854
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688161322878665484122327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190336860388686215915319077 35688161322878665484122327)
  ·
    refine ⟨53532241984317998226183491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688161322878665484122327 53532241984317998226183491)
    ·
      refine ⟨80298362976476997339275237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53532241984317998226183491 80298362976476997339275237)
      ·
        refine ⟨15055943058089437001114107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80298362976476997339275237 15055943058089437001114107)
        ·
          refine ⟨22583914587134155501671161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055943058089437001114107 22583914587134155501671161)
          ·
            refine ⟨16937935940350616626253371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22583914587134155501671161 16937935940350616626253371)
            ·
              refine ⟨25406903910525924939380057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16937935940350616626253371 25406903910525924939380057)
              ·
                refine ⟨19055177932894443704535043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25406903910525924939380057 19055177932894443704535043)
                ·
                  refine ⟨28582766899341665556802565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19055177932894443704535043 28582766899341665556802565)
                  ·
                    refine ⟨5359268793626562291900481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28582766899341665556802565 5359268793626562291900481)
                    ·
                      refine ⟨4019451595219921718925361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359268793626562291900481 4019451595219921718925361)
                      ·
                        rfl

theorem cell23_7827854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7827854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827854 prefixEnd_7827854 := by exact prefixLift 7827854
  have htrace : WordTrace (prefixWord ++ tailWord_7827854) baseStart_7827854 baseEnd_7827854 := by
    simpa [prefixWord, tailWord_7827854, baseEnd_7827854] using wordTrace_append hprefix tailTrace_7827854
  have hstable : (prefixWord ++ tailWord_7827854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827854).length < 2 ^ (prefixWord ++ tailWord_7827854).sum := by decide
  have hdescent : baseEnd_7827854 < baseStart_7827854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827937 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_7827937 : Nat := 118140960795 + 7827937 * 2 ^ 59
def prefixEnd_7827937 : Nat := 4983230072969 + 3 ^ 40 * 7827937 * 2
def baseEnd_7827937 : Nat := 1339831404704748298062493

theorem tailTrace_7827937 : CollatzResearch.WordTrace tailWord_7827937 prefixEnd_7827937 1339831404704748298062493 := by
  unfold tailWord_7827937
  simp only [CollatzResearch.WordTrace]
  refine ⟨285508317841728629048250065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190338878561152419365500043 285508317841728629048250065)
  ·
    refine ⟨214131238381296471786187549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285508317841728629048250065 214131238381296471786187549)
    ·
      refine ⟨80299214392986176919820331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214131238381296471786187549 80299214392986176919820331)
      ·
        refine ⟨120448821589479265379730497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80299214392986176919820331 120448821589479265379730497)
        ·
          refine ⟨90336616192109449034797873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120448821589479265379730497 90336616192109449034797873)
          ·
            refine ⟨67752462144082086776098405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90336616192109449034797873 67752462144082086776098405)
            ·
              refine ⟨12703586652015391270518451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67752462144082086776098405 12703586652015391270518451)
              ·
                refine ⟨19055379978023086905777677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703586652015391270518451 19055379978023086905777677)
                ·
                  refine ⟨7145767491758657589666629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19055379978023086905777677 7145767491758657589666629)
                  ·
                    refine ⟨1339831404704748298062493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145767491758657589666629 1339831404704748298062493)
                    ·
                      rfl

theorem cell23_7827937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_7827937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827937 prefixEnd_7827937 := by exact prefixLift 7827937
  have htrace : WordTrace (prefixWord ++ tailWord_7827937) baseStart_7827937 baseEnd_7827937 := by
    simpa [prefixWord, tailWord_7827937, baseEnd_7827937] using wordTrace_append hprefix tailTrace_7827937
  have hstable : (prefixWord ++ tailWord_7827937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827937).length < 2 ^ (prefixWord ++ tailWord_7827937).sum := by decide
  have hdescent : baseEnd_7827937 < baseStart_7827937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827960 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_7827960 : Nat := 118140960795 + 7827960 * 2 ^ 59
def prefixEnd_7827960 : Nat := 4983230072969 + 3 ^ 40 * 7827960 * 2
def baseEnd_7827960 : Nat := 4019506024169298304199873

theorem tailTrace_7827960 : CollatzResearch.WordTrace tailWord_7827960 prefixEnd_7827960 4019506024169298304199873 := by
  unfold tailWord_7827960
  simp only [CollatzResearch.WordTrace]
  refine ⟨142754578360322651988168667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190339437813763535984224889 142754578360322651988168667)
  ·
    refine ⟨214131867540483977982253001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142754578360322651988168667 214131867540483977982253001)
    ·
      refine ⟨160598900655362983486689751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214131867540483977982253001 160598900655362983486689751)
      ·
        refine ⟨240898350983044475230034627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160598900655362983486689751 240898350983044475230034627)
        ·
          refine ⟨361347526474566712845051941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240898350983044475230034627 361347526474566712845051941)
          ·
            refine ⟨67752661213981258658447239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361347526474566712845051941 67752661213981258658447239)
            ·
              refine ⟨101628991820971887987670859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67752661213981258658447239 101628991820971887987670859)
              ·
                refine ⟨152443487731457831981506289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101628991820971887987670859 152443487731457831981506289)
                ·
                  refine ⟨114332615798593373986129717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152443487731457831981506289 114332615798593373986129717)
                  ·
                    refine ⟨10718682731118128811199661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114332615798593373986129717 10718682731118128811199661)
                    ·
                      refine ⟨4019506024169298304199873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718682731118128811199661 4019506024169298304199873)
                      ·
                        rfl

theorem cell23_7827960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_7827960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827960 prefixEnd_7827960 := by exact prefixLift 7827960
  have htrace : WordTrace (prefixWord ++ tailWord_7827960) baseStart_7827960 baseEnd_7827960 := by
    simpa [prefixWord, tailWord_7827960, baseEnd_7827960] using wordTrace_append hprefix tailTrace_7827960
  have hstable : (prefixWord ++ tailWord_7827960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827960).length < 2 ^ (prefixWord ++ tailWord_7827960).sum := by decide
  have hdescent : baseEnd_7827960 < baseStart_7827960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827981 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7827981 : Nat := 118140960795 + 7827981 * 2 ^ 59
def prefixEnd_7827981 : Nat := 4983230072969 + 3 ^ 40 * 7827981 * 2
def baseEnd_7827981 : Nat := 4019516807263042722037277

theorem tailTrace_7827981 : CollatzResearch.WordTrace tailWord_7827981 prefixEnd_7827981 4019516807263042722037277 := by
  unfold tailWord_7827981
  simp only [CollatzResearch.WordTrace]
  refine ⟨285509922653569224562851797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190339948435712816375234531 285509922653569224562851797)
  ·
    refine ⟨6691638812193028700691839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 285509922653569224562851797 6691638812193028700691839)
    ·
      refine ⟨10037458218289543051037759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691638812193028700691839 10037458218289543051037759)
      ·
        refine ⟨15056187327434314576556639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037458218289543051037759 15056187327434314576556639)
        ·
          refine ⟨22584280991151471864834959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056187327434314576556639 22584280991151471864834959)
          ·
            refine ⟨33876421486727207797252439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22584280991151471864834959 33876421486727207797252439)
            ·
              refine ⟨50814632230090811695878659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33876421486727207797252439 50814632230090811695878659)
              ·
                refine ⟨76221948345136217543817989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50814632230090811695878659 76221948345136217543817989)
                ·
                  refine ⟨14291615314713040789465873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76221948345136217543817989 14291615314713040789465873)
                  ·
                    refine ⟨10718711486034780592099405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14291615314713040789465873 10718711486034780592099405)
                    ·
                      refine ⟨4019516807263042722037277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718711486034780592099405 4019516807263042722037277)
                      ·
                        rfl

theorem cell23_7827981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7827981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827981 prefixEnd_7827981 := by exact prefixLift 7827981
  have htrace : WordTrace (prefixWord ++ tailWord_7827981) baseStart_7827981 baseEnd_7827981 := by
    simpa [prefixWord, tailWord_7827981, baseEnd_7827981] using wordTrace_append hprefix tailTrace_7827981
  have hstable : (prefixWord ++ tailWord_7827981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827981).length < 2 ^ (prefixWord ++ tailWord_7827981).sum := by decide
  have hdescent : baseEnd_7827981 < baseStart_7827981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7827994 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_7827994 : Nat := 118140960795 + 7827994 * 2 ^ 59
def prefixEnd_7827994 : Nat := 4983230072969 + 3 ^ 40 * 7827994 * 2
def baseEnd_7827994 : Nat := 4019523482511551171174717

theorem tailTrace_7827994 : CollatzResearch.WordTrace tailWord_7827994 prefixEnd_7827994 4019523482511551171174717 := by
  unfold tailWord_7827994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71377599200630531945768759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190340264535014751855383357 71377599200630531945768759)
  ·
    refine ⟨107066398800945797918653139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71377599200630531945768759 107066398800945797918653139)
    ·
      refine ⟨160599598201418696877979709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107066398800945797918653139 160599598201418696877979709)
      ·
        refine ⟨60224849325532011329242391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160599598201418696877979709 60224849325532011329242391)
        ·
          refine ⟨90337273988298016993863587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60224849325532011329242391 90337273988298016993863587)
          ·
            refine ⟨135505910982447025490795381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90337273988298016993863587 135505910982447025490795381)
            ·
              refine ⟨12703679154604408639762067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135505910982447025490795381 12703679154604408639762067)
              ·
                refine ⟨19055518731906612959643101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703679154604408639762067 19055518731906612959643101)
                ·
                  refine ⟨7145819524464979859866163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19055518731906612959643101 7145819524464979859866163)
                  ·
                    refine ⟨10718729286697469789799245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145819524464979859866163 10718729286697469789799245)
                    ·
                      refine ⟨4019523482511551171174717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718729286697469789799245 4019523482511551171174717)
                      ·
                        rfl

theorem cell23_7827994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_7827994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7827994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7827994 prefixEnd_7827994 := by exact prefixLift 7827994
  have htrace : WordTrace (prefixWord ++ tailWord_7827994) baseStart_7827994 baseEnd_7827994 := by
    simpa [prefixWord, tailWord_7827994, baseEnd_7827994] using wordTrace_append hprefix tailTrace_7827994
  have hstable : (prefixWord ++ tailWord_7827994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7827994).length < 2 ^ (prefixWord ++ tailWord_7827994).sum := by decide
  have hdescent : baseEnd_7827994 < baseStart_7827994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7827994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828014 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7828014 : Nat := 118140960795 + 7828014 * 2 ^ 59
def prefixEnd_7828014 : Nat := 4983230072969 + 3 ^ 40 * 7828014 * 2
def baseEnd_7828014 : Nat := 1339844584041547030974875

theorem tailTrace_7828014 : CollatzResearch.WordTrace tailWord_7828014 prefixEnd_7828014 1339844584041547030974875 := by
  unfold tailWord_7828014
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688890782806208899850387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190340750841633114132535397 35688890782806208899850387)
  ·
    refine ⟨53533336174209313349775581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688890782806208899850387 53533336174209313349775581)
    ·
      refine ⟨20075001065328492506165843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53533336174209313349775581 20075001065328492506165843)
      ·
        refine ⟨30112501597992738759248765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075001065328492506165843 30112501597992738759248765)
        ·
          refine ⟨11292188099247277034718287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30112501597992738759248765 11292188099247277034718287)
          ·
            refine ⟨16938282148870915552077431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292188099247277034718287 16938282148870915552077431)
            ·
              refine ⟨25407423223306373328116147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16938282148870915552077431 25407423223306373328116147)
              ·
                refine ⟨38111134834959559992174221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25407423223306373328116147 38111134834959559992174221)
                ·
                  refine ⟨14291675563109834997065333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38111134834959559992174221 14291675563109834997065333)
                  ·
                    refine ⟨1339844584041547030974875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14291675563109834997065333 1339844584041547030974875)
                    ·
                      rfl

theorem cell23_7828014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7828014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828014 prefixEnd_7828014 := by exact prefixLift 7828014
  have htrace : WordTrace (prefixWord ++ tailWord_7828014) baseStart_7828014 baseEnd_7828014 := by
    simpa [prefixWord, tailWord_7828014, baseEnd_7828014] using wordTrace_append hprefix tailTrace_7828014
  have hstable : (prefixWord ++ tailWord_7828014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828014).length < 2 ^ (prefixWord ++ tailWord_7828014).sum := by decide
  have hdescent : baseEnd_7828014 < baseStart_7828014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828017 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_7828017 : Nat := 118140960795 + 7828017 * 2 ^ 59
def prefixEnd_7828017 : Nat := 4983230072969 + 3 ^ 40 * 7828017 * 2
def baseEnd_7828017 : Nat := 4019535292566604581187111

theorem tailTrace_7828017 : CollatzResearch.WordTrace tailWord_7828017 prefixEnd_7828017 4019535292566604581187111 := by
  unfold tailWord_7828017
  simp only [CollatzResearch.WordTrace]
  refine ⟨285511235681438802711162305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190340823787625868474108203 285511235681438802711162305)
  ·
    refine ⟨214133426761079102033371729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285511235681438802711162305 214133426761079102033371729)
    ·
      refine ⟨160600070070809326525028797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214133426761079102033371729 160600070070809326525028797)
      ·
        refine ⟨60225026276553497446885799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160600070070809326525028797 60225026276553497446885799)
        ·
          refine ⟨90337539414830246170328699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60225026276553497446885799 90337539414830246170328699)
          ·
            refine ⟨135506309122245369255493049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90337539414830246170328699 135506309122245369255493049)
            ·
              refine ⟨101629731841684026941619787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135506309122245369255493049 101629731841684026941619787)
              ·
                refine ⟨152444597762526040412429681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101629731841684026941619787 152444597762526040412429681)
                ·
                  refine ⟨114333448321894530309322261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152444597762526040412429681 114333448321894530309322261)
                  ·
                    refine ⟨5359380390088806108249481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114333448321894530309322261 5359380390088806108249481)
                    ·
                      refine ⟨4019535292566604581187111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359380390088806108249481 4019535292566604581187111)
                      ·
                        rfl

theorem cell23_7828017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_7828017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828017 prefixEnd_7828017 := by exact prefixLift 7828017
  have htrace : WordTrace (prefixWord ++ tailWord_7828017) baseStart_7828017 baseEnd_7828017 := by
    simpa [prefixWord, tailWord_7828017, baseEnd_7828017] using wordTrace_append hprefix tailTrace_7828017
  have hstable : (prefixWord ++ tailWord_7828017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828017).length < 2 ^ (prefixWord ++ tailWord_7828017).sum := by decide
  have hdescent : baseEnd_7828017 < baseStart_7828017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828037 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_7828037 : Nat := 118140960795 + 7828037 * 2 ^ 59
def prefixEnd_7828037 : Nat := 4983230072969 + 3 ^ 40 * 7828037 * 2
def baseEnd_7828037 : Nat := 4019545562179694502937019

theorem tailTrace_7828037 : CollatzResearch.WordTrace tailWord_7828037 prefixEnd_7828037 4019545562179694502937019 := by
  unfold tailWord_7828037
  simp only [CollatzResearch.WordTrace]
  refine ⟨285511965141366346126890365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190341310094244230751260243 285511965141366346126890365)
  ·
    refine ⟨107066986928012379797583887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285511965141366346126890365 107066986928012379797583887)
    ·
      refine ⟨160600480392018569696375831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107066986928012379797583887 160600480392018569696375831)
      ·
        refine ⟨240900720588027854544563747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160600480392018569696375831 240900720588027854544563747)
        ·
          refine ⟨361351080882041781816845621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240900720588027854544563747 361351080882041781816845621)
          ·
            refine ⟨33876663832691417045329277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361351080882041781816845621 33876663832691417045329277)
            ·
              refine ⟨12703748937259281391998479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33876663832691417045329277 12703748937259281391998479)
              ·
                refine ⟨19055623405888922087997719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703748937259281391998479 19055623405888922087997719)
                ·
                  refine ⟨28583435108833383131996579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19055623405888922087997719 28583435108833383131996579)
                  ·
                    refine ⟨42875152663250074697994869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28583435108833383131996579 42875152663250074697994869)
                    ·
                      refine ⟨4019545562179694502937019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42875152663250074697994869 4019545562179694502937019)
                      ·
                        rfl

theorem cell23_7828037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_7828037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828037 prefixEnd_7828037 := by exact prefixLift 7828037
  have htrace : WordTrace (prefixWord ++ tailWord_7828037) baseStart_7828037 baseEnd_7828037 := by
    simpa [prefixWord, tailWord_7828037, baseEnd_7828037] using wordTrace_append hprefix tailTrace_7828037
  have hstable : (prefixWord ++ tailWord_7828037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828037).length < 2 ^ (prefixWord ++ tailWord_7828037).sum := by decide
  have hdescent : baseEnd_7828037 < baseStart_7828037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828038 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7828038 : Nat := 118140960795 + 7828038 * 2 ^ 59
def prefixEnd_7828038 : Nat := 4983230072969 + 3 ^ 40 * 7828038 * 2
def baseEnd_7828038 : Nat := 4019546075660348999024515

theorem tailTrace_7828038 : CollatzResearch.WordTrace tailWord_7828038 prefixEnd_7828038 4019546075660348999024515 := by
  unfold tailWord_7828038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922250050448835103052399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190341334409575148865117845 8922250050448835103052399)
  ·
    refine ⟨13383375075673252654578599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922250050448835103052399 13383375075673252654578599)
    ·
      refine ⟨20075062613509878981867899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383375075673252654578599 20075062613509878981867899)
      ·
        refine ⟨30112593920264818472801849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075062613509878981867899 30112593920264818472801849)
        ·
          refine ⟨22584445440198613854601387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30112593920264818472801849 22584445440198613854601387)
          ·
            refine ⟨33876668160297920781902081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22584445440198613854601387 33876668160297920781902081)
            ·
              refine ⟨25407501120223440586426561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33876668160297920781902081 25407501120223440586426561)
              ·
                refine ⟨19055625840167580439819921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25407501120223440586426561 19055625840167580439819921)
                ·
                  refine ⟨14291719380125685329864941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19055625840167580439819921 14291719380125685329864941)
                  ·
                    refine ⟨5359394767547131998699353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14291719380125685329864941 5359394767547131998699353)
                    ·
                      refine ⟨4019546075660348999024515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359394767547131998699353 4019546075660348999024515)
                      ·
                        rfl

theorem cell23_7828038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7828038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828038 prefixEnd_7828038 := by exact prefixLift 7828038
  have htrace : WordTrace (prefixWord ++ tailWord_7828038) baseStart_7828038 baseEnd_7828038 := by
    simpa [prefixWord, tailWord_7828038, baseEnd_7828038] using wordTrace_append hprefix tailTrace_7828038
  have hstable : (prefixWord ++ tailWord_7828038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828038).length < 2 ^ (prefixWord ++ tailWord_7828038).sum := by decide
  have hdescent : baseEnd_7828038 < baseStart_7828038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828044 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_7828044 : Nat := 118140960795 + 7828044 * 2 ^ 59
def prefixEnd_7828044 : Nat := 4983230072969 + 3 ^ 40 * 7828044 * 2
def baseEnd_7828044 : Nat := 1339849718848091991849829

theorem tailTrace_7828044 : CollatzResearch.WordTrace tailWord_7828044 prefixEnd_7828044 1339849718848091991849829 := by
  unfold tailWord_7828044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142756110226170493161197593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190341480301560657548263457 142756110226170493161197593)
  ·
    refine ⟨107067082669627869870898195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142756110226170493161197593 107067082669627869870898195)
    ·
      refine ⟨160600624004441804806347293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107067082669627869870898195 160600624004441804806347293)
      ·
        refine ⟨60225234001665676802380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160600624004441804806347293 60225234001665676802380235)
        ·
          refine ⟨90337851002498515203570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60225234001665676802380235 90337851002498515203570353)
          ·
            refine ⟨67753388251873886402677765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90337851002498515203570353 67753388251873886402677765)
            ·
              refine ⟨12703760297226353700502081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67753388251873886402677765 12703760297226353700502081)
              ·
                refine ⟨9527820222919765275376561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703760297226353700502081 9527820222919765275376561)
                ·
                  refine ⟨7145865167189823956532421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527820222919765275376561 7145865167189823956532421)
                  ·
                    refine ⟨1339849718848091991849829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145865167189823956532421 1339849718848091991849829)
                    ·
                      rfl

theorem cell23_7828044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_7828044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828044 prefixEnd_7828044 := by exact prefixLift 7828044
  have htrace : WordTrace (prefixWord ++ tailWord_7828044) baseStart_7828044 baseEnd_7828044 := by
    simpa [prefixWord, tailWord_7828044, baseEnd_7828044] using wordTrace_append hprefix tailTrace_7828044
  have hstable : (prefixWord ++ tailWord_7828044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828044).length < 2 ^ (prefixWord ++ tailWord_7828044).sum := by decide
  have hdescent : baseEnd_7828044 < baseStart_7828044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828045 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_7828045 : Nat := 118140960795 + 7828045 * 2 ^ 59
def prefixEnd_7828045 : Nat := 4983230072969 + 3 ^ 40 * 7828045 * 2
def baseEnd_7828045 : Nat := 4019549670024930471636983

theorem tailTrace_7828045 : CollatzResearch.WordTrace tailWord_7828045 prefixEnd_7828045 4019549670024930471636983 := by
  unfold tailWord_7828045
  simp only [CollatzResearch.WordTrace]
  refine ⟨285512256925337363493181589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190341504616891575662121059 285512256925337363493181589)
  ·
    refine ⟨13383387043375188913742887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285512256925337363493181589 13383387043375188913742887)
    ·
      refine ⟨20075080565062783370614331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383387043375188913742887 20075080565062783370614331)
      ·
        refine ⟨30112620847594175055921497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075080565062783370614331 30112620847594175055921497)
        ·
          refine ⟨22584465635695631291941123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30112620847594175055921497 22584465635695631291941123)
          ·
            refine ⟨33876698453543446937911685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22584465635695631291941123 33876698453543446937911685)
            ·
              refine ⟨6351880960039396300858441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33876698453543446937911685 6351880960039396300858441)
              ·
                refine ⟨4763910720029547225643831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351880960039396300858441 4763910720029547225643831)
                ·
                  refine ⟨7145866080044320838465747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763910720029547225643831 7145866080044320838465747)
                  ·
                    refine ⟨10718799120066481257698621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145866080044320838465747 10718799120066481257698621)
                    ·
                      refine ⟨4019549670024930471636983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718799120066481257698621 4019549670024930471636983)
                      ·
                        rfl

theorem cell23_7828045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_7828045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828045 prefixEnd_7828045 := by exact prefixLift 7828045
  have htrace : WordTrace (prefixWord ++ tailWord_7828045) baseStart_7828045 baseEnd_7828045 := by
    simpa [prefixWord, tailWord_7828045, baseEnd_7828045] using wordTrace_append hprefix tailTrace_7828045
  have hstable : (prefixWord ++ tailWord_7828045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828045).length < 2 ^ (prefixWord ++ tailWord_7828045).sum := by decide
  have hdescent : baseEnd_7828045 < baseStart_7828045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828085 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7828085 : Nat := 118140960795 + 7828085 * 2 ^ 59
def prefixEnd_7828085 : Nat := 4983230072969 + 3 ^ 40 * 7828085 * 2
def baseEnd_7828085 : Nat := 4019570209251110315136799

theorem tailTrace_7828085 : CollatzResearch.WordTrace tailWord_7828085 prefixEnd_7828085 4019570209251110315136799 := by
  unfold tailWord_7828085
  simp only [CollatzResearch.WordTrace]
  refine ⟨285513715845192450324637709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190342477230128300216425139 285513715845192450324637709)
  ·
    refine ⟨107067643441947168871739141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285513715845192450324637709 107067643441947168871739141)
    ·
      refine ⟨20075183145365094163451089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107067643441947168871739141 20075183145365094163451089)
      ·
        refine ⟨15056387359023820622588317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20075183145365094163451089 15056387359023820622588317)
        ·
          refine ⟨5646145259633932733470619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15056387359023820622588317 5646145259633932733470619)
          ·
            refine ⟨8469217889450899100205929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646145259633932733470619 8469217889450899100205929)
            ·
              refine ⟨6351913417088174325154447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8469217889450899100205929 6351913417088174325154447)
              ·
                refine ⟨9527870125632261487731671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351913417088174325154447 9527870125632261487731671)
                ·
                  refine ⟨14291805188448392231597507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527870125632261487731671 14291805188448392231597507)
                  ·
                    refine ⟨21437707782672588347396261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14291805188448392231597507 21437707782672588347396261)
                    ·
                      refine ⟨4019570209251110315136799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21437707782672588347396261 4019570209251110315136799)
                      ·
                        rfl

theorem cell23_7828085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7828085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828085 prefixEnd_7828085 := by exact prefixLift 7828085
  have htrace : WordTrace (prefixWord ++ tailWord_7828085) baseStart_7828085 baseEnd_7828085 := by
    simpa [prefixWord, tailWord_7828085, baseEnd_7828085] using wordTrace_append hprefix tailTrace_7828085
  have hstable : (prefixWord ++ tailWord_7828085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828085).length < 2 ^ (prefixWord ++ tailWord_7828085).sum := by decide
  have hdescent : baseEnd_7828085 < baseStart_7828085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828101 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_7828101 : Nat := 118140960795 + 7828101 * 2 ^ 59
def prefixEnd_7828101 : Nat := 4983230072969 + 3 ^ 40 * 7828101 * 2
def baseEnd_7828101 : Nat := 4019578424941582252536725

theorem tailTrace_7828101 : CollatzResearch.WordTrace tailWord_7828101 prefixEnd_7828101 4019578424941582252536725 := by
  unfold tailWord_7828101
  simp only [CollatzResearch.WordTrace]
  refine ⟨285514299413134485057220157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190342866275422990038146771 285514299413134485057220157)
  ·
    refine ⟨107067862279925431896457559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285514299413134485057220157 107067862279925431896457559)
    ·
      refine ⟨160601793419888147844686339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107067862279925431896457559 160601793419888147844686339)
      ·
        refine ⟨240902690129832221767029509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160601793419888147844686339 240902690129832221767029509)
        ·
          refine ⟨45169254399343541581318033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240902690129832221767029509 45169254399343541581318033)
          ·
            refine ⟨33876940799507656185988525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45169254399343541581318033 33876940799507656185988525)
            ·
              refine ⟨12703852799815371069745697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33876940799507656185988525 12703852799815371069745697)
              ·
                refine ⟨9527889599861528302309273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703852799815371069745697 9527889599861528302309273)
                ·
                  refine ⟨7145917199896146226731955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527889599861528302309273 7145917199896146226731955)
                  ·
                    refine ⟨10718875799844219340097933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145917199896146226731955 10718875799844219340097933)
                    ·
                      refine ⟨4019578424941582252536725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10718875799844219340097933 4019578424941582252536725)
                      ·
                        rfl

theorem cell23_7828101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_7828101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828101 prefixEnd_7828101 := by exact prefixLift 7828101
  have htrace : WordTrace (prefixWord ++ tailWord_7828101) baseStart_7828101 baseEnd_7828101 := by
    simpa [prefixWord, tailWord_7828101, baseEnd_7828101] using wordTrace_append hprefix tailTrace_7828101
  have hstable : (prefixWord ++ tailWord_7828101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828101).length < 2 ^ (prefixWord ++ tailWord_7828101).sum := by decide
  have hdescent : baseEnd_7828101 < baseStart_7828101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828128 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2]
def baseStart_7828128 : Nat := 118140960795 + 7828128 * 2 ^ 59
def prefixEnd_7828128 : Nat := 4983230072969 + 3 ^ 40 * 7828128 * 2
def baseEnd_7828128 : Nat := 4019592288919253646899101

theorem tailTrace_7828128 : CollatzResearch.WordTrace tailWord_7828128 prefixEnd_7828128 4019592288919253646899101 := by
  unfold tailWord_7828128
  simp only [CollatzResearch.WordTrace]
  refine ⟨142757642092018334334226519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190343522789357779112302025 142757642092018334334226519)
  ·
    refine ⟨214136463138027501501339779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142757642092018334334226519 214136463138027501501339779)
    ·
      refine ⟨321204694707041252252009669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214136463138027501501339779 321204694707041252252009669)
      ·
        refine ⟨60225880257570234797251813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321204694707041252252009669 60225880257570234797251813)
        ·
          refine ⟨11292352548294419024484715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60225880257570234797251813 11292352548294419024484715)
          ·
            refine ⟨16938528822441628536727073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292352548294419024484715 16938528822441628536727073)
            ·
              refine ⟨12703896616831221402545305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16938528822441628536727073 12703896616831221402545305)
              ·
                refine ⟨9527922462623416051908979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703896616831221402545305 9527922462623416051908979)
                ·
                  refine ⟨14291883693935124077863469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527922462623416051908979 14291883693935124077863469)
                  ·
                    refine ⟨5359456385225671529198801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14291883693935124077863469 5359456385225671529198801)
                    ·
                      refine ⟨4019592288919253646899101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359456385225671529198801 4019592288919253646899101)
                      ·
                        rfl

theorem cell23_7828128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_7828128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828128 prefixEnd_7828128 := by exact prefixLift 7828128
  have htrace : WordTrace (prefixWord ++ tailWord_7828128) baseStart_7828128 baseEnd_7828128 := by
    simpa [prefixWord, tailWord_7828128, baseEnd_7828128] using wordTrace_append hprefix tailTrace_7828128
  have hstable : (prefixWord ++ tailWord_7828128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828128).length < 2 ^ (prefixWord ++ tailWord_7828128).sum := by decide
  have hdescent : baseEnd_7828128 < baseStart_7828128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828158 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_7828158 : Nat := 118140960795 + 7828158 * 2 ^ 59
def prefixEnd_7828158 : Nat := 4983230072969 + 3 ^ 40 * 7828158 * 2
def baseEnd_7828158 : Nat := 4019607693338888529523963

theorem tailTrace_7828158 : CollatzResearch.WordTrace tailWord_7828158 prefixEnd_7828158 4019607693338888529523963 := by
  unfold tailWord_7828158
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689547296740997974005641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190344252249285322528030085 35689547296740997974005641)
  ·
    refine ⟨26767160472555748480504231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35689547296740997974005641 26767160472555748480504231)
    ·
      refine ⟨40150740708833622720756347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26767160472555748480504231 40150740708833622720756347)
      ·
        refine ⟨60226111063250434081134521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40150740708833622720756347 60226111063250434081134521)
        ·
          refine ⟨45169583297437825560850891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60226111063250434081134521 45169583297437825560850891)
          ·
            refine ⟨67754374946156738341276337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45169583297437825560850891 67754374946156738341276337)
            ·
              refine ⟨50815781209617553755957253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67754374946156738341276337 50815781209617553755957253)
              ·
                refine ⟨9527958976803291329241985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50815781209617553755957253 9527958976803291329241985)
                ·
                  refine ⟨7145969232602468496931489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527958976803291329241985 7145969232602468496931489)
                  ·
                    refine ⟨5359476924451851372698617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145969232602468496931489 5359476924451851372698617)
                    ·
                      refine ⟨4019607693338888529523963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359476924451851372698617 4019607693338888529523963)
                      ·
                        rfl

theorem cell23_7828158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_7828158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828158 prefixEnd_7828158 := by exact prefixLift 7828158
  have htrace : WordTrace (prefixWord ++ tailWord_7828158) baseStart_7828158 baseEnd_7828158 := by
    simpa [prefixWord, tailWord_7828158, baseEnd_7828158] using wordTrace_append hprefix tailTrace_7828158
  have hstable : (prefixWord ++ tailWord_7828158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828158).length < 2 ^ (prefixWord ++ tailWord_7828158).sum := by decide
  have hdescent : baseEnd_7828158 < baseStart_7828158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828164 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 7]
def baseStart_7828164 : Nat := 118140960795 + 7828164 * 2 ^ 59
def prefixEnd_7828164 : Nat := 4983230072969 + 3 ^ 40 * 7828164 * 2
def baseEnd_7828164 : Nat := 446623419358090611783215

theorem tailTrace_7828164 : CollatzResearch.WordTrace tailWord_7828164 prefixEnd_7828164 446623419358090611783215 := by
  unfold tailWord_7828164
  simp only [CollatzResearch.WordTrace]
  refine ⟨142758298605953123408381773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190344398141270831211175697 142758298605953123408381773)
  ·
    refine ⟨53534361977232421278143165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142758298605953123408381773 53534361977232421278143165)
    ·
      refine ⟨20075385741462157979303687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53534361977232421278143165 20075385741462157979303687)
      ·
        refine ⟨30113078612193236968955531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075385741462157979303687 30113078612193236968955531)
        ·
          refine ⟨45169617918289855453433297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113078612193236968955531 45169617918289855453433297)
          ·
            refine ⟨33877213438717391590074973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45169617918289855453433297 33877213438717391590074973)
            ·
              refine ⟨12703955039519021846278115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33877213438717391590074973 12703955039519021846278115)
              ·
                refine ⟨19055932559278532769417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703955039519021846278115 19055932559278532769417173)
                ·
                  refine ⟨446623419358090611783215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19055932559278532769417173 446623419358090611783215)
                  ·
                    rfl

theorem cell23_7828164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_7828164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828164 prefixEnd_7828164 := by exact prefixLift 7828164
  have htrace : WordTrace (prefixWord ++ tailWord_7828164) baseStart_7828164 baseEnd_7828164 := by
    simpa [prefixWord, tailWord_7828164, baseEnd_7828164] using wordTrace_append hprefix tailTrace_7828164
  have hstable : (prefixWord ++ tailWord_7828164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828164).length < 2 ^ (prefixWord ++ tailWord_7828164).sum := by decide
  have hdescent : baseEnd_7828164 < baseStart_7828164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828177 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_7828177 : Nat := 118140960795 + 7828177 * 2 ^ 59
def prefixEnd_7828177 : Nat := 4983230072969 + 3 ^ 40 * 7828177 * 2
def baseEnd_7828177 : Nat := 1339872483157107985062125

theorem tailTrace_7828177 : CollatzResearch.WordTrace tailWord_7828177 prefixEnd_7828177 1339872483157107985062125 := by
  unfold tailWord_7828177
  simp only [CollatzResearch.WordTrace]
  refine ⟨285517071360859150036986785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190344714240572766691324523 285517071360859150036986785)
  ·
    refine ⟨214137803520644362527740089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285517071360859150036986785 214137803520644362527740089)
    ·
      refine ⟨160603352640483271895805067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214137803520644362527740089 160603352640483271895805067)
      ·
        refine ⟨240905028960724907843707601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160603352640483271895805067 240905028960724907843707601)
        ·
          refine ⟨180678771720543680882780701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240905028960724907843707601 180678771720543680882780701)
          ·
            refine ⟨67754539395203880331042763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180678771720543680882780701 67754539395203880331042763)
            ·
              refine ⟨101631809092805820496564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67754539395203880331042763 101631809092805820496564145)
              ·
                refine ⟨76223856819604365372423109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101631809092805820496564145 76223856819604365372423109)
                ·
                  refine ⟨14291973153675818507329333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76223856819604365372423109 14291973153675818507329333)
                  ·
                    refine ⟨1339872483157107985062125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14291973153675818507329333 1339872483157107985062125)
                    ·
                      rfl

theorem cell23_7828177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_7828177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828177 prefixEnd_7828177 := by exact prefixLift 7828177
  have htrace : WordTrace (prefixWord ++ tailWord_7828177) baseStart_7828177 baseEnd_7828177 := by
    simpa [prefixWord, tailWord_7828177, baseEnd_7828177] using wordTrace_append hprefix tailTrace_7828177
  have hstable : (prefixWord ++ tailWord_7828177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828177).length < 2 ^ (prefixWord ++ tailWord_7828177).sum := by decide
  have hdescent : baseEnd_7828177 < baseStart_7828177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828227 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_7828227 : Nat := 118140960795 + 7828227 * 2 ^ 59
def prefixEnd_7828227 : Nat := 4983230072969 + 3 ^ 40 * 7828227 * 2
def baseEnd_7828227 : Nat := 4019643123504048759561145

theorem tailTrace_7828227 : CollatzResearch.WordTrace tailWord_7828227 prefixEnd_7828227 4019643123504048759561145 := by
  unfold tailWord_7828227
  simp only [CollatzResearch.WordTrace]
  refine ⟨285518895010678008576306935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190345930007118672384204623 285518895010678008576306935)
  ·
    refine ⟨428278342516017012864460403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285518895010678008576306935 428278342516017012864460403)
    ·
      refine ⟨642417513774025519296690605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428278342516017012864460403 642417513774025519296690605)
      ·
        refine ⟨240906567665259569736258977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642417513774025519296690605 240906567665259569736258977)
        ·
          refine ⟨180679925748944677302194233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240906567665259569736258977 180679925748944677302194233)
          ·
            refine ⟨135509944311708507976645675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180679925748944677302194233 135509944311708507976645675)
            ·
              refine ⟨203264916467562761964968513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135509944311708507976645675 203264916467562761964968513)
              ·
                refine ⟨152448687350672071473726385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203264916467562761964968513 152448687350672071473726385)
                ·
                  refine ⟨114336515513004053605294789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152448687350672071473726385 114336515513004053605294789)
                  ·
                    refine ⟨21438096658688260050992773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114336515513004053605294789 21438096658688260050992773)
                    ·
                      refine ⟨4019643123504048759561145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21438096658688260050992773 4019643123504048759561145)
                      ·
                        rfl

theorem cell23_7828227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_7828227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828227 prefixEnd_7828227 := by exact prefixLift 7828227
  have htrace : WordTrace (prefixWord ++ tailWord_7828227) baseStart_7828227 baseEnd_7828227 := by
    simpa [prefixWord, tailWord_7828227, baseEnd_7828227] using wordTrace_append hprefix tailTrace_7828227
  have hstable : (prefixWord ++ tailWord_7828227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828227).length < 2 ^ (prefixWord ++ tailWord_7828227).sum := by decide
  have hdescent : baseEnd_7828227 < baseStart_7828227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828231 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7828231 : Nat := 118140960795 + 7828231 * 2 ^ 59
def prefixEnd_7828231 : Nat := 4983230072969 + 3 ^ 40 * 7828231 * 2
def baseEnd_7828231 : Nat := 4019645177426666743911127

theorem tailTrace_7828231 : CollatzResearch.WordTrace tailWord_7828231 prefixEnd_7828231 4019645177426666743911127 := by
  unfold tailWord_7828231
  simp only [CollatzResearch.WordTrace]
  refine ⟨285519040902663517259452547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190346027268442344839635031 285519040902663517259452547)
  ·
    refine ⟨428278561353995275889178821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285519040902663517259452547 428278561353995275889178821)
    ·
      refine ⟨80302230253874114229221029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428278561353995275889178821 80302230253874114229221029)
      ·
        refine ⟨15056668172601396417978943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80302230253874114229221029 15056668172601396417978943)
        ·
          refine ⟨22585002258902094626968415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056668172601396417978943 22585002258902094626968415)
          ·
            refine ⟨33877503388353141940452623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22585002258902094626968415 33877503388353141940452623)
            ·
              refine ⟨50816255082529712910678935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33877503388353141940452623 50816255082529712910678935)
              ·
                refine ⟨76224382623794569366018403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50816255082529712910678935 76224382623794569366018403)
                ·
                  refine ⟨114336573935691854049027605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76224382623794569366018403 114336573935691854049027605)
                  ·
                    refine ⟨5359526903235555658548169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114336573935691854049027605 5359526903235555658548169)
                    ·
                      refine ⟨4019645177426666743911127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359526903235555658548169 4019645177426666743911127)
                      ·
                        rfl

theorem cell23_7828231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7828231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828231 prefixEnd_7828231 := by exact prefixLift 7828231
  have htrace : WordTrace (prefixWord ++ tailWord_7828231) baseStart_7828231 baseEnd_7828231 := by
    simpa [prefixWord, tailWord_7828231, baseEnd_7828231] using wordTrace_append hprefix tailTrace_7828231
  have hstable : (prefixWord ++ tailWord_7828231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828231).length < 2 ^ (prefixWord ++ tailWord_7828231).sum := by decide
  have hdescent : baseEnd_7828231 < baseStart_7828231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828234 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_7828234 : Nat := 118140960795 + 7828234 * 2 ^ 59
def prefixEnd_7828234 : Nat := 4983230072969 + 3 ^ 40 * 7828234 * 2
def baseEnd_7828234 : Nat := 4019646717868630232173613

theorem tailTrace_7828234 : CollatzResearch.WordTrace tailWord_7828234 prefixEnd_7828234 4019646717868630232173613 := by
  unfold tailWord_7828234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71379787580413162192952939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190346100214435099181207837 71379787580413162192952939)
  ·
    refine ⟨107069681370619743289429409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71379787580413162192952939 107069681370619743289429409)
    ·
      refine ⟨80302261027964807467072057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107069681370619743289429409 80302261027964807467072057)
      ·
        refine ⟨60226695770973605600304043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80302261027964807467072057 60226695770973605600304043)
        ·
          refine ⟨90340043656460408400456065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60226695770973605600304043 90340043656460408400456065)
          ·
            refine ⟨67755032742345306300342049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90340043656460408400456065 67755032742345306300342049)
            ·
              refine ⟨50816274556758979725256537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67755032742345306300342049 50816274556758979725256537)
              ·
                refine ⟨38112205917569234793942403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50816274556758979725256537 38112205917569234793942403)
                ·
                  refine ⟨57168308876353852190913605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38112205917569234793942403 57168308876353852190913605)
                  ·
                    refine ⟨10719057914316347285796301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57168308876353852190913605 10719057914316347285796301)
                    ·
                      refine ⟨4019646717868630232173613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719057914316347285796301 4019646717868630232173613)
                      ·
                        rfl

theorem cell23_7828234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_7828234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828234 prefixEnd_7828234 := by exact prefixLift 7828234
  have htrace : WordTrace (prefixWord ++ tailWord_7828234) baseStart_7828234 baseEnd_7828234 := by
    simpa [prefixWord, tailWord_7828234, baseEnd_7828234] using wordTrace_append hprefix tailTrace_7828234
  have hstable : (prefixWord ++ tailWord_7828234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828234).length < 2 ^ (prefixWord ++ tailWord_7828234).sum := by decide
  have hdescent : baseEnd_7828234 < baseStart_7828234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828258 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_7828258 : Nat := 118140960795 + 7828258 * 2 ^ 59
def prefixEnd_7828258 : Nat := 4983230072969 + 3 ^ 40 * 7828258 * 2
def baseEnd_7828258 : Nat := 1339886347134779379424501

theorem tailTrace_7828258 : CollatzResearch.WordTrace tailWord_7828258 prefixEnd_7828258 1339886347134779379424501 := by
  unfold tailWord_7828258
  simp only [CollatzResearch.WordTrace]
  refine ⟨71380006418391425217671357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190346683782377133913790285 71380006418391425217671357)
  ·
    refine ⟨26767502406896784456626759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71380006418391425217671357 26767502406896784456626759)
    ·
      refine ⟨40151253610345176684940139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26767502406896784456626759 40151253610345176684940139)
      ·
        refine ⟨60226880415517765027410209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40151253610345176684940139 60226880415517765027410209)
        ·
          refine ⟨45170160311638323770557657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60226880415517765027410209 45170160311638323770557657)
          ·
            refine ⟨33877620233728742827918243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45170160311638323770557657 33877620233728742827918243)
            ·
              refine ⟨50816430350593114241877365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33877620233728742827918243 50816430350593114241877365)
              ·
                refine ⟨4764040345368104460176003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50816430350593114241877365 4764040345368104460176003)
                ·
                  refine ⟨7146060518052156690264005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764040345368104460176003 7146060518052156690264005)
                  ·
                    refine ⟨1339886347134779379424501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146060518052156690264005 1339886347134779379424501)
                    ·
                      rfl

theorem cell23_7828258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_7828258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828258 prefixEnd_7828258 := by exact prefixLift 7828258
  have htrace : WordTrace (prefixWord ++ tailWord_7828258) baseStart_7828258 baseEnd_7828258 := by
    simpa [prefixWord, tailWord_7828258, baseEnd_7828258] using wordTrace_append hprefix tailTrace_7828258
  have hstable : (prefixWord ++ tailWord_7828258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828258).length < 2 ^ (prefixWord ++ tailWord_7828258).sum := by decide
  have hdescent : baseEnd_7828258 < baseStart_7828258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828304 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_7828304 : Nat := 118140960795 + 7828304 * 2 ^ 59
def prefixEnd_7828304 : Nat := 4983230072969 + 3 ^ 40 * 7828304 * 2
def baseEnd_7828304 : Nat := 4019682661514444958298291

theorem tailTrace_7828304 : CollatzResearch.WordTrace tailWord_7828304 prefixEnd_7828304 4019682661514444958298291 := by
  unfold tailWord_7828304
  simp only [CollatzResearch.WordTrace]
  refine ⟨142760851715699525363429983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190347802287599367151239977 142760851715699525363429983)
  ·
    refine ⟨214141277573549288045144975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142760851715699525363429983 214141277573549288045144975)
    ·
      refine ⟨321211916360323932067717463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214141277573549288045144975 321211916360323932067717463)
      ·
        refine ⟨481817874540485898101576195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321211916360323932067717463 481817874540485898101576195)
        ·
          refine ⟨722726811810728847152364293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481817874540485898101576195 722726811810728847152364293)
          ·
            refine ⟨135511277214511658841068305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 722726811810728847152364293 135511277214511658841068305)
            ·
              refine ⟨101633457910883744130801229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135511277214511658841068305 101633457910883744130801229)
              ·
                refine ⟨38112546716581404049050461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101633457910883744130801229 38112546716581404049050461)
                ·
                  refine ⟨14292205018718026518393923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38112546716581404049050461 14292205018718026518393923)
                  ·
                    refine ⟨21438307528077039777590885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14292205018718026518393923 21438307528077039777590885)
                    ·
                      refine ⟨4019682661514444958298291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21438307528077039777590885 4019682661514444958298291)
                      ·
                        rfl

theorem cell23_7828304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_7828304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828304 prefixEnd_7828304 := by exact prefixLift 7828304
  have htrace : WordTrace (prefixWord ++ tailWord_7828304) baseStart_7828304 baseEnd_7828304 := by
    simpa [prefixWord, tailWord_7828304, baseEnd_7828304] using wordTrace_append hprefix tailTrace_7828304
  have hstable : (prefixWord ++ tailWord_7828304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828304).length < 2 ^ (prefixWord ++ tailWord_7828304).sum := by decide
  have hdescent : baseEnd_7828304 < baseStart_7828304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828341 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7828341 : Nat := 118140960795 + 7828341 * 2 ^ 59
def prefixEnd_7828341 : Nat := 4983230072969 + 3 ^ 40 * 7828341 * 2
def baseEnd_7828341 : Nat := 4019701660298661313535621

theorem tailTrace_7828341 : CollatzResearch.WordTrace tailWord_7828341 prefixEnd_7828341 4019701660298661313535621 := by
  unfold tailWord_7828341
  simp only [CollatzResearch.WordTrace]
  refine ⟨285523052932265006045956877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190348701954843337363971251 285523052932265006045956877)
  ·
    refine ⟨107071144849599377267233829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285523052932265006045956877 107071144849599377267233829)
    ·
      refine ⟨20075839659299883237606343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107071144849599377267233829 20075839659299883237606343)
      ·
        refine ⟨30113759488949824856409515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075839659299883237606343 30113759488949824856409515)
        ·
          refine ⟨45170639233424737284614273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113759488949824856409515 45170639233424737284614273)
          ·
            refine ⟨33877979425068552963460705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45170639233424737284614273 33877979425068552963460705)
            ·
              refine ⟨25408484568801414722595529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33877979425068552963460705 25408484568801414722595529)
              ·
                refine ⟨19056363426601061041946647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25408484568801414722595529 19056363426601061041946647)
                ·
                  refine ⟨28584545139901591562919971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19056363426601061041946647 28584545139901591562919971)
                  ·
                    refine ⟨42876817709852387344379957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28584545139901591562919971 42876817709852387344379957)
                    ·
                      refine ⟨4019701660298661313535621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42876817709852387344379957 4019701660298661313535621)
                      ·
                        rfl

theorem cell23_7828341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7828341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828341 prefixEnd_7828341 := by exact prefixLift 7828341
  have htrace : WordTrace (prefixWord ++ tailWord_7828341) baseStart_7828341 baseEnd_7828341 := by
    simpa [prefixWord, tailWord_7828341, baseEnd_7828341] using wordTrace_append hprefix tailTrace_7828341
  have hstable : (prefixWord ++ tailWord_7828341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828341).length < 2 ^ (prefixWord ++ tailWord_7828341).sum := by decide
  have hdescent : baseEnd_7828341 < baseStart_7828341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828371 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 3]
def baseStart_7828371 : Nat := 118140960795 + 7828371 * 2 ^ 59
def prefixEnd_7828371 : Nat := 4983230072969 + 3 ^ 40 * 7828371 * 2
def baseEnd_7828371 : Nat := 4019717064718296196160483

theorem tailTrace_7828371 : CollatzResearch.WordTrace tailWord_7828371 prefixEnd_7828371 4019717064718296196160483 := by
  unfold tailWord_7828371
  simp only [CollatzResearch.WordTrace]
  refine ⟨285524147122156321169548967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190349431414770880779699311 285524147122156321169548967)
  ·
    refine ⟨428286220683234481754323451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285524147122156321169548967 428286220683234481754323451)
    ·
      refine ⟨642429331024851722631485177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428286220683234481754323451 642429331024851722631485177)
      ·
        refine ⟨481821998268638791973613883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642429331024851722631485177 481821998268638791973613883)
        ·
          refine ⟨722732997402958187960420825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481821998268638791973613883 722732997402958187960420825)
          ·
            refine ⟨542049748052218640970315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722732997402958187960420825 542049748052218640970315619)
            ·
              refine ⟨813074622078327961455473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542049748052218640970315619 813074622078327961455473429)
              ·
                refine ⟨38112872909921623193225317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 813074622078327961455473429 38112872909921623193225317)
                ·
                  refine ⟨7146163670610304348729747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38112872909921623193225317 7146163670610304348729747)
                  ·
                    refine ⟨10719245505915456523094621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146163670610304348729747 10719245505915456523094621)
                    ·
                      refine ⟨4019717064718296196160483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719245505915456523094621 4019717064718296196160483)
                      ·
                        rfl

theorem cell23_7828371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_7828371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828371 prefixEnd_7828371 := by exact prefixLift 7828371
  have htrace : WordTrace (prefixWord ++ tailWord_7828371) baseStart_7828371 baseEnd_7828371 := by
    simpa [prefixWord, tailWord_7828371, baseEnd_7828371] using wordTrace_append hprefix tailTrace_7828371
  have hstable : (prefixWord ++ tailWord_7828371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828371).length < 2 ^ (prefixWord ++ tailWord_7828371).sum := by decide
  have hdescent : baseEnd_7828371 < baseStart_7828371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828372 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7828372 : Nat := 118140960795 + 7828372 * 2 ^ 59
def prefixEnd_7828372 : Nat := 4983230072969 + 3 ^ 40 * 7828372 * 2
def baseEnd_7828372 : Nat := 4019717578198950692247979

theorem tailTrace_7828372 : CollatzResearch.WordTrace tailWord_7828372 prefixEnd_7828372 4019717578198950692247979 := by
  unfold tailWord_7828372
  simp only [CollatzResearch.WordTrace]
  refine ⟨142762091797576349170167685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190349455730101798893556913 142762091797576349170167685)
  ·
    refine ⟨26767892212045565469406441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142762091797576349170167685 26767892212045565469406441)
    ·
      refine ⟨20075919159034174102054831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26767892212045565469406441 20075919159034174102054831)
      ·
        refine ⟨30113878738551261153082247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075919159034174102054831 30113878738551261153082247)
        ·
          refine ⟨45170818107826891729623371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113878738551261153082247 45170818107826891729623371)
          ·
            refine ⟨67756227161740337594435057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45170818107826891729623371 67756227161740337594435057)
            ·
              refine ⟨50817170371305253195826293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67756227161740337594435057 50817170371305253195826293)
              ·
                refine ⟨4764109722309867487108715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50817170371305253195826293 4764109722309867487108715)
                ·
                  refine ⟨7146164583464801230663073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764109722309867487108715 7146164583464801230663073)
                  ·
                    refine ⟨5359623437598600922997305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146164583464801230663073 5359623437598600922997305)
                    ·
                      refine ⟨4019717578198950692247979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359623437598600922997305 4019717578198950692247979)
                      ·
                        rfl

theorem cell23_7828372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7828372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828372 prefixEnd_7828372 := by exact prefixLift 7828372
  have htrace : WordTrace (prefixWord ++ tailWord_7828372) baseStart_7828372 baseEnd_7828372 := by
    simpa [prefixWord, tailWord_7828372, baseEnd_7828372] using wordTrace_append hprefix tailTrace_7828372
  have hstable : (prefixWord ++ tailWord_7828372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828372).length < 2 ^ (prefixWord ++ tailWord_7828372).sum := by decide
  have hdescent : baseEnd_7828372 < baseStart_7828372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828384 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7828384 : Nat := 118140960795 + 7828384 * 2 ^ 59
def prefixEnd_7828384 : Nat := 4983230072969 + 3 ^ 40 * 7828384 * 2
def baseEnd_7828384 : Nat := 4019723739966804645297923

theorem tailTrace_7828384 : CollatzResearch.WordTrace tailWord_7828384 prefixEnd_7828384 4019723739966804645297923 := by
  unfold tailWord_7828384
  simp only [CollatzResearch.WordTrace]
  refine ⟨142762310635554612194886103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190349747514072816259848137 142762310635554612194886103)
  ·
    refine ⟨214143465953331918292329155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142762310635554612194886103 214143465953331918292329155)
    ·
      refine ⟨321215198929997877438493733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214143465953331918292329155 321215198929997877438493733)
      ·
        refine ⟨60227849799374602019717575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321215198929997877438493733 60227849799374602019717575)
        ·
          refine ⟨90341774699061903029576363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60227849799374602019717575 90341774699061903029576363)
          ·
            refine ⟨135512662048592854544364545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90341774699061903029576363 135512662048592854544364545)
            ·
              refine ⟨101634496536444640908273409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135512662048592854544364545 101634496536444640908273409)
              ·
                refine ⟨76225872402333480681205057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101634496536444640908273409 76225872402333480681205057)
                ·
                  refine ⟨57169404301750110510903793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76225872402333480681205057 57169404301750110510903793)
                  ·
                    refine ⟨42877053226312582883177845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57169404301750110510903793 42877053226312582883177845)
                    ·
                      refine ⟨4019723739966804645297923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42877053226312582883177845 4019723739966804645297923)
                      ·
                        rfl

theorem cell23_7828384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7828384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828384 prefixEnd_7828384 := by exact prefixLift 7828384
  have htrace : WordTrace (prefixWord ++ tailWord_7828384) baseStart_7828384 baseEnd_7828384 := by
    simpa [prefixWord, tailWord_7828384, baseEnd_7828384] using wordTrace_append hprefix tailTrace_7828384
  have hstable : (prefixWord ++ tailWord_7828384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828384).length < 2 ^ (prefixWord ++ tailWord_7828384).sum := by decide
  have hdescent : baseEnd_7828384 < baseStart_7828384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828406 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7828406 : Nat := 118140960795 + 7828406 * 2 ^ 59
def prefixEnd_7828406 : Nat := 4983230072969 + 3 ^ 40 * 7828406 * 2
def baseEnd_7828406 : Nat := 4019735036541203559222823

theorem tailTrace_7828406 : CollatzResearch.WordTrace tailWord_7828406 prefixEnd_7828406 4019735036541203559222823 := by
  unfold tailWord_7828406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845338979814345134192067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190350282451353014764715381 17845338979814345134192067)
  ·
    refine ⟨26768008469721517701288101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17845338979814345134192067 26768008469721517701288101)
    ·
      refine ⟨5019001588072784568991519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26768008469721517701288101 5019001588072784568991519)
      ·
        refine ⟨7528502382109176853487279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019001588072784568991519 7528502382109176853487279)
        ·
          refine ⟨11292753573163765280230919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528502382109176853487279 11292753573163765280230919)
          ·
            refine ⟨16939130359745647920346379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292753573163765280230919 16939130359745647920346379)
            ·
              refine ⟨25408695539618471880519569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16939130359745647920346379 25408695539618471880519569)
              ·
                refine ⟨19056521654713853910389677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25408695539618471880519569 19056521654713853910389677)
                ·
                  refine ⟨7146195620517695216396129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19056521654713853910389677 7146195620517695216396129)
                  ·
                    refine ⟨5359646715388271412297097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146195620517695216396129 5359646715388271412297097)
                    ·
                      refine ⟨4019735036541203559222823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359646715388271412297097 4019735036541203559222823)
                      ·
                        rfl

theorem cell23_7828406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7828406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828406 prefixEnd_7828406 := by exact prefixLift 7828406
  have htrace : WordTrace (prefixWord ++ tailWord_7828406) baseStart_7828406 baseEnd_7828406 := by
    simpa [prefixWord, tailWord_7828406, baseEnd_7828406] using wordTrace_append hprefix tailTrace_7828406
  have hstable : (prefixWord ++ tailWord_7828406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828406).length < 2 ^ (prefixWord ++ tailWord_7828406).sum := by decide
  have hdescent : baseEnd_7828406 < baseStart_7828406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828428 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7828428 : Nat := 118140960795 + 7828428 * 2 ^ 59
def prefixEnd_7828428 : Nat := 4983230072969 + 3 ^ 40 * 7828428 * 2
def baseEnd_7828428 : Nat := 4019746333115602473147721

theorem tailTrace_7828428 : CollatzResearch.WordTrace tailWord_7828428 prefixEnd_7828428 4019746333115602473147721 := by
  unfold tailWord_7828428
  simp only [CollatzResearch.WordTrace]
  refine ⟨142763113041474909952186969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190350817388633213269582625 142763113041474909952186969)
  ·
    refine ⟨107072334781106182464140227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142763113041474909952186969 107072334781106182464140227)
    ·
      refine ⟨160608502171659273696210341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107072334781106182464140227 160608502171659273696210341)
      ·
        refine ⟨30114094157186113818039439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160608502171659273696210341 30114094157186113818039439)
        ·
          refine ⟨45171141235779170727059159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30114094157186113818039439 45171141235779170727059159)
          ·
            refine ⟨67756711853668756090588739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45171141235779170727059159 67756711853668756090588739)
            ·
              refine ⟨101635067780503134135883109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67756711853668756090588739 101635067780503134135883109)
              ·
                refine ⟨19056575208844337650478083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101635067780503134135883109 19056575208844337650478083)
                ·
                  refine ⟨28584862813266506475717125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19056575208844337650478083 28584862813266506475717125)
                  ·
                    refine ⟨5359661777487469964196961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28584862813266506475717125 5359661777487469964196961)
                    ·
                      refine ⟨4019746333115602473147721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359661777487469964196961 4019746333115602473147721)
                      ·
                        rfl

theorem cell23_7828428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7828428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828428 prefixEnd_7828428 := by exact prefixLift 7828428
  have htrace : WordTrace (prefixWord ++ tailWord_7828428) baseStart_7828428 baseEnd_7828428 := by
    simpa [prefixWord, tailWord_7828428, baseEnd_7828428] using wordTrace_append hprefix tailTrace_7828428
  have hstable : (prefixWord ++ tailWord_7828428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828428).length < 2 ^ (prefixWord ++ tailWord_7828428).sum := by decide
  have hdescent : baseEnd_7828428 < baseStart_7828428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828438 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7828438 : Nat := 118140960795 + 7828438 * 2 ^ 59
def prefixEnd_7828438 : Nat := 4983230072969 + 3 ^ 40 * 7828438 * 2
def baseEnd_7828438 : Nat := 1339917155974049144674225

theorem tailTrace_7828438 : CollatzResearch.WordTrace tailWord_7828438 prefixEnd_7828438 1339917155974049144674225 := by
  unfold tailWord_7828438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845411925807099475764873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190351060541942394408158645 17845411925807099475764873)
  ·
    refine ⟨13384058944355324606823655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17845411925807099475764873 13384058944355324606823655)
    ·
      refine ⟨20076088416532986910235483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384058944355324606823655 20076088416532986910235483)
      ·
        refine ⟨30114132624799480365353225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076088416532986910235483 30114132624799480365353225)
        ·
          refine ⟨22585599468599610274014919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30114132624799480365353225 22585599468599610274014919)
          ·
            refine ⟨33878399202899415411022379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22585599468599610274014919 33878399202899415411022379)
            ·
              refine ⟨50817598804349123116533569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33878399202899415411022379 50817598804349123116533569)
              ·
                refine ⟨38113199103261842337400177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50817598804349123116533569 38113199103261842337400177)
                ·
                  refine ⟨28584899327446381753050133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38113199103261842337400177 28584899327446381753050133)
                  ·
                    refine ⟨1339917155974049144674225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28584899327446381753050133 1339917155974049144674225)
                    ·
                      rfl

theorem cell23_7828438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7828438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828438 prefixEnd_7828438 := by exact prefixLift 7828438
  have htrace : WordTrace (prefixWord ++ tailWord_7828438) baseStart_7828438 baseEnd_7828438 := by
    simpa [prefixWord, tailWord_7828438, baseEnd_7828438] using wordTrace_append hprefix tailTrace_7828438
  have hstable : (prefixWord ++ tailWord_7828438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828438).length < 2 ^ (prefixWord ++ tailWord_7828438).sum := by decide
  have hdescent : baseEnd_7828438 < baseStart_7828438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828441 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_7828441 : Nat := 118140960795 + 7828441 * 2 ^ 59
def prefixEnd_7828441 : Nat := 4983230072969 + 3 ^ 40 * 7828441 * 2
def baseEnd_7828441 : Nat := 4019753008364110922285161

theorem tailTrace_7828441 : CollatzResearch.WordTrace tailWord_7828441 prefixEnd_7828441 4019753008364110922285161 := by
  unfold tailWord_7828441
  simp only [CollatzResearch.WordTrace]
  refine ⟨285526700231902723124597177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190351133487935148749731451 285526700231902723124597177)
  ·
    refine ⟨214145025173927042343447883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285526700231902723124597177 214145025173927042343447883)
    ·
      refine ⟨321217537760890563515171825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214145025173927042343447883 321217537760890563515171825)
      ·
        refine ⟨240913153320667922636378869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321217537760890563515171825 240913153320667922636378869)
        ·
          refine ⟨22585608123812617747160519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240913153320667922636378869 22585608123812617747160519)
          ·
            refine ⟨33878412185718926620740779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22585608123812617747160519 33878412185718926620740779)
            ·
              refine ⟨50817618278578389931111169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33878412185718926620740779 50817618278578389931111169)
              ·
                refine ⟨38113213708933792448333377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50817618278578389931111169 38113213708933792448333377)
                ·
                  refine ⟨28584910281700344336250033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38113213708933792448333377 28584910281700344336250033)
                  ·
                    refine ⟨21438682711275258252187525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28584910281700344336250033 21438682711275258252187525)
                    ·
                      refine ⟨4019753008364110922285161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21438682711275258252187525 4019753008364110922285161)
                      ·
                        rfl

theorem cell23_7828441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_7828441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828441 prefixEnd_7828441 := by exact prefixLift 7828441
  have htrace : WordTrace (prefixWord ++ tailWord_7828441) baseStart_7828441 baseEnd_7828441 := by
    simpa [prefixWord, tailWord_7828441, baseEnd_7828441] using wordTrace_append hprefix tailTrace_7828441
  have hstable : (prefixWord ++ tailWord_7828441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828441).length < 2 ^ (prefixWord ++ tailWord_7828441).sum := by decide
  have hdescent : baseEnd_7828441 < baseStart_7828441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828451 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 7]
def baseStart_7828451 : Nat := 118140960795 + 7828451 * 2 ^ 59
def prefixEnd_7828451 : Nat := 4983230072969 + 3 ^ 40 * 7828451 * 2
def baseEnd_7828451 : Nat := 446639793685628431462235

theorem tailTrace_7828451 : CollatzResearch.WordTrace tailWord_7828451 prefixEnd_7828451 446639793685628431462235 := by
  unfold tailWord_7828451
  simp only [CollatzResearch.WordTrace]
  refine ⟨285527064961866494832461207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190351376641244329888307471 285527064961866494832461207)
  ·
    refine ⟨428290597442799742248691811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285527064961866494832461207 428290597442799742248691811)
    ·
      refine ⟨642435896164199613373037717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428290597442799742248691811 642435896164199613373037717)
      ·
        refine ⟨30114182632696856876861143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 642435896164199613373037717 30114182632696856876861143)
        ·
          refine ⟨45171273949045285315291715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30114182632696856876861143 45171273949045285315291715)
          ·
            refine ⟨67756910923567927972937573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45171273949045285315291715 67756910923567927972937573)
            ·
              refine ⟨12704420798168986494925795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67756910923567927972937573 12704420798168986494925795)
              ·
                refine ⟨19056631197253479742388693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704420798168986494925795 19056631197253479742388693)
                ·
                  refine ⟨446639793685628431462235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19056631197253479742388693 446639793685628431462235)
                  ·
                    rfl

theorem cell23_7828451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 7].length) (baseStart_7828451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828451 prefixEnd_7828451 := by exact prefixLift 7828451
  have htrace : WordTrace (prefixWord ++ tailWord_7828451) baseStart_7828451 baseEnd_7828451 := by
    simpa [prefixWord, tailWord_7828451, baseEnd_7828451] using wordTrace_append hprefix tailTrace_7828451
  have hstable : (prefixWord ++ tailWord_7828451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828451).length < 2 ^ (prefixWord ++ tailWord_7828451).sum := by decide
  have hdescent : baseEnd_7828451 < baseStart_7828451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828462 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_7828462 : Nat := 118140960795 + 7828462 * 2 ^ 59
def prefixEnd_7828462 : Nat := 4983230072969 + 3 ^ 40 * 7828462 * 2
def baseEnd_7828462 : Nat := 4019763791457855340122565

theorem tailTrace_7828462 : CollatzResearch.WordTrace tailWord_7828462 prefixEnd_7828462 4019763791457855340122565 := by
  unfold tailWord_7828462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690933270603330463888955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190351644109884429140741093 35690933270603330463888955)
  ·
    refine ⟨53536399905904995695833433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35690933270603330463888955 53536399905904995695833433)
    ·
      refine ⟨40152299929428746771875075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53536399905904995695833433 40152299929428746771875075)
      ·
        refine ⟨60228449894143120157812613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152299929428746771875075 60228449894143120157812613)
        ·
          refine ⟨11292834355151835029589865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60228449894143120157812613 11292834355151835029589865)
          ·
            refine ⟨8469625766363876272192399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11292834355151835029589865 8469625766363876272192399)
            ·
              refine ⟨12704438649545814408288599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469625766363876272192399 12704438649545814408288599)
              ·
                refine ⟨19056657974318721612432899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704438649545814408288599 19056657974318721612432899)
                ·
                  refine ⟨28584986961478082418649349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19056657974318721612432899 28584986961478082418649349)
                  ·
                    refine ⟨5359685055277140453496753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28584986961478082418649349 5359685055277140453496753)
                    ·
                      refine ⟨4019763791457855340122565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359685055277140453496753 4019763791457855340122565)
                      ·
                        rfl

theorem cell23_7828462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_7828462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828462 prefixEnd_7828462 := by exact prefixLift 7828462
  have htrace : WordTrace (prefixWord ++ tailWord_7828462) baseStart_7828462 baseEnd_7828462 := by
    simpa [prefixWord, tailWord_7828462, baseEnd_7828462] using wordTrace_append hprefix tailTrace_7828462
  have hstable : (prefixWord ++ tailWord_7828462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828462).length < 2 ^ (prefixWord ++ tailWord_7828462).sum := by decide
  have hdescent : baseEnd_7828462 < baseStart_7828462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828481 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7828481 : Nat := 118140960795 + 7828481 * 2 ^ 59
def prefixEnd_7828481 : Nat := 4983230072969 + 3 ^ 40 * 7828481 * 2
def baseEnd_7828481 : Nat := 1339924515863430255261659

theorem tailTrace_7828481 : CollatzResearch.WordTrace tailWord_7828481 prefixEnd_7828481 1339924515863430255261659 := by
  unfold tailWord_7828481
  simp only [CollatzResearch.WordTrace]
  refine ⟨285528159151757809956053297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190352106101171873304035531 285528159151757809956053297)
  ·
    refine ⟨214146119363818357467039973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285528159151757809956053297 214146119363818357467039973)
    ·
      refine ⟨40152397380715942025069995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214146119363818357467039973 40152397380715942025069995)
      ·
        refine ⟨60228596071073913037604993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152397380715942025069995 60228596071073913037604993)
        ·
          refine ⟨45171447053305434778203745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60228596071073913037604993 45171447053305434778203745)
          ·
            refine ⟨33878585289979076083652809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45171447053305434778203745 33878585289979076083652809)
            ·
              refine ⟨25408938967484307062739607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33878585289979076083652809 25408938967484307062739607)
              ·
                refine ⟨38113408451226460594109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25408938967484307062739607 38113408451226460594109411)
                ·
                  refine ⟨57170112676839690891164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38113408451226460594109411 57170112676839690891164117)
                  ·
                    refine ⟨1339924515863430255261659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57170112676839690891164117 1339924515863430255261659)
                    ·
                      rfl

theorem cell23_7828481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7828481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828481 prefixEnd_7828481 := by exact prefixLift 7828481
  have htrace : WordTrace (prefixWord ++ tailWord_7828481) baseStart_7828481 baseEnd_7828481 := by
    simpa [prefixWord, tailWord_7828481, baseEnd_7828481] using wordTrace_append hprefix tailTrace_7828481
  have hstable : (prefixWord ++ tailWord_7828481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828481).length < 2 ^ (prefixWord ++ tailWord_7828481).sum := by decide
  have hdescent : baseEnd_7828481 < baseStart_7828481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828508 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7828508 : Nat := 118140960795 + 7828508 * 2 ^ 59
def prefixEnd_7828508 : Nat := 4983230072969 + 3 ^ 40 * 7828508 * 2
def baseEnd_7828508 : Nat := 4019787411567962160147353

theorem tailTrace_7828508 : CollatzResearch.WordTrace tailWord_7828508 prefixEnd_7828508 4019787411567962160147353 := by
  unfold tailWord_7828508
  simp only [CollatzResearch.WordTrace]
  refine ⟨142764571961329996783643089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190352762615106662378190785 142764571961329996783643089)
  ·
    refine ⟨107073428970997497587732317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142764571961329996783643089 107073428970997497587732317)
    ·
      refine ⟨40152535864124061595399619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107073428970997497587732317 40152535864124061595399619)
      ·
        refine ⟨60228803796186092393099429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152535864124061595399619 60228803796186092393099429)
        ·
          refine ⟨11292900711784892323706143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60228803796186092393099429 11292900711784892323706143)
          ·
            refine ⟨16939351067677338485559215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292900711784892323706143 16939351067677338485559215)
            ·
              refine ⟨25409026601516007728338823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16939351067677338485559215 25409026601516007728338823)
              ·
                refine ⟨38113539902274011592508235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25409026601516007728338823 38113539902274011592508235)
                ·
                  refine ⟨57170309853411017388762353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38113539902274011592508235 57170309853411017388762353)
                  ·
                    refine ⟨42877732390058263041571765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57170309853411017388762353 42877732390058263041571765)
                    ·
                      refine ⟨4019787411567962160147353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42877732390058263041571765 4019787411567962160147353)
                      ·
                        rfl

theorem cell23_7828508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7828508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828508 prefixEnd_7828508 := by exact prefixLift 7828508
  have htrace : WordTrace (prefixWord ++ tailWord_7828508) baseStart_7828508 baseEnd_7828508 := by
    simpa [prefixWord, tailWord_7828508, baseEnd_7828508] using wordTrace_append hprefix tailTrace_7828508
  have hstable : (prefixWord ++ tailWord_7828508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828508).length < 2 ^ (prefixWord ++ tailWord_7828508).sum := by decide
  have hdescent : baseEnd_7828508 < baseStart_7828508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828538 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_7828538 : Nat := 118140960795 + 7828538 * 2 ^ 59
def prefixEnd_7828538 : Nat := 4983230072969 + 3 ^ 40 * 7828538 * 2
def baseEnd_7828538 : Nat := 4019802815987597042772215

theorem tailTrace_7828538 : CollatzResearch.WordTrace tailWord_7828538 prefixEnd_7828538 4019802815987597042772215 := by
  unfold tailWord_7828538
  simp only [CollatzResearch.WordTrace]
  refine ⟨71382559528137827172719567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190353492075034205793918845 71382559528137827172719567)
  ·
    refine ⟨107073839292206740759079351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71382559528137827172719567 107073839292206740759079351)
    ·
      refine ⟨160610758938310111138619027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107073839292206740759079351 160610758938310111138619027)
      ·
        refine ⟨240916138407465166707928541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160610758938310111138619027 240916138407465166707928541)
        ·
          refine ⟨90343551902799437515473203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240916138407465166707928541 90343551902799437515473203)
          ·
            refine ⟨135515327854199156273209805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90343551902799437515473203 135515327854199156273209805)
            ·
              refine ⟨50818247945324683602453677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135515327854199156273209805 50818247945324683602453677)
              ·
                refine ⟨19056842979496756350920129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50818247945324683602453677 19056842979496756350920129)
                ·
                  refine ⟨14292632234622567263190097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19056842979496756350920129 14292632234622567263190097)
                  ·
                    refine ⟨10719474175966925447392573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14292632234622567263190097 10719474175966925447392573)
                    ·
                      refine ⟨4019802815987597042772215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719474175966925447392573 4019802815987597042772215)
                      ·
                        rfl

theorem cell23_7828538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_7828538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828538 prefixEnd_7828538 := by exact prefixLift 7828538
  have htrace : WordTrace (prefixWord ++ tailWord_7828538) baseStart_7828538 baseEnd_7828538 := by
    simpa [prefixWord, tailWord_7828538, baseEnd_7828538] using wordTrace_append hprefix tailTrace_7828538
  have hstable : (prefixWord ++ tailWord_7828538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828538).length < 2 ^ (prefixWord ++ tailWord_7828538).sum := by decide
  have hdescent : baseEnd_7828538 < baseStart_7828538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828558 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_7828558 : Nat := 118140960795 + 7828558 * 2 ^ 59
def prefixEnd_7828558 : Nat := 4983230072969 + 3 ^ 40 * 7828558 * 2
def baseEnd_7828558 : Nat := 446645898400076329391347

theorem tailTrace_7828558 : CollatzResearch.WordTrace tailWord_7828558 prefixEnd_7828558 446645898400076329391347 := by
  unfold tailWord_7828558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691370946559856513325791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190353978381652568071070885 35691370946559856513325791)
  ·
    refine ⟨53537056419839784769988687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35691370946559856513325791 53537056419839784769988687)
    ·
      refine ⟨80305584629759677154983031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53537056419839784769988687 80305584629759677154983031)
      ·
        refine ⟨120458376944639515732474547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80305584629759677154983031 120458376944639515732474547)
        ·
          refine ⟨180687565416959273598711821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120458376944639515732474547 180687565416959273598711821)
          ·
            refine ⟨67757837031359727599516933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180687565416959273598711821 67757837031359727599516933)
            ·
              refine ⟨12704594443379948924909425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67757837031359727599516933 12704594443379948924909425)
              ·
                refine ⟨9528445832534961693682069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12704594443379948924909425 9528445832534961693682069)
                ·
                  refine ⟨446645898400076329391347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9528445832534961693682069 446645898400076329391347)
                  ·
                    rfl

theorem cell23_7828558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_7828558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828558 prefixEnd_7828558 := by exact prefixLift 7828558
  have htrace : WordTrace (prefixWord ++ tailWord_7828558) baseStart_7828558 baseEnd_7828558 := by
    simpa [prefixWord, tailWord_7828558, baseEnd_7828558] using wordTrace_append hprefix tailTrace_7828558
  have hstable : (prefixWord ++ tailWord_7828558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828558).length < 2 ^ (prefixWord ++ tailWord_7828558).sum := by decide
  have hdescent : baseEnd_7828558 < baseStart_7828558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828562 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_7828562 : Nat := 118140960795 + 7828562 * 2 ^ 59
def prefixEnd_7828562 : Nat := 4983230072969 + 3 ^ 40 * 7828562 * 2
def baseEnd_7828562 : Nat := 1339938379841101649624035

theorem tailTrace_7828562 : CollatzResearch.WordTrace tailWord_7828562 prefixEnd_7828562 1339938379841101649624035 := by
  unfold tailWord_7828562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71382778366116090197437985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190354075642976240526501293 71382778366116090197437985)
  ·
    refine ⟨53537083774587067648078489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71382778366116090197437985 53537083774587067648078489)
    ·
      refine ⟨40152812830940300736058867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53537083774587067648078489 40152812830940300736058867)
      ·
        refine ⟨60229219246410451104088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152812830940300736058867 60229219246410451104088301)
        ·
          refine ⟨22585957217403919164033113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60229219246410451104088301 22585957217403919164033113)
          ·
            refine ⟨16939467913052939373024835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22585957217403919164033113 16939467913052939373024835)
            ·
              refine ⟨25409201869579409059537253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16939467913052939373024835 25409201869579409059537253)
              ·
                refine ⟨4764225350546139198663235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25409201869579409059537253 4764225350546139198663235)
                ·
                  refine ⟨7146338025819208797994853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764225350546139198663235 7146338025819208797994853)
                  ·
                    refine ⟨1339938379841101649624035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146338025819208797994853 1339938379841101649624035)
                    ·
                      rfl

theorem cell23_7828562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_7828562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828562 prefixEnd_7828562 := by exact prefixLift 7828562
  have htrace : WordTrace (prefixWord ++ tailWord_7828562) baseStart_7828562 baseEnd_7828562 := by
    simpa [prefixWord, tailWord_7828562, baseEnd_7828562] using wordTrace_append hprefix tailTrace_7828562
  have hstable : (prefixWord ++ tailWord_7828562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828562).length < 2 ^ (prefixWord ++ tailWord_7828562).sum := by decide
  have hdescent : baseEnd_7828562 < baseStart_7828562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828581 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7828581 : Nat := 118140960795 + 7828581 * 2 ^ 59
def prefixEnd_7828581 : Nat := 4983230072969 + 3 ^ 40 * 7828581 * 2
def baseEnd_7828581 : Nat := 4019824895655740374534517

theorem tailTrace_7828581 : CollatzResearch.WordTrace tailWord_7828581 prefixEnd_7828581 4019824895655740374534517 := by
  unfold tailWord_7828581
  simp only [CollatzResearch.WordTrace]
  refine ⟨285531806451395527034693597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190354537634263684689795731 285531806451395527034693597)
  ·
    refine ⟨107074427419273322638010099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285531806451395527034693597 107074427419273322638010099)
    ·
      refine ⟨160611641128909983957015149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107074427419273322638010099 160611641128909983957015149)
      ·
        refine ⟨60229365423341243983880681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160611641128909983957015149 60229365423341243983880681)
        ·
          refine ⟨45172024067505932987910511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60229365423341243983880681 45172024067505932987910511)
          ·
            refine ⟨67758036101258899481865767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45172024067505932987910511 67758036101258899481865767)
            ·
              refine ⟨101637054151888349222798651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67758036101258899481865767 101637054151888349222798651)
              ·
                refine ⟨152455581227832523834197977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101637054151888349222798651 152455581227832523834197977)
                ·
                  refine ⟨114341685920874392875648483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152455581227832523834197977 114341685920874392875648483)
                  ·
                    refine ⟨171512528881311589313472725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114341685920874392875648483 171512528881311589313472725)
                    ·
                      refine ⟨4019824895655740374534517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171512528881311589313472725 4019824895655740374534517)
                      ·
                        rfl

theorem cell23_7828581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7828581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828581 prefixEnd_7828581 := by exact prefixLift 7828581
  have htrace : WordTrace (prefixWord ++ tailWord_7828581) baseStart_7828581 baseEnd_7828581 := by
    simpa [prefixWord, tailWord_7828581, baseEnd_7828581] using wordTrace_append hprefix tailTrace_7828581
  have hstable : (prefixWord ++ tailWord_7828581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828581).length < 2 ^ (prefixWord ++ tailWord_7828581).sum := by decide
  have hdescent : baseEnd_7828581 < baseStart_7828581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828585 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_7828585 : Nat := 118140960795 + 7828585 * 2 ^ 59
def prefixEnd_7828585 : Nat := 4983230072969 + 3 ^ 40 * 7828585 * 2
def baseEnd_7828585 : Nat := 4019826949578358358884499

theorem tailTrace_7828585 : CollatzResearch.WordTrace tailWord_7828585 prefixEnd_7828585 4019826949578358358884499 := by
  unfold tailWord_7828585
  simp only [CollatzResearch.WordTrace]
  refine ⟨285531952343381035717839209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190354634895587357145226139 285531952343381035717839209)
  ·
    refine ⟨214148964257535776788379407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285531952343381035717839209 214148964257535776788379407)
    ·
      refine ⟨321223446386303665182569111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214148964257535776788379407 321223446386303665182569111)
      ·
        refine ⟨481835169579455497773853667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321223446386303665182569111 481835169579455497773853667)
        ·
          refine ⟨722752754369183246660780501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481835169579455497773853667 722752754369183246660780501)
          ·
            refine ⟨16939517680527732343612043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 722752754369183246660780501 16939517680527732343612043)
            ·
              refine ⟨25409276520791598515418065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16939517680527732343612043 25409276520791598515418065)
              ·
                refine ⟨19056957390593698886563549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25409276520791598515418065 19056957390593698886563549)
                ·
                  refine ⟨7146359021472637082461331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19056957390593698886563549 7146359021472637082461331)
                  ·
                    refine ⟨10719538532208955623691997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146359021472637082461331 10719538532208955623691997)
                    ·
                      refine ⟨4019826949578358358884499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719538532208955623691997 4019826949578358358884499)
                      ·
                        rfl

theorem cell23_7828585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_7828585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828585 prefixEnd_7828585 := by exact prefixLift 7828585
  have htrace : WordTrace (prefixWord ++ tailWord_7828585) baseStart_7828585 baseEnd_7828585 := by
    simpa [prefixWord, tailWord_7828585, baseEnd_7828585] using wordTrace_append hprefix tailTrace_7828585
  have hstable : (prefixWord ++ tailWord_7828585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828585).length < 2 ^ (prefixWord ++ tailWord_7828585).sum := by decide
  have hdescent : baseEnd_7828585 < baseStart_7828585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828588 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_7828588 : Nat := 118140960795 + 7828588 * 2 ^ 59
def prefixEnd_7828588 : Nat := 4983230072969 + 3 ^ 40 * 7828588 * 2
def baseEnd_7828588 : Nat := 1339942830006773949048995

theorem tailTrace_7828588 : CollatzResearch.WordTrace tailWord_7828588 prefixEnd_7828588 1339942830006773949048995 := by
  unfold tailWord_7828588
  simp only [CollatzResearch.WordTrace]
  refine ⟨142766030881185083615099209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190354707841580111486798945 142766030881185083615099209)
  ·
    refine ⟨107074523160888812711324407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142766030881185083615099209 107074523160888812711324407)
    ·
      refine ⟨160611784741333219066986611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107074523160888812711324407 160611784741333219066986611)
      ·
        refine ⟨240917677111999828600479917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160611784741333219066986611 240917677111999828600479917)
        ·
          refine ⟨90344128916999935725179969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240917677111999828600479917 90344128916999935725179969)
          ·
            refine ⟨67758096687749951793884977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90344128916999935725179969 67758096687749951793884977)
            ·
              refine ⟨50818572515812463845413733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67758096687749951793884977 50818572515812463845413733)
              ·
                refine ⟨9528482346714836971015075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50818572515812463845413733 9528482346714836971015075)
                ·
                  refine ⟨14292723520072255456522613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9528482346714836971015075 14292723520072255456522613)
                  ·
                    refine ⟨1339942830006773949048995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14292723520072255456522613 1339942830006773949048995)
                    ·
                      rfl

theorem cell23_7828588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_7828588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828588 prefixEnd_7828588 := by exact prefixLift 7828588
  have htrace : WordTrace (prefixWord ++ tailWord_7828588) baseStart_7828588 baseEnd_7828588 := by
    simpa [prefixWord, tailWord_7828588, baseEnd_7828588] using wordTrace_append hprefix tailTrace_7828588
  have hstable : (prefixWord ++ tailWord_7828588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828588).length < 2 ^ (prefixWord ++ tailWord_7828588).sum := by decide
  have hdescent : baseEnd_7828588 < baseStart_7828588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828645 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_7828645 : Nat := 118140960795 + 7828645 * 2 ^ 59
def prefixEnd_7828645 : Nat := 4983230072969 + 3 ^ 40 * 7828645 * 2
def baseEnd_7828645 : Nat := 4019857758417628124134223

theorem tailTrace_7828645 : CollatzResearch.WordTrace tailWord_7828645 prefixEnd_7828645 4019857758417628124134223 := by
  unfold tailWord_7828645
  simp only [CollatzResearch.WordTrace]
  refine ⟨285534140723163665965023389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190356093815442443976682259 285534140723163665965023389)
  ·
    refine ⟨107075302771186374736883771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285534140723163665965023389 107075302771186374736883771)
    ·
      refine ⟨160612954156779562105325657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107075302771186374736883771 160612954156779562105325657)
      ·
        refine ⟨120459715617584671578994243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160612954156779562105325657 120459715617584671578994243)
        ·
          refine ⟨180689573426377007368491365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120459715617584671578994243 180689573426377007368491365)
          ·
            refine ⟨33879295017445688881592131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180689573426377007368491365 33879295017445688881592131)
            ·
              refine ⟨50818942526168533322388197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33879295017445688881592131 50818942526168533322388197)
              ·
                refine ⟨9528551723656599997947787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50818942526168533322388197 9528551723656599997947787)
                ·
                  refine ⟨14292827585484899996921681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9528551723656599997947787 14292827585484899996921681)
                  ·
                    refine ⟨10719620689113674997691261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14292827585484899996921681 10719620689113674997691261)
                    ·
                      refine ⟨4019857758417628124134223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719620689113674997691261 4019857758417628124134223)
                      ·
                        rfl

theorem cell23_7828645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_7828645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828645 prefixEnd_7828645 := by exact prefixLift 7828645
  have htrace : WordTrace (prefixWord ++ tailWord_7828645) baseStart_7828645 baseEnd_7828645 := by
    simpa [prefixWord, tailWord_7828645, baseEnd_7828645] using wordTrace_append hprefix tailTrace_7828645
  have hstable : (prefixWord ++ tailWord_7828645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828645).length < 2 ^ (prefixWord ++ tailWord_7828645).sum := by decide
  have hdescent : baseEnd_7828645 < baseStart_7828645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828653 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_7828653 : Nat := 118140960795 + 7828653 * 2 ^ 59
def prefixEnd_7828653 : Nat := 4983230072969 + 3 ^ 40 * 7828653 * 2
def baseEnd_7828653 : Nat := 4019861866262864092834187

theorem tailTrace_7828653 : CollatzResearch.WordTrace tailWord_7828653 prefixEnd_7828653 4019861866262864092834187 := by
  unfold tailWord_7828653
  simp only [CollatzResearch.WordTrace]
  refine ⟨285534432507134683331314613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190356288338089788887543075 285534432507134683331314613)
  ·
    refine ⟨26768853047543876562310745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285534432507134683331314613 26768853047543876562310745)
    ·
      refine ⟨20076639785657907421733059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26768853047543876562310745 20076639785657907421733059)
      ·
        refine ⟨30114959678486861132599589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076639785657907421733059 30114959678486861132599589)
        ·
          refine ⟨5646554939716286462362423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30114959678486861132599589 5646554939716286462362423)
          ·
            refine ⟨8469832409574429693543635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646554939716286462362423 8469832409574429693543635)
            ·
              refine ⟨12704748614361644540315453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469832409574429693543635 12704748614361644540315453)
              ·
                refine ⟨4764280730385616702618295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12704748614361644540315453 4764280730385616702618295)
                ·
                  refine ⟨7146421095578425053927443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764280730385616702618295 7146421095578425053927443)
                  ·
                    refine ⟨10719631643367637580891165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7146421095578425053927443 10719631643367637580891165)
                    ·
                      refine ⟨4019861866262864092834187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719631643367637580891165 4019861866262864092834187)
                      ·
                        rfl

theorem cell23_7828653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_7828653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828653 prefixEnd_7828653 := by exact prefixLift 7828653
  have htrace : WordTrace (prefixWord ++ tailWord_7828653) baseStart_7828653 baseEnd_7828653 := by
    simpa [prefixWord, tailWord_7828653, baseEnd_7828653] using wordTrace_append hprefix tailTrace_7828653
  have hstable : (prefixWord ++ tailWord_7828653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828653).length < 2 ^ (prefixWord ++ tailWord_7828653).sum := by decide
  have hdescent : baseEnd_7828653 < baseStart_7828653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828659 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 1, 2, 2]
def baseStart_7828659 : Nat := 118140960795 + 7828659 * 2 ^ 59
def prefixEnd_7828659 : Nat := 4983230072969 + 3 ^ 40 * 7828659 * 2
def baseEnd_7828659 : Nat := 4019864947146791069359159

theorem tailTrace_7828659 : CollatzResearch.WordTrace tailWord_7828659 prefixEnd_7828659 4019864947146791069359159 := by
  unfold tailWord_7828659
  simp only [CollatzResearch.WordTrace]
  refine ⟨285534651345112946356033031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190356434230075297570688687 285534651345112946356033031)
  ·
    refine ⟨428301977017669419534049547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285534651345112946356033031 428301977017669419534049547)
    ·
      refine ⟨642452965526504129301074321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428301977017669419534049547 642452965526504129301074321)
      ·
        refine ⟨481839724144878096975805741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642452965526504129301074321 481839724144878096975805741)
        ·
          refine ⟨180689896554329286365927153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481839724144878096975805741 180689896554329286365927153)
          ·
            refine ⟨135517422415746964774445365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180689896554329286365927153 135517422415746964774445365)
            ·
              refine ⟨12704758351476277947604253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135517422415746964774445365 12704758351476277947604253)
              ·
                refine ⟨4764284381803604230351595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12704758351476277947604253 4764284381803604230351595)
                ·
                  refine ⟨7146426572705406345527393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764284381803604230351595 7146426572705406345527393)
                  ·
                    refine ⟨5359819929529054759145545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146426572705406345527393 5359819929529054759145545)
                    ·
                      refine ⟨4019864947146791069359159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359819929529054759145545 4019864947146791069359159)
                      ·
                        rfl

theorem cell23_7828659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 2, 2].length) (baseStart_7828659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828659 prefixEnd_7828659 := by exact prefixLift 7828659
  have htrace : WordTrace (prefixWord ++ tailWord_7828659) baseStart_7828659 baseEnd_7828659 := by
    simpa [prefixWord, tailWord_7828659, baseEnd_7828659] using wordTrace_append hprefix tailTrace_7828659
  have hstable : (prefixWord ++ tailWord_7828659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828659).length < 2 ^ (prefixWord ++ tailWord_7828659).sum := by decide
  have hdescent : baseEnd_7828659 < baseStart_7828659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828676 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7828676 : Nat := 118140960795 + 7828676 * 2 ^ 59
def prefixEnd_7828676 : Nat := 4983230072969 + 3 ^ 40 * 7828676 * 2
def baseEnd_7828676 : Nat := 4019873676317917502846581

theorem tailTrace_7828676 : CollatzResearch.WordTrace tailWord_7828676 prefixEnd_7828676 4019873676317917502846581 := by
  unfold tailWord_7828676
  simp only [CollatzResearch.WordTrace]
  refine ⟨142767635693025679129700941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190356847590700905506267921 142767635693025679129700941)
  ·
    refine ⟨53537863384884629673637853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142767635693025679129700941 53537863384884629673637853)
    ·
      refine ⟨20076698769331736127614195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53537863384884629673637853 20076698769331736127614195)
      ·
        refine ⟨30115048153997604191421293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076698769331736127614195 30115048153997604191421293)
        ·
          refine ⟨11293143057749101571782985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30115048153997604191421293 11293143057749101571782985)
          ·
            refine ⟨8469857293311826178837239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11293143057749101571782985 8469857293311826178837239)
            ·
              refine ⟨12704785939967739268255859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469857293311826178837239 12704785939967739268255859)
              ·
                refine ⟨19057178909951608902383789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704785939967739268255859 19057178909951608902383789)
                ·
                  refine ⟨7146442091231853338393921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19057178909951608902383789 7146442091231853338393921)
                  ·
                    refine ⟨5359831568423890003795441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146442091231853338393921 5359831568423890003795441)
                    ·
                      refine ⟨4019873676317917502846581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359831568423890003795441 4019873676317917502846581)
                      ·
                        rfl

theorem cell23_7828676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7828676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828676 prefixEnd_7828676 := by exact prefixLift 7828676
  have htrace : WordTrace (prefixWord ++ tailWord_7828676) baseStart_7828676 baseEnd_7828676 := by
    simpa [prefixWord, tailWord_7828676, baseEnd_7828676] using wordTrace_append hprefix tailTrace_7828676
  have hstable : (prefixWord ++ tailWord_7828676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828676).length < 2 ^ (prefixWord ++ tailWord_7828676).sum := by decide
  have hdescent : baseEnd_7828676 < baseStart_7828676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_7828681 : Nat := 118140960795 + 7828681 * 2 ^ 59
def prefixEnd_7828681 : Nat := 4983230072969 + 3 ^ 40 * 7828681 * 2
def baseEnd_7828681 : Nat := 4019876243721189983284057

theorem tailTrace_7828681 : CollatzResearch.WordTrace tailWord_7828681 prefixEnd_7828681 4019876243721189983284057 := by
  unfold tailWord_7828681
  simp only [CollatzResearch.WordTrace]
  refine ⟨285535453751033244113333897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190356969167355496075555931 285535453751033244113333897)
  ·
    refine ⟨214151590313274933085000423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285535453751033244113333897 214151590313274933085000423)
    ·
      refine ⟨321227385469912399627500635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214151590313274933085000423 321227385469912399627500635)
      ·
        refine ⟨481841078204868599441250953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321227385469912399627500635 481841078204868599441250953)
        ·
          refine ⟨361380808653651449580938215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481841078204868599441250953 361380808653651449580938215)
          ·
            refine ⟨542071212980477174371407323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361380808653651449580938215 542071212980477174371407323)
            ·
              refine ⟨813106819470715761557110985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542071212980477174371407323 813106819470715761557110985)
              ·
                refine ⟨609830114603036821167833239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813106819470715761557110985 609830114603036821167833239)
                ·
                  refine ⟨914745171904555231751749859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609830114603036821167833239 914745171904555231751749859)
                  ·
                    refine ⟨1372117757856832847627624789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914745171904555231751749859 1372117757856832847627624789)
                    ·
                      refine ⟨4019876243721189983284057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1372117757856832847627624789 4019876243721189983284057)
                      ·
                        rfl

theorem cell23_7828681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_7828681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828681 prefixEnd_7828681 := by exact prefixLift 7828681
  have htrace : WordTrace (prefixWord ++ tailWord_7828681) baseStart_7828681 baseEnd_7828681 := by
    simpa [prefixWord, tailWord_7828681, baseEnd_7828681] using wordTrace_append hprefix tailTrace_7828681
  have hstable : (prefixWord ++ tailWord_7828681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828681).length < 2 ^ (prefixWord ++ tailWord_7828681).sum := by decide
  have hdescent : baseEnd_7828681 < baseStart_7828681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828686 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_7828686 : Nat := 118140960795 + 7828686 * 2 ^ 59
def prefixEnd_7828686 : Nat := 4983230072969 + 3 ^ 40 * 7828686 * 2
def baseEnd_7828686 : Nat := 1339959603708154154573845

theorem tailTrace_7828686 : CollatzResearch.WordTrace tailWord_7828686 prefixEnd_7828686 1339959603708154154573845 := by
  unfold tailWord_7828686
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691954514501891245908239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190357090744010086644843941 35691954514501891245908239)
  ·
    refine ⟨53537931771752836868862359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35691954514501891245908239 53537931771752836868862359)
    ·
      refine ⟨80306897657629255303293539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53537931771752836868862359 80306897657629255303293539)
      ·
        refine ⟨120460346486443882954940309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80306897657629255303293539 120460346486443882954940309)
        ·
          refine ⟨5646578741552057013512827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120460346486443882954940309 5646578741552057013512827)
          ·
            refine ⟨8469868112328085520269241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646578741552057013512827 8469868112328085520269241)
            ·
              refine ⟨6352401084246064140201931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8469868112328085520269241 6352401084246064140201931)
              ·
                refine ⟨9528601626369096210302897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352401084246064140201931 9528601626369096210302897)
                ·
                  refine ⟨7146451219776822157727173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9528601626369096210302897 7146451219776822157727173)
                  ·
                    refine ⟨1339959603708154154573845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146451219776822157727173 1339959603708154154573845)
                    ·
                      rfl

theorem cell23_7828686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_7828686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828686 prefixEnd_7828686 := by exact prefixLift 7828686
  have htrace : WordTrace (prefixWord ++ tailWord_7828686) baseStart_7828686 baseEnd_7828686 := by
    simpa [prefixWord, tailWord_7828686, baseEnd_7828686] using wordTrace_append hprefix tailTrace_7828686
  have hstable : (prefixWord ++ tailWord_7828686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828686).length < 2 ^ (prefixWord ++ tailWord_7828686).sum := by decide
  have hdescent : baseEnd_7828686 < baseStart_7828686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828715 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 4, 2]
def baseStart_7828715 : Nat := 118140960795 + 7828715 * 2 ^ 59
def prefixEnd_7828715 : Nat := 4983230072969 + 3 ^ 40 * 7828715 * 2
def baseEnd_7828715 : Nat := 4019893702063442850258901

theorem tailTrace_7828715 : CollatzResearch.WordTrace tailWord_7828715 prefixEnd_7828715 4019893702063442850258901 := by
  unfold tailWord_7828715
  simp only [CollatzResearch.WordTrace]
  refine ⟨285536693832910067920071599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190357795888606711946714399 285536693832910067920071599)
  ·
    refine ⟨428305040749365101880107399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285536693832910067920071599 428305040749365101880107399)
    ·
      refine ⟨642457561124047652820161099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428305040749365101880107399 642457561124047652820161099)
      ·
        refine ⟨963686341686071479230241649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642457561124047652820161099 963686341686071479230241649)
        ·
          refine ⟨722764756264553609422681237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963686341686071479230241649 722764756264553609422681237)
          ·
            refine ⟨33879597949900950441688183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 722764756264553609422681237 33879597949900950441688183)
            ·
              refine ⟨50819396924851425662532275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33879597949900950441688183 50819396924851425662532275)
              ·
                refine ⟨76229095387277138493798413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50819396924851425662532275 76229095387277138493798413)
                ·
                  refine ⟨28585910770228926935174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76229095387277138493798413 28585910770228926935174405)
                  ·
                    refine ⟨5359858269417923800345201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28585910770228926935174405 5359858269417923800345201)
                    ·
                      refine ⟨4019893702063442850258901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5359858269417923800345201 4019893702063442850258901)
                      ·
                        rfl

theorem cell23_7828715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4, 2].length) (baseStart_7828715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828715 prefixEnd_7828715 := by exact prefixLift 7828715
  have htrace : WordTrace (prefixWord ++ tailWord_7828715) baseStart_7828715 baseEnd_7828715 := by
    simpa [prefixWord, tailWord_7828715, baseEnd_7828715] using wordTrace_append hprefix tailTrace_7828715
  have hstable : (prefixWord ++ tailWord_7828715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828715).length < 2 ^ (prefixWord ++ tailWord_7828715).sum := by decide
  have hdescent : baseEnd_7828715 < baseStart_7828715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828772 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 5]
def baseStart_7828772 : Nat := 118140960795 + 7828772 * 2 ^ 59
def prefixEnd_7828772 : Nat := 4983230072969 + 3 ^ 40 * 7828772 * 2
def baseEnd_7828772 : Nat := 446658107828972125249571

theorem tailTrace_7828772 : CollatzResearch.WordTrace tailWord_7828772 prefixEnd_7828772 446658107828972125249571 := by
  unfold tailWord_7828772
  simp only [CollatzResearch.WordTrace]
  refine ⟨142769386396851783327448285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190359181862469044436597713 142769386396851783327448285)
  ·
    refine ⟨53538519898819418747793107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142769386396851783327448285 53538519898819418747793107)
    ·
      refine ⟨80307779848229128121689661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53538519898819418747793107 80307779848229128121689661)
      ·
        refine ⟨30115417443085923045633623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80307779848229128121689661 30115417443085923045633623)
        ·
          refine ⟨45173126164628884568450435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30115417443085923045633623 45173126164628884568450435)
          ·
            refine ⟨67759689246943326852675653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45173126164628884568450435 67759689246943326852675653)
            ·
              refine ⟨12704941733801873784876685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67759689246943326852675653 12704941733801873784876685)
              ·
                refine ⟨4764353150175702669328757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12704941733801873784876685 4764353150175702669328757)
                ·
                  refine ⟨446658107828972125249571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4764353150175702669328757 446658107828972125249571)
                  ·
                    rfl

theorem cell23_7828772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_7828772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828772 prefixEnd_7828772 := by exact prefixLift 7828772
  have htrace : WordTrace (prefixWord ++ tailWord_7828772) baseStart_7828772 baseEnd_7828772 := by
    simpa [prefixWord, tailWord_7828772, baseEnd_7828772] using wordTrace_append hprefix tailTrace_7828772
  have hstable : (prefixWord ++ tailWord_7828772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828772).length < 2 ^ (prefixWord ++ tailWord_7828772).sum := by decide
  have hdescent : baseEnd_7828772 < baseStart_7828772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828825 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_7828825 : Nat := 118140960795 + 7828825 * 2 ^ 59
def prefixEnd_7828825 : Nat := 4983230072969 + 3 ^ 40 * 7828825 * 2
def baseEnd_7828825 : Nat := 4019950184935437419883395

theorem tailTrace_7828825 : CollatzResearch.WordTrace tailWord_7828825 prefixEnd_7828825 4019950184935437419883395 := by
  unfold tailWord_7828825
  simp only [CollatzResearch.WordTrace]
  refine ⟨285540705862511556706575929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190360470575007704471050619 285540705862511556706575929)
  ·
    refine ⟨214155529396883667529931947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285540705862511556706575929 214155529396883667529931947)
    ·
      refine ⟨321233294095325501294897921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214155529396883667529931947 321233294095325501294897921)
      ·
        refine ⟨240924970571494125971173441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321233294095325501294897921 240924970571494125971173441)
        ·
          refine ⟨180693727928620594478380081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240924970571494125971173441 180693727928620594478380081)
          ·
            refine ⟨135520295946465445858785061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180693727928620594478380081 135520295946465445858785061)
            ·
              refine ⟨25410055489962271098522199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135520295946465445858785061 25410055489962271098522199)
              ·
                refine ⟨38115083234943406647783299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25410055489962271098522199 38115083234943406647783299)
                ·
                  refine ⟨57172624852415109971674949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38115083234943406647783299 57172624852415109971674949)
                  ·
                    refine ⟨10719867159827833119689053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57172624852415109971674949 10719867159827833119689053)
                    ·
                      refine ⟨4019950184935437419883395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10719867159827833119689053 4019950184935437419883395)
                      ·
                        rfl

theorem cell23_7828825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_7828825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828825 prefixEnd_7828825 := by exact prefixLift 7828825
  have htrace : WordTrace (prefixWord ++ tailWord_7828825) baseStart_7828825 baseEnd_7828825 := by
    simpa [prefixWord, tailWord_7828825, baseEnd_7828825] using wordTrace_append hprefix tailTrace_7828825
  have hstable : (prefixWord ++ tailWord_7828825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828825).length < 2 ^ (prefixWord ++ tailWord_7828825).sum := by decide
  have hdescent : baseEnd_7828825 < baseStart_7828825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828845 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7828845 : Nat := 118140960795 + 7828845 * 2 ^ 59
def prefixEnd_7828845 : Nat := 4983230072969 + 3 ^ 40 * 7828845 * 2
def baseEnd_7828845 : Nat := 446662272727614149070367

theorem tailTrace_7828845 : CollatzResearch.WordTrace tailWord_7828845 prefixEnd_7828845 446662272727614149070367 := by
  unfold tailWord_7828845
  simp only [CollatzResearch.WordTrace]
  refine ⟨285541435322439100122303989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190360956881626066748202659 285541435322439100122303989)
  ·
    refine ⟨26769509561478665636465999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285541435322439100122303989 26769509561478665636465999)
    ·
      refine ⟨40154264342217998454698999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26769509561478665636465999 40154264342217998454698999)
      ·
        refine ⟨60231396513326997682048499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40154264342217998454698999 60231396513326997682048499)
        ·
          refine ⟨90347094769990496523072749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60231396513326997682048499 90347094769990496523072749)
          ·
            refine ⟨33880160538746436196152281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90347094769990496523072749 33880160538746436196152281)
            ·
              refine ⟨25410120404059827147114211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33880160538746436196152281 25410120404059827147114211)
              ·
                refine ⟨38115180606089740720671317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25410120404059827147114211 38115180606089740720671317)
                ·
                  refine ⟨446662272727614149070367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38115180606089740720671317 446662272727614149070367)
                  ·
                    rfl

theorem cell23_7828845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7828845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828845 prefixEnd_7828845 := by exact prefixLift 7828845
  have htrace : WordTrace (prefixWord ++ tailWord_7828845) baseStart_7828845 baseEnd_7828845 := by
    simpa [prefixWord, tailWord_7828845, baseEnd_7828845] using wordTrace_append hprefix tailTrace_7828845
  have hstable : (prefixWord ++ tailWord_7828845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828845).length < 2 ^ (prefixWord ++ tailWord_7828845).sum := by decide
  have hdescent : baseEnd_7828845 < baseStart_7828845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828875 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 3, 5]
def baseStart_7828875 : Nat := 118140960795 + 7828875 * 2 ^ 59
def prefixEnd_7828875 : Nat := 4983230072969 + 3 ^ 40 * 7828875 * 2
def baseEnd_7828875 : Nat := 1339991952989387408086055

theorem tailTrace_7828875 : CollatzResearch.WordTrace tailWord_7828875 prefixEnd_7828875 1339991952989387408086055 := by
  unfold tailWord_7828875
  simp only [CollatzResearch.WordTrace]
  refine ⟨285542529512330415245896079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190361686341553610163930719 285542529512330415245896079)
  ·
    refine ⟨428313794268495622868844119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285542529512330415245896079 428313794268495622868844119)
    ·
      refine ⟨642470691402743434303266179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428313794268495622868844119 642470691402743434303266179)
      ·
        refine ⟨963706037104115151454899269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642470691402743434303266179 963706037104115151454899269)
        ·
          refine ⟨180694881957021590897793613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 963706037104115151454899269 180694881957021590897793613)
          ·
            refine ⟨67760580733883096586672605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180694881957021590897793613 67760580733883096586672605)
            ·
              refine ⟨25410217775206161220002227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67760580733883096586672605 25410217775206161220002227)
              ·
                refine ⟨38115326662809241830003341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25410217775206161220002227 38115326662809241830003341)
                ·
                  refine ⟨14293247498553465686251253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38115326662809241830003341 14293247498553465686251253)
                  ·
                    refine ⟨1339991952989387408086055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14293247498553465686251253 1339991952989387408086055)
                    ·
                      rfl

theorem cell23_7828875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].length) (baseStart_7828875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828875 prefixEnd_7828875 := by exact prefixLift 7828875
  have htrace : WordTrace (prefixWord ++ tailWord_7828875) baseStart_7828875 baseEnd_7828875 := by
    simpa [prefixWord, tailWord_7828875, baseEnd_7828875] using wordTrace_append hprefix tailTrace_7828875
  have hstable : (prefixWord ++ tailWord_7828875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828875).length < 2 ^ (prefixWord ++ tailWord_7828875).sum := by decide
  have hdescent : baseEnd_7828875 < baseStart_7828875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_7828915 : Nat := 118140960795 + 7828915 * 2 ^ 59
def prefixEnd_7828915 : Nat := 4983230072969 + 3 ^ 40 * 7828915 * 2
def baseEnd_7828915 : Nat := 4019996398194342067757981

theorem tailTrace_7828915 : CollatzResearch.WordTrace tailWord_7828915 prefixEnd_7828915 4019996398194342067757981 := by
  unfold tailWord_7828915
  simp only [CollatzResearch.WordTrace]
  refine ⟨285543988432185502077352199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190362658954790334718234799 285543988432185502077352199)
  ·
    refine ⟨428315982648278253116028299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285543988432185502077352199 428315982648278253116028299)
    ·
      refine ⟨642473973972417379674042449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428315982648278253116028299 642473973972417379674042449)
      ·
        refine ⟨481855480479313034755531837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642473973972417379674042449 481855480479313034755531837)
        ·
          refine ⟨180695805179742388033324439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481855480479313034755531837 180695805179742388033324439)
          ·
            refine ⟨271043707769613582049986659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180695805179742388033324439 271043707769613582049986659)
            ·
              refine ⟨406565561654420373074979989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271043707769613582049986659 406565561654420373074979989)
              ·
                refine ⟨19057760702550954987889687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406565561654420373074979989 19057760702550954987889687)
                ·
                  refine ⟨28586641053826432481834531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19057760702550954987889687 28586641053826432481834531)
                  ·
                    refine ⟨42879961580739648722751797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28586641053826432481834531 42879961580739648722751797)
                    ·
                      refine ⟨4019996398194342067757981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42879961580739648722751797 4019996398194342067757981)
                      ·
                        rfl

theorem cell23_7828915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_7828915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828915 prefixEnd_7828915 := by exact prefixLift 7828915
  have htrace : WordTrace (prefixWord ++ tailWord_7828915) baseStart_7828915 baseEnd_7828915 := by
    simpa [prefixWord, tailWord_7828915, baseEnd_7828915] using wordTrace_append hprefix tailTrace_7828915
  have hstable : (prefixWord ++ tailWord_7828915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828915).length < 2 ^ (prefixWord ++ tailWord_7828915).sum := by decide
  have hdescent : baseEnd_7828915 < baseStart_7828915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828942 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7828942 : Nat := 118140960795 + 7828942 * 2 ^ 59
def prefixEnd_7828942 : Nat := 4983230072969 + 3 ^ 40 * 7828942 * 2
def baseEnd_7828942 : Nat := 4020010262172013462120357

theorem tailTrace_7828942 : CollatzResearch.WordTrace tailWord_7828942 prefixEnd_7828942 4020010262172013462120357 := by
  unfold tailWord_7828942
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693121650385960711073135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190363315468725123792390053 35693121650385960711073135)
  ·
    refine ⟨53539682475578941066609703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35693121650385960711073135 53539682475578941066609703)
    ·
      refine ⟨80309523713368411599914555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53539682475578941066609703 80309523713368411599914555)
      ·
        refine ⟨120464285570052617399871833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80309523713368411599914555 120464285570052617399871833)
        ·
          refine ⟨90348214177539463049903875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120464285570052617399871833 90348214177539463049903875)
          ·
            refine ⟨135522321266309194574855813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90348214177539463049903875 135522321266309194574855813)
            ·
              refine ⟨25410435237432973982785465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135522321266309194574855813 25410435237432973982785465)
              ·
                refine ⟨19057826428074730487089099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25410435237432973982785465 19057826428074730487089099)
                ·
                  refine ⟨28586739642112095730633649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19057826428074730487089099 28586739642112095730633649)
                  ·
                    refine ⟨21440054731584071797975237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28586739642112095730633649 21440054731584071797975237)
                    ·
                      refine ⟨4020010262172013462120357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21440054731584071797975237 4020010262172013462120357)
                      ·
                        rfl

theorem cell23_7828942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7828942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828942 prefixEnd_7828942 := by exact prefixLift 7828942
  have htrace : WordTrace (prefixWord ++ tailWord_7828942) baseStart_7828942 baseEnd_7828942 := by
    simpa [prefixWord, tailWord_7828942, baseEnd_7828942] using wordTrace_append hprefix tailTrace_7828942
  have hstable : (prefixWord ++ tailWord_7828942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828942).length < 2 ^ (prefixWord ++ tailWord_7828942).sum := by decide
  have hdescent : baseEnd_7828942 < baseStart_7828942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828949 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7828949 : Nat := 118140960795 + 7828949 * 2 ^ 59
def prefixEnd_7828949 : Nat := 4983230072969 + 3 ^ 40 * 7828949 * 2
def baseEnd_7828949 : Nat := 4020013856536594934732825

theorem tailTrace_7828949 : CollatzResearch.WordTrace tailWord_7828949 prefixEnd_7828949 4020013856536594934732825 := by
  unfold tailWord_7828949
  simp only [CollatzResearch.WordTrace]
  refine ⟨285545228514062325884089901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190363485676041550589393267 285545228514062325884089901)
  ·
    refine ⟨107079460692773372206533713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285545228514062325884089901 107079460692773372206533713)
    ·
      refine ⟨80309595519580029154900285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107079460692773372206533713 80309595519580029154900285)
      ·
        refine ⟨30116098319842510933087607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80309595519580029154900285 30116098319842510933087607)
        ·
          refine ⟨45174147479763766399631411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30116098319842510933087607 45174147479763766399631411)
          ·
            refine ⟨67761221219645649599447117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45174147479763766399631411 67761221219645649599447117)
            ·
              refine ⟨25410457957367118599792669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67761221219645649599447117 25410457957367118599792669)
              ·
                refine ⟨9528921734012669474922251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25410457957367118599792669 9528921734012669474922251)
                ·
                  refine ⟨14293382601019004212383377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9528921734012669474922251 14293382601019004212383377)
                  ·
                    refine ⟨10720036950764253159287533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14293382601019004212383377 10720036950764253159287533)
                    ·
                      refine ⟨4020013856536594934732825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10720036950764253159287533 4020013856536594934732825)
                      ·
                        rfl

theorem cell23_7828949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7828949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828949 prefixEnd_7828949 := by exact prefixLift 7828949
  have htrace : WordTrace (prefixWord ++ tailWord_7828949) baseStart_7828949 baseEnd_7828949 := by
    simpa [prefixWord, tailWord_7828949, baseEnd_7828949] using wordTrace_append hprefix tailTrace_7828949
  have hstable : (prefixWord ++ tailWord_7828949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828949).length < 2 ^ (prefixWord ++ tailWord_7828949).sum := by decide
  have hdescent : baseEnd_7828949 < baseStart_7828949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828963 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7828963 : Nat := 118140960795 + 7828963 * 2 ^ 59
def prefixEnd_7828963 : Nat := 4983230072969 + 3 ^ 40 * 7828963 * 2
def baseEnd_7828963 : Nat := 4020021045265757879957761

theorem tailTrace_7828963 : CollatzResearch.WordTrace tailWord_7828963 prefixEnd_7828963 4020021045265757879957761 := by
  unfold tailWord_7828963
  simp only [CollatzResearch.WordTrace]
  refine ⟨285545739136011606275099543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190363826090674404183399695 285545739136011606275099543)
  ·
    refine ⟨428318608704017409412649315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285545739136011606275099543 428318608704017409412649315)
    ·
      refine ⟨642477913056026114118973973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428318608704017409412649315 642477913056026114118973973)
      ·
        refine ⟨30116152174501224099326905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 642477913056026114118973973 30116152174501224099326905)
        ·
          refine ⟨22587114130875918074495179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30116152174501224099326905 22587114130875918074495179)
          ·
            refine ⟨33880671196313877111742769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22587114130875918074495179 33880671196313877111742769)
            ·
              refine ⟨25410503397235407833807077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33880671196313877111742769 25410503397235407833807077)
              ·
                refine ⟨4764469386981638968838827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25410503397235407833807077 4764469386981638968838827)
                ·
                  refine ⟨7146704080472458453258241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764469386981638968838827 7146704080472458453258241)
                  ·
                    refine ⟨5360028060354343839943681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146704080472458453258241 5360028060354343839943681)
                    ·
                      refine ⟨4020021045265757879957761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360028060354343839943681 4020021045265757879957761)
                      ·
                        rfl

theorem cell23_7828963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7828963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828963 prefixEnd_7828963 := by exact prefixLift 7828963
  have htrace : WordTrace (prefixWord ++ tailWord_7828963) baseStart_7828963 baseEnd_7828963 := by
    simpa [prefixWord, tailWord_7828963, baseEnd_7828963] using wordTrace_append hprefix tailTrace_7828963
  have hstable : (prefixWord ++ tailWord_7828963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828963).length < 2 ^ (prefixWord ++ tailWord_7828963).sum := by decide
  have hdescent : baseEnd_7828963 < baseStart_7828963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828972 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_7828972 : Nat := 118140960795 + 7828972 * 2 ^ 59
def prefixEnd_7828972 : Nat := 4983230072969 + 3 ^ 40 * 7828972 * 2
def baseEnd_7828972 : Nat := 4020025666591648344745219

theorem tailTrace_7828972 : CollatzResearch.WordTrace tailWord_7828972 prefixEnd_7828972 4020025666591648344745219 := by
  unfold tailWord_7828972
  simp only [CollatzResearch.WordTrace]
  refine ⟨142773033696489500406088585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190364044928652667208118113 142773033696489500406088585)
  ·
    refine ⟨107079775272367125304566439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142773033696489500406088585 107079775272367125304566439)
    ·
      refine ⟨160619662908550687956849659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107079775272367125304566439 160619662908550687956849659)
      ·
        refine ⟨240929494362826031935274489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160619662908550687956849659 240929494362826031935274489)
        ·
          refine ⟨180697120772119523951455867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240929494362826031935274489 180697120772119523951455867)
          ·
            refine ⟨271045681158179285927183801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180697120772119523951455867 271045681158179285927183801)
            ·
              refine ⟨203284260868634464445387851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271045681158179285927183801 203284260868634464445387851)
              ·
                refine ⟨304926391302951696668081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203284260868634464445387851 304926391302951696668081777)
                ·
                  refine ⟨228694793477213772501061333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304926391302951696668081777 228694793477213772501061333)
                  ·
                    refine ⟨5360034222122197792993625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228694793477213772501061333 5360034222122197792993625)
                    ·
                      refine ⟨4020025666591648344745219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360034222122197792993625 4020025666591648344745219)
                      ·
                        rfl

theorem cell23_7828972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_7828972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828972 prefixEnd_7828972 := by exact prefixLift 7828972
  have htrace : WordTrace (prefixWord ++ tailWord_7828972) baseStart_7828972 baseEnd_7828972 := by
    simpa [prefixWord, tailWord_7828972, baseEnd_7828972] using wordTrace_append hprefix tailTrace_7828972
  have hstable : (prefixWord ++ tailWord_7828972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828972).length < 2 ^ (prefixWord ++ tailWord_7828972).sum := by decide
  have hdescent : baseEnd_7828972 < baseStart_7828972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828973 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_7828973 : Nat := 118140960795 + 7828973 * 2 ^ 59
def prefixEnd_7828973 : Nat := 4983230072969 + 3 ^ 40 * 7828973 * 2
def baseEnd_7828973 : Nat := 1340008726690767613610905

theorem tailTrace_7828973 : CollatzResearch.WordTrace tailWord_7828973 prefixEnd_7828973 1340008726690767613610905 := by
  unfold tailWord_7828973
  simp only [CollatzResearch.WordTrace]
  refine ⟨285546103865975377982963573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190364069243983585321975715 285546103865975377982963573)
  ·
    refine ⟨26769947237435191685902835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285546103865975377982963573 26769947237435191685902835)
    ·
      refine ⟨40154920856152787528854253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26769947237435191685902835 40154920856152787528854253)
      ·
        refine ⟨15058095321057295323320345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40154920856152787528854253 15058095321057295323320345)
        ·
          refine ⟨11293571490792971492490259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15058095321057295323320345 11293571490792971492490259)
          ·
            refine ⟨16940357236189457238735389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11293571490792971492490259 16940357236189457238735389)
            ·
              refine ⟨6352633963571046464525771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16940357236189457238735389 6352633963571046464525771)
              ·
                refine ⟨9528950945356569696788657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352633963571046464525771 9528950945356569696788657)
                ·
                  refine ⟨7146713209017427272591493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9528950945356569696788657 7146713209017427272591493)
                  ·
                    refine ⟨1340008726690767613610905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146713209017427272591493 1340008726690767613610905)
                    ·
                      rfl

theorem cell23_7828973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_7828973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828973 prefixEnd_7828973 := by exact prefixLift 7828973
  have htrace : WordTrace (prefixWord ++ tailWord_7828973) baseStart_7828973 baseEnd_7828973 := by
    simpa [prefixWord, tailWord_7828973, baseEnd_7828973] using wordTrace_append hprefix tailTrace_7828973
  have hstable : (prefixWord ++ tailWord_7828973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828973).length < 2 ^ (prefixWord ++ tailWord_7828973).sum := by decide
  have hdescent : baseEnd_7828973 < baseStart_7828973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7828995 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 6]
def baseStart_7828995 : Nat := 118140960795 + 7828995 * 2 ^ 59
def prefixEnd_7828995 : Nat := 4983230072969 + 3 ^ 40 * 7828995 * 2
def baseEnd_7828995 : Nat := 1340012492215567251585871

theorem tailTrace_7828995 : CollatzResearch.WordTrace tailWord_7828995 prefixEnd_7828995 1340012492215567251585871 := by
  unfold tailWord_7828995
  simp only [CollatzResearch.WordTrace]
  refine ⟨285546906271895675740264439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190364604181263783826842959 285546906271895675740264439)
  ·
    refine ⟨428320359407843513610396659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285546906271895675740264439 428320359407843513610396659)
    ·
      refine ⟨642480539111765270415594989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428320359407843513610396659 642480539111765270415594989)
      ·
        refine ⟨240930202166911976405848121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642480539111765270415594989 240930202166911976405848121)
        ·
          refine ⟨180697651625183982304386091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240930202166911976405848121 180697651625183982304386091)
          ·
            refine ⟨271046477437775973456579137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180697651625183982304386091 271046477437775973456579137)
            ·
              refine ⟨203284858078331980092434353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271046477437775973456579137 203284858078331980092434353)
              ·
                refine ⟨152463643558748985069325765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203284858078331980092434353 152463643558748985069325765)
                ·
                  refine ⟨28586933167265434700498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152463643558748985069325765 28586933167265434700498581)
                  ·
                    refine ⟨1340012492215567251585871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28586933167265434700498581 1340012492215567251585871)
                    ·
                      rfl

theorem cell23_7828995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_7828995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7828995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7828995 prefixEnd_7828995 := by exact prefixLift 7828995
  have htrace : WordTrace (prefixWord ++ tailWord_7828995) baseStart_7828995 baseEnd_7828995 := by
    simpa [prefixWord, tailWord_7828995, baseEnd_7828995] using wordTrace_append hprefix tailTrace_7828995
  have hstable : (prefixWord ++ tailWord_7828995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7828995).length < 2 ^ (prefixWord ++ tailWord_7828995).sum := by decide
  have hdescent : baseEnd_7828995 < baseStart_7828995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7828995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829072 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_7829072 : Nat := 118140960795 + 7829072 * 2 ^ 59
def prefixEnd_7829072 : Nat := 4983230072969 + 3 ^ 40 * 7829072 * 2
def baseEnd_7829072 : Nat := 1340025671552365984498253

theorem tailTrace_7829072 : CollatzResearch.WordTrace tailWord_7829072 prefixEnd_7829072 1340025671552365984498253 := by
  unfold tailWord_7829072
  simp only [CollatzResearch.WordTrace]
  refine ⟨142774857346308358945408735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190366476461744478593878313 142774857346308358945408735)
  ·
    refine ⟨214162286019462538418113103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142774857346308358945408735 214162286019462538418113103)
    ·
      refine ⟨321243429029193807627169655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214162286019462538418113103 321243429029193807627169655)
      ·
        refine ⟨481865143543790711440754483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321243429029193807627169655 481865143543790711440754483)
        ·
          refine ⟨722797715315686067161131725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481865143543790711440754483 722797715315686067161131725)
          ·
            refine ⟨271049143243382275185424397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722797715315686067161131725 271049143243382275185424397)
            ·
              refine ⟨101643428716268353194534149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271049143243382275185424397 101643428716268353194534149)
              ·
                refine ⟨19058142884300316223975153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101643428716268353194534149 19058142884300316223975153)
                ·
                  refine ⟨14293607163225237167981365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19058142884300316223975153 14293607163225237167981365)
                  ·
                    refine ⟨1340025671552365984498253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14293607163225237167981365 1340025671552365984498253)
                    ·
                      rfl

theorem cell23_7829072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_7829072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829072 prefixEnd_7829072 := by exact prefixLift 7829072
  have htrace : WordTrace (prefixWord ++ tailWord_7829072) baseStart_7829072 baseEnd_7829072 := by
    simpa [prefixWord, tailWord_7829072, baseEnd_7829072] using wordTrace_append hprefix tailTrace_7829072
  have hstable : (prefixWord ++ tailWord_7829072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829072).length < 2 ^ (prefixWord ++ tailWord_7829072).sum := by decide
  have hdescent : baseEnd_7829072 < baseStart_7829072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829079 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_7829079 : Nat := 118140960795 + 7829079 * 2 ^ 59
def prefixEnd_7829079 : Nat := 4983230072969 + 3 ^ 40 * 7829079 * 2
def baseEnd_7829079 : Nat := 4020080609021679426107227

theorem tailTrace_7829079 : CollatzResearch.WordTrace tailWord_7829079 prefixEnd_7829079 4020080609021679426107227 := by
  unfold tailWord_7829079
  simp only [CollatzResearch.WordTrace]
  refine ⟨285549970003591358086322291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190366646669060905390881527 285549970003591358086322291)
  ·
    refine ⟨428324955005387037129483437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285549970003591358086322291 428324955005387037129483437)
    ·
      refine ⟨160621858127020138923556289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428324955005387037129483437 160621858127020138923556289)
      ·
        refine ⟨120466393595265104192667217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160621858127020138923556289 120466393595265104192667217)
        ·
          refine ⟨90349795196448828144500413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120466393595265104192667217 90349795196448828144500413)
          ·
            refine ⟨33881173198668310554187655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90349795196448828144500413 33881173198668310554187655)
            ·
              refine ⟨50821759798002465831281483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33881173198668310554187655 50821759798002465831281483)
              ·
                refine ⟨76232639697003698746922225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50821759798002465831281483 76232639697003698746922225)
                ·
                  refine ⟨57174479772752774060191669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76232639697003698746922225 57174479772752774060191669)
                  ·
                    refine ⟨5360107478695572568142969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57174479772752774060191669 5360107478695572568142969)
                    ·
                      refine ⟨4020080609021679426107227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360107478695572568142969 4020080609021679426107227)
                      ·
                        rfl

theorem cell23_7829079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_7829079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829079 prefixEnd_7829079 := by exact prefixLift 7829079
  have htrace : WordTrace (prefixWord ++ tailWord_7829079) baseStart_7829079 baseEnd_7829079 := by
    simpa [prefixWord, tailWord_7829079, baseEnd_7829079] using wordTrace_append hprefix tailTrace_7829079
  have hstable : (prefixWord ++ tailWord_7829079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829079).length < 2 ^ (prefixWord ++ tailWord_7829079).sum := by decide
  have hdescent : baseEnd_7829079 < baseStart_7829079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829106 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_7829106 : Nat := 118140960795 + 7829106 * 2 ^ 59
def prefixEnd_7829106 : Nat := 4983230072969 + 3 ^ 40 * 7829106 * 2
def baseEnd_7829106 : Nat := 1340031490999783606823201

theorem tailTrace_7829106 : CollatzResearch.WordTrace tailWord_7829106 prefixEnd_7829106 1340031490999783606823201 := by
  unfold tailWord_7829106
  simp only [CollatzResearch.WordTrace]
  refine ⟨71387738693623385424388793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190367303182995694465036781 71387738693623385424388793)
  ·
    refine ⟨53540804020217539068291595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71387738693623385424388793 53540804020217539068291595)
    ·
      refine ⟨80311206030326308602437393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53540804020217539068291595 80311206030326308602437393)
      ·
        refine ⟨60233404522744731451828045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80311206030326308602437393 60233404522744731451828045)
        ·
          refine ⟨22587526696029274294435517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60233404522744731451828045 22587526696029274294435517)
          ·
            refine ⟨8470322511010977860413319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22587526696029274294435517 8470322511010977860413319)
            ·
              refine ⟨12705483766516466790619979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470322511010977860413319 12705483766516466790619979)
              ·
                refine ⟨19058225649774700185929969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705483766516466790619979 19058225649774700185929969)
                ·
                  refine ⟨14293669237331025139447477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19058225649774700185929969 14293669237331025139447477)
                  ·
                    refine ⟨1340031490999783606823201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14293669237331025139447477 1340031490999783606823201)
                    ·
                      rfl

theorem cell23_7829106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_7829106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829106 prefixEnd_7829106 := by exact prefixLift 7829106
  have htrace : WordTrace (prefixWord ++ tailWord_7829106) baseStart_7829106 baseEnd_7829106 := by
    simpa [prefixWord, tailWord_7829106, baseEnd_7829106] using wordTrace_append hprefix tailTrace_7829106
  have hstable : (prefixWord ++ tailWord_7829106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829106).length < 2 ^ (prefixWord ++ tailWord_7829106).sum := by decide
  have hdescent : baseEnd_7829106 < baseStart_7829106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829129 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_7829129 : Nat := 118140960795 + 7829129 * 2 ^ 59
def prefixEnd_7829129 : Nat := 4983230072969 + 3 ^ 40 * 7829129 * 2
def baseEnd_7829129 : Nat := 4020106283054404230481997

theorem tailTrace_7829129 : CollatzResearch.WordTrace tailWord_7829129 prefixEnd_7829129 4020106283054404230481997 := by
  unfold tailWord_7829129
  simp only [CollatzResearch.WordTrace]
  refine ⟨285551793653410216625642441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190367862435606811083761627 285551793653410216625642441)
  ·
    refine ⟨214163845240057662469231831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285551793653410216625642441 214163845240057662469231831)
    ·
      refine ⟨321245767860086493703847747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214163845240057662469231831 321245767860086493703847747)
      ·
        refine ⟨481868651790129740555771621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321245767860086493703847747 481868651790129740555771621)
        ·
          refine ⟨90350372210649326354207179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481868651790129740555771621 90350372210649326354207179)
          ·
            refine ⟨135525558315973989531310769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90350372210649326354207179 135525558315973989531310769)
            ·
              refine ⟨101644168736980492148483077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135525558315973989531310769 101644168736980492148483077)
              ·
                refine ⟨19058281638183842277840577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101644168736980492148483077 19058281638183842277840577)
                ·
                  refine ⟨14293711228637881708380433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19058281638183842277840577 14293711228637881708380433)
                  ·
                    refine ⟨10720283421478411281285325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14293711228637881708380433 10720283421478411281285325)
                    ·
                      refine ⟨4020106283054404230481997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10720283421478411281285325 4020106283054404230481997)
                      ·
                        rfl

theorem cell23_7829129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_7829129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829129 prefixEnd_7829129 := by exact prefixLift 7829129
  have htrace : WordTrace (prefixWord ++ tailWord_7829129) baseStart_7829129 baseEnd_7829129 := by
    simpa [prefixWord, tailWord_7829129, baseEnd_7829129] using wordTrace_append hprefix tailTrace_7829129
  have hstable : (prefixWord ++ tailWord_7829129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829129).length < 2 ^ (prefixWord ++ tailWord_7829129).sum := by decide
  have hdescent : baseEnd_7829129 < baseStart_7829129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829132 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 8]
def baseStart_7829132 : Nat := 118140960795 + 7829132 * 2 ^ 59
def prefixEnd_7829132 : Nat := 4983230072969 + 3 ^ 40 * 7829132 * 2
def baseEnd_7829132 : Nat := 446678647055151968749387

theorem tailTrace_7829132 : CollatzResearch.WordTrace tailWord_7829132 prefixEnd_7829132 446678647055151968749387 := by
  unfold tailWord_7829132
  simp only [CollatzResearch.WordTrace]
  refine ⟨142775951536199674069000825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190367935381599565425334433 142775951536199674069000825)
  ·
    refine ⟨107081963652149755551750619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142775951536199674069000825 107081963652149755551750619)
    ·
      refine ⟨160622945478224633327625929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107081963652149755551750619 160622945478224633327625929)
      ·
        refine ⟨120467209108668474995719447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160622945478224633327625929 120467209108668474995719447)
        ·
          refine ⟨180700813663002712493579171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120467209108668474995719447 180700813663002712493579171)
          ·
            refine ⟨271051220494504068740368757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180700813663002712493579171 271051220494504068740368757)
            ·
              refine ⟨25411051921359756444409571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271051220494504068740368757 25411051921359756444409571)
              ·
                refine ⟨38116577882039634666614357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25411051921359756444409571 38116577882039634666614357)
                ·
                  refine ⟨446678647055151968749387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38116577882039634666614357 446678647055151968749387)
                  ·
                    rfl

theorem cell23_7829132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_7829132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829132 prefixEnd_7829132 := by exact prefixLift 7829132
  have htrace : WordTrace (prefixWord ++ tailWord_7829132) baseStart_7829132 baseEnd_7829132 := by
    simpa [prefixWord, tailWord_7829132, baseEnd_7829132] using wordTrace_append hprefix tailTrace_7829132
  have hstable : (prefixWord ++ tailWord_7829132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829132).length < 2 ^ (prefixWord ++ tailWord_7829132).sum := by decide
  have hdescent : baseEnd_7829132 < baseStart_7829132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829213 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7829213 : Nat := 118140960795 + 7829213 * 2 ^ 59
def prefixEnd_7829213 : Nat := 4983230072969 + 3 ^ 40 * 7829213 * 2
def baseEnd_7829213 : Nat := 1340049805143127300610537

theorem tailTrace_7829213 : CollatzResearch.WordTrace tailWord_7829213 prefixEnd_7829213 1340049805143127300610537 := by
  unfold tailWord_7829213
  simp only [CollatzResearch.WordTrace]
  refine ⟨285554857385105898971700293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190369904923403932647800195 285554857385105898971700293)
  ·
    refine ⟨53541535759707356057193805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285554857385105898971700293 53541535759707356057193805)
    ·
      refine ⟨20078075909890258521447677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53541535759707356057193805 20078075909890258521447677)
      ·
        refine ⟨7529278466208846945542879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20078075909890258521447677 7529278466208846945542879)
        ·
          refine ⟨11293917699313270418314319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529278466208846945542879 11293917699313270418314319)
          ·
            refine ⟨16940876548969905627471479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11293917699313270418314319 16940876548969905627471479)
            ·
              refine ⟨25411314823454858441207219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16940876548969905627471479 25411314823454858441207219)
              ·
                refine ⟨38116972235182287661810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25411314823454858441207219 38116972235182287661810829)
                ·
                  refine ⟨14293864588193357873179061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38116972235182287661810829 14293864588193357873179061)
                  ·
                    refine ⟨1340049805143127300610537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14293864588193357873179061 1340049805143127300610537)
                    ·
                      rfl

theorem cell23_7829213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7829213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829213 prefixEnd_7829213 := by exact prefixLift 7829213
  have htrace : WordTrace (prefixWord ++ tailWord_7829213) baseStart_7829213 baseEnd_7829213 := by
    simpa [prefixWord, tailWord_7829213, baseEnd_7829213] using wordTrace_append hprefix tailTrace_7829213
  have hstable : (prefixWord ++ tailWord_7829213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829213).length < 2 ^ (prefixWord ++ tailWord_7829213).sum := by decide
  have hdescent : baseEnd_7829213 < baseStart_7829213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829216 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_7829216 : Nat := 118140960795 + 7829216 * 2 ^ 59
def prefixEnd_7829216 : Nat := 4983230072969 + 3 ^ 40 * 7829216 * 2
def baseEnd_7829216 : Nat := 4020150955871345390094097

theorem tailTrace_7829216 : CollatzResearch.WordTrace tailWord_7829216 prefixEnd_7829216 4020150955871345390094097 := by
  unfold tailWord_7829216
  simp only [CollatzResearch.WordTrace]
  refine ⟨142777483402047515242029751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190369977869396686989373001 142777483402047515242029751)
  ·
    refine ⟨214166225103071272863044627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142777483402047515242029751 214166225103071272863044627)
    ·
      refine ⟨321249337654606909294566941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214166225103071272863044627 321249337654606909294566941)
      ·
        refine ⟨120468501620477590985462603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321249337654606909294566941 120468501620477590985462603)
        ·
          refine ⟨180702752430716386478193905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120468501620477590985462603 180702752430716386478193905)
          ·
            refine ⟨135527064323037289858645429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180702752430716386478193905 135527064323037289858645429)
            ·
              refine ⟨12705662280284745924248009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135527064323037289858645429 12705662280284745924248009)
              ·
                refine ⟨9529246710213559443186007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12705662280284745924248009 9529246710213559443186007)
                ·
                  refine ⟨14293870065320339164779011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9529246710213559443186007 14293870065320339164779011)
                  ·
                    refine ⟨21440805097980508747168517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14293870065320339164779011 21440805097980508747168517)
                    ·
                      refine ⟨4020150955871345390094097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21440805097980508747168517 4020150955871345390094097)
                      ·
                        rfl

theorem cell23_7829216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_7829216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829216 prefixEnd_7829216 := by exact prefixLift 7829216
  have htrace : WordTrace (prefixWord ++ tailWord_7829216) baseStart_7829216 baseEnd_7829216 := by
    simpa [prefixWord, tailWord_7829216, baseEnd_7829216] using wordTrace_append hprefix tailTrace_7829216
  have hstable : (prefixWord ++ tailWord_7829216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829216).length < 2 ^ (prefixWord ++ tailWord_7829216).sum := by decide
  have hdescent : baseEnd_7829216 < baseStart_7829216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829233 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_7829233 : Nat := 118140960795 + 7829233 * 2 ^ 59
def prefixEnd_7829233 : Nat := 4983230072969 + 3 ^ 40 * 7829233 * 2
def baseEnd_7829233 : Nat := 4020159685042471823581519

theorem tailTrace_7829233 : CollatzResearch.WordTrace tailWord_7829233 prefixEnd_7829233 4020159685042471823581519 := by
  unfold tailWord_7829233
  simp only [CollatzResearch.WordTrace]
  refine ⟨285555586845033442387428353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190370391230022294924952235 285555586845033442387428353)
  ·
    refine ⟨214166690133775081790571265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285555586845033442387428353 214166690133775081790571265)
    ·
      refine ⟨160625017600331311342928449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214166690133775081790571265 160625017600331311342928449)
      ·
        refine ⟨120468763200248483507196337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160625017600331311342928449 120468763200248483507196337)
        ·
          refine ⟨90351572400186362630397253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120468763200248483507196337 90351572400186362630397253)
          ·
            refine ⟨16940919825034942993199485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90351572400186362630397253 16940919825034942993199485)
            ·
              refine ⟨6352844934388103622449807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16940919825034942993199485 6352844934388103622449807)
              ·
                refine ⟨9529267401582155433674711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352844934388103622449807 9529267401582155433674711)
                ·
                  refine ⟨14293901102373233150512067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9529267401582155433674711 14293901102373233150512067)
                  ·
                    refine ⟨21440851653559849725768101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14293901102373233150512067 21440851653559849725768101)
                    ·
                      refine ⟨4020159685042471823581519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21440851653559849725768101 4020159685042471823581519)
                      ·
                        rfl

theorem cell23_7829233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_7829233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829233 prefixEnd_7829233 := by exact prefixLift 7829233
  have htrace : WordTrace (prefixWord ++ tailWord_7829233) baseStart_7829233 baseEnd_7829233 := by
    simpa [prefixWord, tailWord_7829233, baseEnd_7829233] using wordTrace_append hprefix tailTrace_7829233
  have hstable : (prefixWord ++ tailWord_7829233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829233).length < 2 ^ (prefixWord ++ tailWord_7829233).sum := by decide
  have hdescent : baseEnd_7829233 < baseStart_7829233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829250 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_7829250 : Nat := 118140960795 + 7829250 * 2 ^ 59
def prefixEnd_7829250 : Nat := 4983230072969 + 3 ^ 40 * 7829250 * 2
def baseEnd_7829250 : Nat := 4020168414213598257068941

theorem tailTrace_7829250 : CollatzResearch.WordTrace tailWord_7829250 prefixEnd_7829250 4020168414213598257068941 := by
  unfold tailWord_7829250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71389051721492963572699301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190370804590647902860531469 71389051721492963572699301)
  ·
    refine ⟨13385447197779930669881119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71389051721492963572699301 13385447197779930669881119)
    ·
      refine ⟨20078170796669896004821679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385447197779930669881119 20078170796669896004821679)
      ·
        refine ⟨30117256195004844007232519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078170796669896004821679 30117256195004844007232519)
        ·
          refine ⟨45175884292507266010848779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30117256195004844007232519 45175884292507266010848779)
          ·
            refine ⟨67763826438760899016273169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45175884292507266010848779 67763826438760899016273169)
            ·
              refine ⟨50822869829070674262204877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67763826438760899016273169 50822869829070674262204877)
              ·
                refine ⟨19058576185901502848326829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50822869829070674262204877 19058576185901502848326829)
                ·
                  refine ⟨7146966069713063568122561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19058576185901502848326829 7146966069713063568122561)
                  ·
                    refine ⟨5360224552284797676091921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146966069713063568122561 5360224552284797676091921)
                    ·
                      refine ⟨4020168414213598257068941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360224552284797676091921 4020168414213598257068941)
                      ·
                        rfl

theorem cell23_7829250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_7829250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829250 prefixEnd_7829250 := by exact prefixLift 7829250
  have htrace : WordTrace (prefixWord ++ tailWord_7829250) baseStart_7829250 baseEnd_7829250 := by
    simpa [prefixWord, tailWord_7829250, baseEnd_7829250] using wordTrace_append hprefix tailTrace_7829250
  have hstable : (prefixWord ++ tailWord_7829250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829250).length < 2 ^ (prefixWord ++ tailWord_7829250).sum := by decide
  have hdescent : baseEnd_7829250 < baseStart_7829250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829279 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7829279 : Nat := 118140960795 + 7829279 * 2 ^ 59
def prefixEnd_7829279 : Nat := 4983230072969 + 3 ^ 40 * 7829279 * 2
def baseEnd_7829279 : Nat := 4020183305152578643606307

theorem tailTrace_7829279 : CollatzResearch.WordTrace tailWord_7829279 prefixEnd_7829279 4020183305152578643606307 := by
  unfold tailWord_7829279
  simp only [CollatzResearch.WordTrace]
  refine ⟨285557264602866792243602891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190371509735244528162401927 285557264602866792243602891)
  ·
    refine ⟨428335896904300188365404337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285557264602866792243602891 428335896904300188365404337)
    ·
      refine ⟨321251922678225141274053253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428335896904300188365404337 321251922678225141274053253)
      ·
        refine ⟨60234735502167213988884985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321251922678225141274053253 60234735502167213988884985)
        ·
          refine ⟨45176051626625410491663739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60234735502167213988884985 45176051626625410491663739)
          ·
            refine ⟨67764077439938115737495609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45176051626625410491663739 67764077439938115737495609)
            ·
              refine ⟨50823058079953586803121707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67764077439938115737495609 50823058079953586803121707)
              ·
                refine ⟨76234587119930380204682561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50823058079953586803121707 76234587119930380204682561)
                ·
                  refine ⟨57175940339947785153511921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76234587119930380204682561 57175940339947785153511921)
                  ·
                    refine ⟨42881955254960838865133941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57175940339947785153511921 42881955254960838865133941)
                    ·
                      refine ⟨4020183305152578643606307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42881955254960838865133941 4020183305152578643606307)
                      ·
                        rfl

theorem cell23_7829279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7829279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829279 prefixEnd_7829279 := by exact prefixLift 7829279
  have htrace : WordTrace (prefixWord ++ tailWord_7829279) baseStart_7829279 baseEnd_7829279 := by
    simpa [prefixWord, tailWord_7829279, baseEnd_7829279] using wordTrace_append hprefix tailTrace_7829279
  have hstable : (prefixWord ++ tailWord_7829279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829279).length < 2 ^ (prefixWord ++ tailWord_7829279).sum := by decide
  have hdescent : baseEnd_7829279 < baseStart_7829279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829300 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_7829300 : Nat := 118140960795 + 7829300 * 2 ^ 59
def prefixEnd_7829300 : Nat := 4983230072969 + 3 ^ 40 * 7829300 * 2
def baseEnd_7829300 : Nat := 4020194088246323061443711

theorem tailTrace_7829300 : CollatzResearch.WordTrace tailWord_7829300 prefixEnd_7829300 4020194088246323061443711 := by
  unfold tailWord_7829300
  simp only [CollatzResearch.WordTrace]
  refine ⟨142779015267895356415058677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190372020357193808553411569 142779015267895356415058677)
  ·
    refine ⟨13385532681365189663911751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142779015267895356415058677 13385532681365189663911751)
    ·
      refine ⟨20078299022047784495867627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385532681365189663911751 20078299022047784495867627)
      ·
        refine ⟨30117448533071676743801441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078299022047784495867627 30117448533071676743801441)
        ·
          refine ⟨22588086399803757557851081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30117448533071676743801441 22588086399803757557851081)
          ·
            refine ⟨16941064799852818168388311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22588086399803757557851081 16941064799852818168388311)
            ·
              refine ⟨25411597199779227252582467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941064799852818168388311 25411597199779227252582467)
              ·
                refine ⟨38117395799668840878873701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25411597199779227252582467 38117395799668840878873701)
                ·
                  refine ⟨7147011712437907664788819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38117395799668840878873701 7147011712437907664788819)
                  ·
                    refine ⟨10720517568656861497183229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147011712437907664788819 10720517568656861497183229)
                    ·
                      refine ⟨4020194088246323061443711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10720517568656861497183229 4020194088246323061443711)
                      ·
                        rfl

theorem cell23_7829300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_7829300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829300 prefixEnd_7829300 := by exact prefixLift 7829300
  have htrace : WordTrace (prefixWord ++ tailWord_7829300) baseStart_7829300 baseEnd_7829300 := by
    simpa [prefixWord, tailWord_7829300, baseEnd_7829300] using wordTrace_append hprefix tailTrace_7829300
  have hstable : (prefixWord ++ tailWord_7829300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829300).length < 2 ^ (prefixWord ++ tailWord_7829300).sum := by decide
  have hdescent : baseEnd_7829300 < baseStart_7829300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829374 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7829374 : Nat := 118140960795 + 7829374 * 2 ^ 59
def prefixEnd_7829374 : Nat := 4983230072969 + 3 ^ 40 * 7829374 * 2
def baseEnd_7829374 : Nat := 4020232085814755771918371

theorem tailTrace_7829374 : CollatzResearch.WordTrace tailWord_7829374 prefixEnd_7829374 4020232085814755771918371 := by
  unfold tailWord_7829374
  simp only [CollatzResearch.WordTrace]
  refine ⟨35695091192190327933538897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190373819691681748978874117 35695091192190327933538897)
  ·
    refine ⟨26771318394142745950154173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35695091192190327933538897 26771318394142745950154173)
    ·
      refine ⟨10039244397803529731307815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26771318394142745950154173 10039244397803529731307815)
      ·
        refine ⟨15058866596705294596961723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039244397803529731307815 15058866596705294596961723)
        ·
          refine ⟨22588299895057941895442585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15058866596705294596961723 22588299895057941895442585)
          ·
            refine ⟨16941224921293456421581939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22588299895057941895442585 16941224921293456421581939)
            ·
              refine ⟨25411837381940184632372909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941224921293456421581939 25411837381940184632372909)
              ·
                refine ⟨9529439018227569237139841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25411837381940184632372909 9529439018227569237139841)
                ·
                  refine ⟨7147079263670676927854881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529439018227569237139841 7147079263670676927854881)
                  ·
                    refine ⟨5360309447753007695891161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147079263670676927854881 5360309447753007695891161)
                    ·
                      refine ⟨4020232085814755771918371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360309447753007695891161 4020232085814755771918371)
                      ·
                        rfl

theorem cell23_7829374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7829374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829374 prefixEnd_7829374 := by exact prefixLift 7829374
  have htrace : WordTrace (prefixWord ++ tailWord_7829374) baseStart_7829374 baseEnd_7829374 := by
    simpa [prefixWord, tailWord_7829374, baseEnd_7829374] using wordTrace_append hprefix tailTrace_7829374
  have hstable : (prefixWord ++ tailWord_7829374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829374).length < 2 ^ (prefixWord ++ tailWord_7829374).sum := by decide
  have hdescent : baseEnd_7829374 < baseStart_7829374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829463 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_7829463 : Nat := 118140960795 + 7829463 * 2 ^ 59
def prefixEnd_7829463 : Nat := 4983230072969 + 3 ^ 40 * 7829463 * 2
def baseEnd_7829463 : Nat := 4020277785593005923705461

theorem tailTrace_7829463 : CollatzResearch.WordTrace tailWord_7829463 prefixEnd_7829463 4020277785593005923705461 := by
  unfold tailWord_7829463
  simp only [CollatzResearch.WordTrace]
  refine ⟨285563975634200191668301043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190375983756133461112200695 285563975634200191668301043)
  ·
    refine ⟨428345963451300287502451565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285563975634200191668301043 428345963451300287502451565)
    ·
      refine ⟨160629736294237607813419337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428345963451300287502451565 160629736294237607813419337)
      ·
        refine ⟨120472302220678205860064503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160629736294237607813419337 120472302220678205860064503)
        ·
          refine ⟨180708453331017308790096755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120472302220678205860064503 180708453331017308790096755)
          ·
            refine ⟨271062679996525963185145133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180708453331017308790096755 271062679996525963185145133)
            ·
              refine ⟨101648504998697236194429425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271062679996525963185145133 101648504998697236194429425)
              ·
                refine ⟨76236378749022927145822069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101648504998697236194429425 76236378749022927145822069)
                ·
                  refine ⟨7147160507720899419920819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76236378749022927145822069 7147160507720899419920819)
                  ·
                    refine ⟨10720740761581349129881229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147160507720899419920819 10720740761581349129881229)
                    ·
                      refine ⟨4020277785593005923705461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10720740761581349129881229 4020277785593005923705461)
                      ·
                        rfl

theorem cell23_7829463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_7829463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829463 prefixEnd_7829463 := by exact prefixLift 7829463
  have htrace : WordTrace (prefixWord ++ tailWord_7829463) baseStart_7829463 baseEnd_7829463 := by
    simpa [prefixWord, tailWord_7829463, baseEnd_7829463] using wordTrace_append hprefix tailTrace_7829463
  have hstable : (prefixWord ++ tailWord_7829463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829463).length < 2 ^ (prefixWord ++ tailWord_7829463).sum := by decide
  have hdescent : baseEnd_7829463 < baseStart_7829463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829533 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7829533 : Nat := 118140960795 + 7829533 * 2 ^ 59
def prefixEnd_7829533 : Nat := 4983230072969 + 3 ^ 40 * 7829533 * 2
def baseEnd_7829533 : Nat := 4020313729238820649830139

theorem tailTrace_7829533 : CollatzResearch.WordTrace tailWord_7829533 prefixEnd_7829533 4020313729238820649830139 := by
  unfold tailWord_7829533
  simp only [CollatzResearch.WordTrace]
  refine ⟨285566528743946593623349253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190377685829297729082232835 285566528743946593623349253)
  ·
    refine ⟨53543724139489986304377985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285566528743946593623349253 53543724139489986304377985)
    ·
      refine ⟨40157793104617489728283489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53543724139489986304377985 40157793104617489728283489)
      ·
        refine ⟨30118344828463117296212617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40157793104617489728283489 30118344828463117296212617)
        ·
          refine ⟨22588758621347337972159463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30118344828463117296212617 22588758621347337972159463)
          ·
            refine ⟨33883137932021006958239195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22588758621347337972159463 33883137932021006958239195)
            ·
              refine ⟨50824706898031510437358793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33883137932021006958239195 50824706898031510437358793)
              ·
                refine ⟨38118530173523632828019095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50824706898031510437358793 38118530173523632828019095)
                ·
                  refine ⟨57177795260285449242028643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38118530173523632828019095 57177795260285449242028643)
                  ·
                    refine ⟨85766692890428173863042965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57177795260285449242028643 85766692890428173863042965)
                    ·
                      refine ⟨4020313729238820649830139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85766692890428173863042965 4020313729238820649830139)
                      ·
                        rfl

theorem cell23_7829533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7829533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829533 prefixEnd_7829533 := by exact prefixLift 7829533
  have htrace : WordTrace (prefixWord ++ tailWord_7829533) baseStart_7829533 baseEnd_7829533 := by
    simpa [prefixWord, tailWord_7829533, baseEnd_7829533] using wordTrace_append hprefix tailTrace_7829533
  have hstable : (prefixWord ++ tailWord_7829533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829533).length < 2 ^ (prefixWord ++ tailWord_7829533).sum := by decide
  have hdescent : baseEnd_7829533 < baseStart_7829533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829563 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 7, 2]
def baseStart_7829563 : Nat := 118140960795 + 7829563 * 2 ^ 59
def prefixEnd_7829563 : Nat := 4983230072969 + 3 ^ 40 * 7829563 * 2
def baseEnd_7829563 : Nat := 4020329133658455532455001

theorem tailTrace_7829563 : CollatzResearch.WordTrace tailWord_7829563 prefixEnd_7829563 4020329133658455532455001 := by
  unfold tailWord_7829563
  simp only [CollatzResearch.WordTrace]
  refine ⟨285567622933837908746941343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190378415289225272497960895 285567622933837908746941343)
  ·
    refine ⟨428351434400756863120412015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285567622933837908746941343 428351434400756863120412015)
    ·
      refine ⟨642527151601135294680618023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428351434400756863120412015 642527151601135294680618023)
      ·
        refine ⟨963790727401702942020927035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642527151601135294680618023 963790727401702942020927035)
        ·
          refine ⟨1445686091102554413031390553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963790727401702942020927035 1445686091102554413031390553)
          ·
            refine ⟨1084264568326915809773542915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445686091102554413031390553 1084264568326915809773542915)
            ·
              refine ⟨1626396852490373714660314373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084264568326915809773542915 1626396852490373714660314373)
              ·
                refine ⟨304949409841945071498808945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1626396852490373714660314373 304949409841945071498808945)
                ·
                  refine ⟨228712057381458803624106709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304949409841945071498808945 228712057381458803624106709)
                  ·
                    refine ⟨5360438844877940709940001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228712057381458803624106709 5360438844877940709940001)
                    ·
                      refine ⟨4020329133658455532455001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360438844877940709940001 4020329133658455532455001)
                      ·
                        rfl

theorem cell23_7829563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7, 2].length) (baseStart_7829563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829563 prefixEnd_7829563 := by exact prefixLift 7829563
  have htrace : WordTrace (prefixWord ++ tailWord_7829563) baseStart_7829563 baseEnd_7829563 := by
    simpa [prefixWord, tailWord_7829563, baseEnd_7829563] using wordTrace_append hprefix tailTrace_7829563
  have hstable : (prefixWord ++ tailWord_7829563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829563).length < 2 ^ (prefixWord ++ tailWord_7829563).sum := by decide
  have hdescent : baseEnd_7829563 < baseStart_7829563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829640 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7829640 : Nat := 118140960795 + 7829640 * 2 ^ 59
def prefixEnd_7829640 : Nat := 4983230072969 + 3 ^ 40 * 7829640 * 2
def baseEnd_7829640 : Nat := 4020368671668851731192147

theorem tailTrace_7829640 : CollatzResearch.WordTrace tailWord_7829640 prefixEnd_7829640 4020368671668851731192147 := by
  unfold tailWord_7829640
  simp only [CollatzResearch.WordTrace]
  refine ⟨142785215677279475448747187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190380287569705967264996249 142785215677279475448747187)
  ·
    refine ⟨214177823515919213173120781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142785215677279475448747187 214177823515919213173120781)
    ·
      refine ⟨80316683818469704939920293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214177823515919213173120781 80316683818469704939920293)
      ·
        refine ⟨15059378215963069676235055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80316683818469704939920293 15059378215963069676235055)
        ·
          refine ⟨22589067323944604514352583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059378215963069676235055 22589067323944604514352583)
          ·
            refine ⟨33883600985916906771528875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22589067323944604514352583 33883600985916906771528875)
            ·
              refine ⟨50825401478875360157293313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33883600985916906771528875 50825401478875360157293313)
              ·
                refine ⟨38119051109156520117969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50825401478875360157293313 38119051109156520117969985)
                ·
                  refine ⟨28589288331867390088477489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38119051109156520117969985 28589288331867390088477489)
                  ·
                    refine ⟨21441966248900542566358117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28589288331867390088477489 21441966248900542566358117)
                    ·
                      refine ⟨4020368671668851731192147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21441966248900542566358117 4020368671668851731192147)
                      ·
                        rfl

theorem cell23_7829640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7829640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829640 prefixEnd_7829640 := by exact prefixLift 7829640
  have htrace : WordTrace (prefixWord ++ tailWord_7829640) baseStart_7829640 baseEnd_7829640 := by
    simpa [prefixWord, tailWord_7829640, baseEnd_7829640] using wordTrace_append hprefix tailTrace_7829640
  have hstable : (prefixWord ++ tailWord_7829640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829640).length < 2 ^ (prefixWord ++ tailWord_7829640).sum := by decide
  have hdescent : baseEnd_7829640 < baseStart_7829640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829650 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_7829650 : Nat := 118140960795 + 7829650 * 2 ^ 59
def prefixEnd_7829650 : Nat := 4983230072969 + 3 ^ 40 * 7829650 * 2
def baseEnd_7829650 : Nat := 446708200719488521340789

theorem tailTrace_7829650 : CollatzResearch.WordTrace tailWord_7829650 prefixEnd_7829650 446708200719488521340789 := by
  unfold tailWord_7829650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71392699021130680651339601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190380530723015148403572269 71392699021130680651339601)
  ·
    refine ⟨53544524265848010488504701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71392699021130680651339601 53544524265848010488504701)
    ·
      refine ⟨20079196599693003933189263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53544524265848010488504701 20079196599693003933189263)
      ·
        refine ⟨30118794899539505899783895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20079196599693003933189263 30118794899539505899783895)
        ·
          refine ⟨45178192349309258849675843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30118794899539505899783895 45178192349309258849675843)
          ·
            refine ⟨67767288523963888274513765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45178192349309258849675843 67767288523963888274513765)
            ·
              refine ⟨12706366598243229051471331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67767288523963888274513765 12706366598243229051471331)
              ·
                refine ⟨19059549897364843577206997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12706366598243229051471331 19059549897364843577206997)
                ·
                  refine ⟨446708200719488521340789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19059549897364843577206997 446708200719488521340789)
                  ·
                    rfl

theorem cell23_7829650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_7829650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829650 prefixEnd_7829650 := by exact prefixLift 7829650
  have htrace : WordTrace (prefixWord ++ tailWord_7829650) baseStart_7829650 baseEnd_7829650 := by
    simpa [prefixWord, tailWord_7829650, baseEnd_7829650] using wordTrace_append hprefix tailTrace_7829650
  have hstable : (prefixWord ++ tailWord_7829650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829650).length < 2 ^ (prefixWord ++ tailWord_7829650).sum := by decide
  have hdescent : baseEnd_7829650 < baseStart_7829650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829660 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7829660 : Nat := 118140960795 + 7829660 * 2 ^ 59
def prefixEnd_7829660 : Nat := 4983230072969 + 3 ^ 40 * 7829660 * 2
def baseEnd_7829660 : Nat := 4020378941281941652942055

theorem tailTrace_7829660 : CollatzResearch.WordTrace tailWord_7829660 prefixEnd_7829660 4020378941281941652942055 := by
  unfold tailWord_7829660
  simp only [CollatzResearch.WordTrace]
  refine ⟨142785580407243247156611217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190380773876324329542148289 142785580407243247156611217)
  ·
    refine ⟨107089185305432435367458413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142785580407243247156611217 107089185305432435367458413)
    ·
      refine ⟨40158444489537163262796905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107089185305432435367458413 40158444489537163262796905)
      ·
        refine ⟨30118833367152872447097679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40158444489537163262796905 30118833367152872447097679)
        ·
          refine ⟨45178250050729308670646519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30118833367152872447097679 45178250050729308670646519)
          ·
            refine ⟨67767375076093963005969779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45178250050729308670646519 67767375076093963005969779)
            ·
              refine ⟨101651062614140944508954669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67767375076093963005969779 101651062614140944508954669)
              ·
                refine ⟨38119148480302854190858001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101651062614140944508954669 38119148480302854190858001)
                ·
                  refine ⟨28589361360227140643143501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38119148480302854190858001 28589361360227140643143501)
                  ·
                    refine ⟨10721010510085177741178813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28589361360227140643143501 10721010510085177741178813)
                    ·
                      refine ⟨4020378941281941652942055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721010510085177741178813 4020378941281941652942055)
                      ·
                        rfl

theorem cell23_7829660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7829660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829660 prefixEnd_7829660 := by exact prefixLift 7829660
  have htrace : WordTrace (prefixWord ++ tailWord_7829660) baseStart_7829660 baseEnd_7829660 := by
    simpa [prefixWord, tailWord_7829660, baseEnd_7829660] using wordTrace_append hprefix tailTrace_7829660
  have hstable : (prefixWord ++ tailWord_7829660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829660).length < 2 ^ (prefixWord ++ tailWord_7829660).sum := by decide
  have hdescent : baseEnd_7829660 < baseStart_7829660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829661 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_7829661 : Nat := 118140960795 + 7829661 * 2 ^ 59
def prefixEnd_7829661 : Nat := 4983230072969 + 3 ^ 40 * 7829661 * 2
def baseEnd_7829661 : Nat := 4020379454762596149029551

theorem tailTrace_7829661 : CollatzResearch.WordTrace tailWord_7829661 prefixEnd_7829661 4020379454762596149029551 := by
  unfold tailWord_7829661
  simp only [CollatzResearch.WordTrace]
  refine ⟨285571197287482871484008837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190380798191655247656005891 285571197287482871484008837)
  ·
    refine ⟨53544599491403038403251657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285571197287482871484008837 53544599491403038403251657)
    ·
      refine ⟨40158449618552278802438743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53544599491403038403251657 40158449618552278802438743)
      ·
        refine ⟨60237674427828418203658115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40158449618552278802438743 60237674427828418203658115)
        ·
          refine ⟨90356511641742627305487173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60237674427828418203658115 90356511641742627305487173)
          ·
            refine ⟨16941845932826742619778845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90356511641742627305487173 16941845932826742619778845)
            ·
              refine ⟨6353192224810028482417067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16941845932826742619778845 6353192224810028482417067)
              ·
                refine ⟨9529788337215042723625601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353192224810028482417067 9529788337215042723625601)
                ·
                  refine ⟨7147341252911282042719201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529788337215042723625601 7147341252911282042719201)
                  ·
                    refine ⟨5360505939683461532039401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147341252911282042719201 5360505939683461532039401)
                    ·
                      refine ⟨4020379454762596149029551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360505939683461532039401 4020379454762596149029551)
                      ·
                        rfl

theorem cell23_7829661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_7829661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829661 prefixEnd_7829661 := by exact prefixLift 7829661
  have htrace : WordTrace (prefixWord ++ tailWord_7829661) baseStart_7829661 baseEnd_7829661 := by
    simpa [prefixWord, tailWord_7829661, baseEnd_7829661] using wordTrace_append hprefix tailTrace_7829661
  have hstable : (prefixWord ++ tailWord_7829661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829661).length < 2 ^ (prefixWord ++ tailWord_7829661).sum := by decide
  have hdescent : baseEnd_7829661 < baseStart_7829661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829713 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_7829713 : Nat := 118140960795 + 7829713 * 2 ^ 59
def prefixEnd_7829713 : Nat := 4983230072969 + 3 ^ 40 * 7829713 * 2
def baseEnd_7829713 : Nat := 4020406155756629945579311

theorem tailTrace_7829713 : CollatzResearch.WordTrace tailWord_7829713 prefixEnd_7829713 4020406155756629945579311 := by
  unfold tailWord_7829713
  simp only [CollatzResearch.WordTrace]
  refine ⟨285573093883294484364901793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190382062588862989576601195 285573093883294484364901793)
  ·
    refine ⟨214179820412470863273676345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285573093883294484364901793 214179820412470863273676345)
    ·
      refine ⟨160634865309353147455257259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214179820412470863273676345 160634865309353147455257259)
      ·
        refine ⟨240952297964029721182885889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160634865309353147455257259 240952297964029721182885889)
        ·
          refine ⟨180714223473022290887164417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240952297964029721182885889 180714223473022290887164417)
          ·
            refine ⟨135535667604766718165373313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180714223473022290887164417 135535667604766718165373313)
            ·
              refine ⟨101651750703575038624029985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135535667604766718165373313 101651750703575038624029985)
              ·
                refine ⟨76238813027681278968022489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101651750703575038624029985 76238813027681278968022489)
                ·
                  refine ⟨57179109770760959226016867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76238813027681278968022489 57179109770760959226016867)
                  ·
                    refine ⟨85768664656141438839025301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57179109770760959226016867 85768664656141438839025301)
                    ·
                      refine ⟨4020406155756629945579311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85768664656141438839025301 4020406155756629945579311)
                      ·
                        rfl

theorem cell23_7829713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_7829713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829713 prefixEnd_7829713 := by exact prefixLift 7829713
  have htrace : WordTrace (prefixWord ++ tailWord_7829713) baseStart_7829713 baseEnd_7829713 := by
    simpa [prefixWord, tailWord_7829713, baseEnd_7829713] using wordTrace_append hprefix tailTrace_7829713
  have hstable : (prefixWord ++ tailWord_7829713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829713).length < 2 ^ (prefixWord ++ tailWord_7829713).sum := by decide
  have hdescent : baseEnd_7829713 < baseStart_7829713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829770 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_7829770 : Nat := 118140960795 + 7829770 * 2 ^ 59
def prefixEnd_7829770 : Nat := 4983230072969 + 3 ^ 40 * 7829770 * 2
def baseEnd_7829770 : Nat := 1340145141384645407522183

theorem tailTrace_7829770 : CollatzResearch.WordTrace tailWord_7829770 prefixEnd_7829770 1340145141384645407522183 := by
  unfold tailWord_7829770
  simp only [CollatzResearch.WordTrace]
  refine ⟨71393793211021995774931691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190383448562725322066484509 71393793211021995774931691)
  ·
    refine ⟨107090689816532993662397537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71393793211021995774931691 107090689816532993662397537)
    ·
      refine ⟨80318017362399745246798153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107090689816532993662397537 80318017362399745246798153)
      ·
        refine ⟨60238513021799808935098615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80318017362399745246798153 60238513021799808935098615)
        ·
          refine ⟨90357769532699713402647923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60238513021799808935098615 90357769532699713402647923)
          ·
            refine ⟨135536654299049570103971885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90357769532699713402647923 135536654299049570103971885)
            ·
              refine ⟨50826245362143588788989457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135536654299049570103971885 50826245362143588788989457)
              ·
                refine ⟨38119684021607691591742093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50826245362143588788989457 38119684021607691591742093)
                ·
                  refine ⟨14294881508102884346903285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38119684021607691591742093 14294881508102884346903285)
                  ·
                    refine ⟨1340145141384645407522183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14294881508102884346903285 1340145141384645407522183)
                    ·
                      rfl

theorem cell23_7829770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_7829770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829770 prefixEnd_7829770 := by exact prefixLift 7829770
  have htrace : WordTrace (prefixWord ++ tailWord_7829770) baseStart_7829770 baseEnd_7829770 := by
    simpa [prefixWord, tailWord_7829770, baseEnd_7829770] using wordTrace_append hprefix tailTrace_7829770
  have hstable : (prefixWord ++ tailWord_7829770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829770).length < 2 ^ (prefixWord ++ tailWord_7829770).sum := by decide
  have hdescent : baseEnd_7829770 < baseStart_7829770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829794 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_7829794 : Nat := 118140960795 + 7829794 * 2 ^ 59
def prefixEnd_7829794 : Nat := 4983230072969 + 3 ^ 40 * 7829794 * 2
def baseEnd_7829794 : Nat := 4020447747689644128666439

theorem tailTrace_7829794 : CollatzResearch.WordTrace tailWord_7829794 prefixEnd_7829794 4020447747689644128666439 := by
  unfold tailWord_7829794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71394012049000258799650109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190384032130667356799066957 71394012049000258799650109)
  ·
    refine ⟨26772754518375097049868791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71394012049000258799650109 26772754518375097049868791)
    ·
      refine ⟨40159131777562645574803187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26772754518375097049868791 40159131777562645574803187)
      ·
        refine ⟨60238697666343968362204781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40159131777562645574803187 60238697666343968362204781)
        ·
          refine ⟨22589511624878988135826793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60238697666343968362204781 22589511624878988135826793)
          ·
            refine ⟨16942133718659241101870095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22589511624878988135826793 16942133718659241101870095)
            ·
              refine ⟨25413200577988861652805143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16942133718659241101870095 25413200577988861652805143)
              ·
                refine ⟨38119800866983292479207715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25413200577988861652805143 38119800866983292479207715)
                ·
                  refine ⟨57179701300474938718811573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38119800866983292479207715 57179701300474938718811573)
                  ·
                    refine ⟨5360596996919525504888585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57179701300474938718811573 5360596996919525504888585)
                    ·
                      refine ⟨4020447747689644128666439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360596996919525504888585 4020447747689644128666439)
                      ·
                        rfl

theorem cell23_7829794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_7829794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829794 prefixEnd_7829794 := by exact prefixLift 7829794
  have htrace : WordTrace (prefixWord ++ tailWord_7829794) baseStart_7829794 baseEnd_7829794 := by
    simpa [prefixWord, tailWord_7829794, baseEnd_7829794] using wordTrace_append hprefix tailTrace_7829794
  have hstable : (prefixWord ++ tailWord_7829794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829794).length < 2 ^ (prefixWord ++ tailWord_7829794).sum := by decide
  have hdescent : baseEnd_7829794 < baseStart_7829794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829820 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7829820 : Nat := 118140960795 + 7829820 * 2 ^ 59
def prefixEnd_7829820 : Nat := 4983230072969 + 3 ^ 40 * 7829820 * 2
def baseEnd_7829820 : Nat := 4020461098186661026941319

theorem tailTrace_7829820 : CollatzResearch.WordTrace tailWord_7829820 prefixEnd_7829820 4020461098186661026941319 := by
  unfold tailWord_7829820
  simp only [CollatzResearch.WordTrace]
  refine ⟨142788498246953420819523457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190384664329271227759364609 142788498246953420819523457)
  ·
    refine ⟨107091373685215065614642593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142788498246953420819523457 107091373685215065614642593)
    ·
      refine ⟨80318530263911299210981945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107091373685215065614642593 80318530263911299210981945)
      ·
        refine ⟨60238897697933474408236459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80318530263911299210981945 60238897697933474408236459)
        ·
          refine ⟨90358346546900211612354689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60238897697933474408236459 90358346546900211612354689)
          ·
            refine ⟨67768759910175158709266017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90358346546900211612354689 67768759910175158709266017)
            ·
              refine ⟨50826569932631369031949513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67768759910175158709266017 50826569932631369031949513)
              ·
                refine ⟨38119927449473526773962135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50826569932631369031949513 38119927449473526773962135)
                ·
                  refine ⟨57179891174210290160943203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38119927449473526773962135 57179891174210290160943203)
                  ·
                    refine ⟨85769836761315435241414805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57179891174210290160943203 85769836761315435241414805)
                    ·
                      refine ⟨4020461098186661026941319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85769836761315435241414805 4020461098186661026941319)
                      ·
                        rfl

theorem cell23_7829820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7829820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829820 prefixEnd_7829820 := by exact prefixLift 7829820
  have htrace : WordTrace (prefixWord ++ tailWord_7829820) baseStart_7829820 baseEnd_7829820 := by
    simpa [prefixWord, tailWord_7829820, baseEnd_7829820] using wordTrace_append hprefix tailTrace_7829820
  have hstable : (prefixWord ++ tailWord_7829820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829820).length < 2 ^ (prefixWord ++ tailWord_7829820).sum := by decide
  have hdescent : baseEnd_7829820 < baseStart_7829820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829844 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_7829844 : Nat := 118140960795 + 7829844 * 2 ^ 59
def prefixEnd_7829844 : Nat := 4983230072969 + 3 ^ 40 * 7829844 * 2
def baseEnd_7829844 : Nat := 4020473421722368933041209

theorem tailTrace_7829844 : CollatzResearch.WordTrace tailWord_7829844 prefixEnd_7829844 4020473421722368933041209 := by
  unfold tailWord_7829844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142788935922909946868960293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190385247897213262491947057 142788935922909946868960293)
  ·
    refine ⟨26772925485545615037930055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142788935922909946868960293 26772925485545615037930055)
    ·
      refine ⟨40159388228318422556895083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26772925485545615037930055 40159388228318422556895083)
      ·
        refine ⟨60239082342477633835342625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40159388228318422556895083 60239082342477633835342625)
        ·
          refine ⟨45179311756858225376506969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60239082342477633835342625 45179311756858225376506969)
          ·
            refine ⟨33884483817643669032380227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45179311756858225376506969 33884483817643669032380227)
            ·
              refine ⟨50826725726465503548570341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33884483817643669032380227 50826725726465503548570341)
              ·
                refine ⟨9530011073712281915356939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50826725726465503548570341 9530011073712281915356939)
                ·
                  refine ⟨14295016610568422873035409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9530011073712281915356939 14295016610568422873035409)
                  ·
                    refine ⟨10721262457926317154776557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14295016610568422873035409 10721262457926317154776557)
                    ·
                      refine ⟨4020473421722368933041209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721262457926317154776557 4020473421722368933041209)
                      ·
                        rfl

theorem cell23_7829844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_7829844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829844 prefixEnd_7829844 := by exact prefixLift 7829844
  have htrace : WordTrace (prefixWord ++ tailWord_7829844) baseStart_7829844 baseEnd_7829844 := by
    simpa [prefixWord, tailWord_7829844, baseEnd_7829844] using wordTrace_append hprefix tailTrace_7829844
  have hstable : (prefixWord ++ tailWord_7829844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829844).length < 2 ^ (prefixWord ++ tailWord_7829844).sum := by decide
  have hdescent : baseEnd_7829844 < baseStart_7829844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829852 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7829852 : Nat := 118140960795 + 7829852 * 2 ^ 59
def prefixEnd_7829852 : Nat := 4983230072969 + 3 ^ 40 * 7829852 * 2
def baseEnd_7829852 : Nat := 4020477529567604901741173

theorem tailTrace_7829852 : CollatzResearch.WordTrace tailWord_7829852 prefixEnd_7829852 4020477529567604901741173 := by
  unfold tailWord_7829852
  simp only [CollatzResearch.WordTrace]
  refine ⟨142789081814895455552105905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190385442419860607402807873 142789081814895455552105905)
  ·
    refine ⟨107091811361171591664079429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142789081814895455552105905 107091811361171591664079429)
    ·
      refine ⟨20079714630219673437014893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107091811361171591664079429 20079714630219673437014893)
      ·
        refine ⟨7529892986332377538880585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20079714630219673437014893 7529892986332377538880585)
        ·
          refine ⟨5647419739749283154160439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529892986332377538880585 5647419739749283154160439)
          ·
            refine ⟨8471129609623924731240659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647419739749283154160439 8471129609623924731240659)
            ·
              refine ⟨12706694414435887096860989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471129609623924731240659 12706694414435887096860989)
              ·
                refine ⟨4765010405413457661322871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706694414435887096860989 4765010405413457661322871)
                ·
                  refine ⟨7147515608120186491984307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765010405413457661322871 7147515608120186491984307)
                  ·
                    refine ⟨10721273412180279737976461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147515608120186491984307 10721273412180279737976461)
                    ·
                      refine ⟨4020477529567604901741173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721273412180279737976461 4020477529567604901741173)
                      ·
                        rfl

theorem cell23_7829852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7829852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829852 prefixEnd_7829852 := by exact prefixLift 7829852
  have htrace : WordTrace (prefixWord ++ tailWord_7829852) baseStart_7829852 baseEnd_7829852 := by
    simpa [prefixWord, tailWord_7829852, baseEnd_7829852] using wordTrace_append hprefix tailTrace_7829852
  have hstable : (prefixWord ++ tailWord_7829852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829852).length < 2 ^ (prefixWord ++ tailWord_7829852).sum := by decide
  have hdescent : baseEnd_7829852 < baseStart_7829852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829874 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_7829874 : Nat := 118140960795 + 7829874 * 2 ^ 59
def prefixEnd_7829874 : Nat := 4983230072969 + 3 ^ 40 * 7829874 * 2
def baseEnd_7829874 : Nat := 4020488826142003815666071

theorem tailTrace_7829874 : CollatzResearch.WordTrace tailWord_7829874 prefixEnd_7829874 4020488826142003815666071 := by
  unfold tailWord_7829874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71394741508927802215378169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190385977357140805907675117 71394741508927802215378169)
  ·
    refine ⟨53546056131695851661533627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71394741508927802215378169 53546056131695851661533627)
    ·
      refine ⟨80319084197543777492300441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53546056131695851661533627 80319084197543777492300441)
      ·
        refine ⟨60239313148157833119225331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80319084197543777492300441 60239313148157833119225331)
        ·
          refine ⟨90358969722236749678837997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60239313148157833119225331 90358969722236749678837997)
          ·
            refine ⟨33884613645838781129564249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90358969722236749678837997 33884613645838781129564249)
            ·
              refine ⟨25413460234379085847173187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33884613645838781129564249 25413460234379085847173187)
              ·
                refine ⟨38120190351568628770759781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25413460234379085847173187 38120190351568628770759781)
                ·
                  refine ⟨7147535690919117894517459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38120190351568628770759781 7147535690919117894517459)
                  ·
                    refine ⟨10721303536378676841776189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147535690919117894517459 10721303536378676841776189)
                    ·
                      refine ⟨4020488826142003815666071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721303536378676841776189 4020488826142003815666071)
                      ·
                        rfl

theorem cell23_7829874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_7829874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829874 prefixEnd_7829874 := by exact prefixLift 7829874
  have htrace : WordTrace (prefixWord ++ tailWord_7829874) baseStart_7829874 baseEnd_7829874 := by
    simpa [prefixWord, tailWord_7829874, baseEnd_7829874] using wordTrace_append hprefix tailTrace_7829874
  have hstable : (prefixWord ++ tailWord_7829874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829874).length < 2 ^ (prefixWord ++ tailWord_7829874).sum := by decide
  have hdescent : baseEnd_7829874 < baseStart_7829874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829891 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 3]
def baseStart_7829891 : Nat := 118140960795 + 7829891 * 2 ^ 59
def prefixEnd_7829891 : Nat := 4983230072969 + 3 ^ 40 * 7829891 * 2
def baseEnd_7829891 : Nat := 4020497555313130249153493

theorem tailTrace_7829891 : CollatzResearch.WordTrace tailWord_7829891 prefixEnd_7829891 4020497555313130249153493 := by
  unfold tailWord_7829891
  simp only [CollatzResearch.WordTrace]
  refine ⟨285579586076649620764881527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190386390717766413843254351 285579586076649620764881527)
  ·
    refine ⟨428369379114974431147322291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285579586076649620764881527 428369379114974431147322291)
    ·
      refine ⟨642554068672461646720983437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428369379114974431147322291 642554068672461646720983437)
      ·
        refine ⟨240957775752173117520368789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642554068672461646720983437 240957775752173117520368789)
        ·
          refine ⟨11294895738383114883767287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240957775752173117520368789 11294895738383114883767287)
          ·
            refine ⟨16942343607574672325650931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294895738383114883767287 16942343607574672325650931)
            ·
              refine ⟨25413515411362008488476397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16942343607574672325650931 25413515411362008488476397)
              ·
                refine ⟨9530068279260753183178649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25413515411362008488476397 9530068279260753183178649)
                ·
                  refine ⟨7147551209445564887383987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530068279260753183178649 7147551209445564887383987)
                  ·
                    refine ⟨10721326814168347331075981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147551209445564887383987 10721326814168347331075981)
                    ·
                      refine ⟨4020497555313130249153493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721326814168347331075981 4020497555313130249153493)
                      ·
                        rfl

theorem cell23_7829891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_7829891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829891 prefixEnd_7829891 := by exact prefixLift 7829891
  have htrace : WordTrace (prefixWord ++ tailWord_7829891) baseStart_7829891 baseEnd_7829891 := by
    simpa [prefixWord, tailWord_7829891, baseEnd_7829891] using wordTrace_append hprefix tailTrace_7829891
  have hstable : (prefixWord ++ tailWord_7829891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829891).length < 2 ^ (prefixWord ++ tailWord_7829891).sum := by decide
  have hdescent : baseEnd_7829891 < baseStart_7829891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829914 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7829914 : Nat := 118140960795 + 7829914 * 2 ^ 59
def prefixEnd_7829914 : Nat := 4983230072969 + 3 ^ 40 * 7829914 * 2
def baseEnd_7829914 : Nat := 4020509365368183659165887

theorem tailTrace_7829914 : CollatzResearch.WordTrace tailWord_7829914 prefixEnd_7829914 4020509365368183659165887 := by
  unfold tailWord_7829914
  simp only [CollatzResearch.WordTrace]
  refine ⟨71395106238891573923242199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190386949970377530461979197 71395106238891573923242199)
  ·
    refine ⟨107092659358337360884863299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71395106238891573923242199 107092659358337360884863299)
    ·
      refine ⟨160638989037506041327294949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107092659358337360884863299 160638989037506041327294949)
      ·
        refine ⟨30119810444532382748867803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160638989037506041327294949 30119810444532382748867803)
        ·
          refine ⟨45179715666798574123301705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30119810444532382748867803 45179715666798574123301705)
          ·
            refine ⟨33884786750098930592476279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45179715666798574123301705 33884786750098930592476279)
            ·
              refine ⟨50827180125148395888714419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33884786750098930592476279 50827180125148395888714419)
              ·
                refine ⟨76240770187722593833071629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50827180125148395888714419 76240770187722593833071629)
                ·
                  refine ⟨28590288820395972687401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76240770187722593833071629 28590288820395972687401861)
                  ·
                    refine ⟨5360679153824244878887849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28590288820395972687401861 5360679153824244878887849)
                    ·
                      refine ⟨4020509365368183659165887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360679153824244878887849 4020509365368183659165887)
                      ·
                        rfl

theorem cell23_7829914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7829914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829914 prefixEnd_7829914 := by exact prefixLift 7829914
  have htrace : WordTrace (prefixWord ++ tailWord_7829914) baseStart_7829914 baseEnd_7829914 := by
    simpa [prefixWord, tailWord_7829914, baseEnd_7829914] using wordTrace_append hprefix tailTrace_7829914
  have hstable : (prefixWord ++ tailWord_7829914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829914).length < 2 ^ (prefixWord ++ tailWord_7829914).sum := by decide
  have hdescent : baseEnd_7829914 < baseStart_7829914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7829948 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7829948 : Nat := 118140960795 + 7829948 * 2 ^ 59
def prefixEnd_7829948 : Nat := 4983230072969 + 3 ^ 40 * 7829948 * 2
def baseEnd_7829948 : Nat := 4020526823710436526140731

theorem tailTrace_7829948 : CollatzResearch.WordTrace tailWord_7829948 prefixEnd_7829948 4020526823710436526140731 := by
  unfold tailWord_7829948
  simp only [CollatzResearch.WordTrace]
  refine ⟨142790832518721559749853249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190387776691628746333137665 142790832518721559749853249)
  ·
    refine ⟨107093124389041169812389937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142790832518721559749853249 107093124389041169812389937)
    ·
      refine ⟨80319843291780877359292453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107093124389041169812389937 80319843291780877359292453)
      ·
        refine ⟨15059970617208914504867335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80319843291780877359292453 15059970617208914504867335)
        ·
          refine ⟨22589955925813371757301003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059970617208914504867335 22589955925813371757301003)
          ·
            refine ⟨33884933888720057635951505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22589955925813371757301003 33884933888720057635951505)
            ·
              refine ⟨25413700416540043226963629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33884933888720057635951505 25413700416540043226963629)
              ·
                refine ⟨9530137656202516210111361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25413700416540043226963629 9530137656202516210111361)
                ·
                  refine ⟨7147603242151887157583521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530137656202516210111361 7147603242151887157583521)
                  ·
                    refine ⟨5360702431613915368187641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147603242151887157583521 5360702431613915368187641)
                    ·
                      refine ⟨4020526823710436526140731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360702431613915368187641 4020526823710436526140731)
                      ·
                        rfl

theorem cell23_7829948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7829948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7829948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7829948 prefixEnd_7829948 := by exact prefixLift 7829948
  have htrace : WordTrace (prefixWord ++ tailWord_7829948) baseStart_7829948 baseEnd_7829948 := by
    simpa [prefixWord, tailWord_7829948, baseEnd_7829948] using wordTrace_append hprefix tailTrace_7829948
  have hstable : (prefixWord ++ tailWord_7829948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7829948).length < 2 ^ (prefixWord ++ tailWord_7829948).sum := by decide
  have hdescent : baseEnd_7829948 < baseStart_7829948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7829948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830022 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7830022 : Nat := 118140960795 + 7830022 * 2 ^ 59
def prefixEnd_7830022 : Nat := 4983230072969 + 3 ^ 40 * 7830022 * 2
def baseEnd_7830022 : Nat := 446729424586541026290599

theorem tailTrace_7830022 : CollatzResearch.WordTrace tailWord_7830022 prefixEnd_7830022 446729424586541026290599 := by
  unfold tailWord_7830022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924511376224219691809385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190389576026116686758600213 8924511376224219691809385)
  ·
    refine ⟨6693383532168164768857039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8924511376224219691809385 6693383532168164768857039)
    ·
      refine ⟨10040075298252247153285559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693383532168164768857039 10040075298252247153285559)
      ·
        refine ⟨15060112947378370729928339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040075298252247153285559 15060112947378370729928339)
        ·
          refine ⟨22590169421067556094892509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15060112947378370729928339 22590169421067556094892509)
          ·
            refine ⟨8471313532900333535584691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22590169421067556094892509 8471313532900333535584691)
            ·
              refine ⟨12706970299350500303377037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471313532900333535584691 12706970299350500303377037)
              ·
                refine ⟨4765113862256437613766389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706970299350500303377037 4765113862256437613766389)
                ·
                  refine ⟨446729424586541026290599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4765113862256437613766389 446729424586541026290599)
                  ·
                    rfl

theorem cell23_7830022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7830022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830022 prefixEnd_7830022 := by exact prefixLift 7830022
  have htrace : WordTrace (prefixWord ++ tailWord_7830022) baseStart_7830022 baseEnd_7830022 := by
    simpa [prefixWord, tailWord_7830022, baseEnd_7830022] using wordTrace_append hprefix tailTrace_7830022
  have hstable : (prefixWord ++ tailWord_7830022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830022).length < 2 ^ (prefixWord ++ tailWord_7830022).sum := by decide
  have hdescent : baseEnd_7830022 < baseStart_7830022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830024 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_7830024 : Nat := 118140960795 + 7830024 * 2 ^ 59
def prefixEnd_7830024 : Nat := 4983230072969 + 3 ^ 40 * 7830024 * 2
def baseEnd_7830024 : Nat := 4020565848240178228790381

theorem tailTrace_7830024 : CollatzResearch.WordTrace tailWord_7830024 prefixEnd_7830024 4020565848240178228790381 := by
  unfold tailWord_7830024
  simp only [CollatzResearch.WordTrace]
  refine ⟨142792218492583892239736563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190389624656778522986315417 142792218492583892239736563)
  ·
    refine ⟨214188327738875838359604845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142792218492583892239736563 214188327738875838359604845)
    ·
      refine ⟨80320622902078439384851817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214188327738875838359604845 80320622902078439384851817)
      ·
        refine ⟨60240467176558829538638863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80320622902078439384851817 60240467176558829538638863)
        ·
          refine ⟨90360700764838244307958295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60240467176558829538638863 90360700764838244307958295)
          ·
            refine ⟨135541051147257366461937443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90360700764838244307958295 135541051147257366461937443)
            ·
              refine ⟨203311576720886049692906165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135541051147257366461937443 203311576720886049692906165)
              ·
                refine ⟨19060460317583067158709953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203311576720886049692906165 19060460317583067158709953)
                ·
                  refine ⟨14295345238187300369032465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19060460317583067158709953 14295345238187300369032465)
                  ·
                    refine ⟨10721508928640475276774349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14295345238187300369032465 10721508928640475276774349)
                    ·
                      refine ⟨4020565848240178228790381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721508928640475276774349 4020565848240178228790381)
                      ·
                        rfl

theorem cell23_7830024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_7830024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830024 prefixEnd_7830024 := by exact prefixLift 7830024
  have htrace : WordTrace (prefixWord ++ tailWord_7830024) baseStart_7830024 baseEnd_7830024 := by
    simpa [prefixWord, tailWord_7830024, baseEnd_7830024] using wordTrace_append hprefix tailTrace_7830024
  have hstable : (prefixWord ++ tailWord_7830024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830024).length < 2 ^ (prefixWord ++ tailWord_7830024).sum := by decide
  have hdescent : baseEnd_7830024 < baseStart_7830024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830027 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 8]
def baseStart_7830027 : Nat := 118140960795 + 7830027 * 2 ^ 59
def prefixEnd_7830027 : Nat := 4983230072969 + 3 ^ 40 * 7830027 * 2
def baseEnd_7830027 : Nat := 446729709853571301894763

theorem tailTrace_7830027 : CollatzResearch.WordTrace tailWord_7830027 prefixEnd_7830027 446729709853571301894763 := by
  unfold tailWord_7830027
  simp only [CollatzResearch.WordTrace]
  refine ⟨285584546404156915991832335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190389697602771277327888223 285584546404156915991832335)
  ·
    refine ⟨428376819606235373987748503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285584546404156915991832335 428376819606235373987748503)
    ·
      refine ⟨642565229409353060981622755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428376819606235373987748503 642565229409353060981622755)
      ·
        refine ⟨963847844114029591472434133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642565229409353060981622755 963847844114029591472434133)
        ·
          refine ⟨22590183846422568550135175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 963847844114029591472434133 22590183846422568550135175)
          ·
            refine ⟨33885275769633852825202763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22590183846422568550135175 33885275769633852825202763)
            ·
              refine ⟨50827913654450779237804145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33885275769633852825202763 50827913654450779237804145)
              ·
                refine ⟨38120935240838084428353109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50827913654450779237804145 38120935240838084428353109)
                ·
                  refine ⟨446729709853571301894763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38120935240838084428353109 446729709853571301894763)
                  ·
                    rfl

theorem cell23_7830027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 8].length) (baseStart_7830027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830027 prefixEnd_7830027 := by exact prefixLift 7830027
  have htrace : WordTrace (prefixWord ++ tailWord_7830027) baseStart_7830027 baseEnd_7830027 := by
    simpa [prefixWord, tailWord_7830027, baseEnd_7830027] using wordTrace_append hprefix tailTrace_7830027
  have hstable : (prefixWord ++ tailWord_7830027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830027).length < 2 ^ (prefixWord ++ tailWord_7830027).sum := by decide
  have hdescent : baseEnd_7830027 < baseStart_7830027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830048 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_7830048 : Nat := 118140960795 + 7830048 * 2 ^ 59
def prefixEnd_7830048 : Nat := 4983230072969 + 3 ^ 40 * 7830048 * 2
def baseEnd_7830048 : Nat := 1340192723925295378296757

theorem tailTrace_7830048 : CollatzResearch.WordTrace tailWord_7830048 prefixEnd_7830048 1340192723925295378296757 := by
  unfold tailWord_7830048
  simp only [CollatzResearch.WordTrace]
  refine ⟨142792656168540418289173399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190390208224720557718897865 142792656168540418289173399)
  ·
    refine ⟨214188984252810627433760099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142792656168540418289173399 214188984252810627433760099)
    ·
      refine ⟨321283476379215941150640149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214188984252810627433760099 321283476379215941150640149)
      ·
        refine ⟨15060162955275747241436257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321283476379215941150640149 15060162955275747241436257)
        ·
          refine ⟨11295122216456810431077193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15060162955275747241436257 11295122216456810431077193)
          ·
            refine ⟨8471341662342607823307895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11295122216456810431077193 8471341662342607823307895)
            ·
              refine ⟨12707012493513911734961843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471341662342607823307895 12707012493513911734961843)
              ·
                refine ⟨19060518740270867602442765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707012493513911734961843 19060518740270867602442765)
                ·
                  refine ⟨7147694527601575350916037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19060518740270867602442765 7147694527601575350916037)
                  ·
                    refine ⟨1340192723925295378296757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147694527601575350916037 1340192723925295378296757)
                    ·
                      rfl

theorem cell23_7830048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_7830048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830048 prefixEnd_7830048 := by exact prefixLift 7830048
  have htrace : WordTrace (prefixWord ++ tailWord_7830048) baseStart_7830048 baseEnd_7830048 := by
    simpa [prefixWord, tailWord_7830048, baseEnd_7830048] using wordTrace_append hprefix tailTrace_7830048
  have hstable : (prefixWord ++ tailWord_7830048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830048).length < 2 ^ (prefixWord ++ tailWord_7830048).sum := by decide
  have hdescent : baseEnd_7830048 < baseStart_7830048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830064 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2]
def baseStart_7830064 : Nat := 118140960795 + 7830064 * 2 ^ 59
def prefixEnd_7830064 : Nat := 4983230072969 + 3 ^ 40 * 7830064 * 2
def baseEnd_7830064 : Nat := 4020586387466358072290197

theorem tailTrace_7830064 : CollatzResearch.WordTrace tailWord_7830064 prefixEnd_7830064 4020586387466358072290197 := by
  unfold tailWord_7830064
  simp only [CollatzResearch.WordTrace]
  refine ⟨142792947952511435655464623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190390597270015247540619497 142792947952511435655464623)
  ·
    refine ⟨214189421928767153483196935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142792947952511435655464623 214189421928767153483196935)
    ·
      refine ⟨321284132893150730224795403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214189421928767153483196935 321284132893150730224795403)
      ·
        refine ⟨481926199339726095337193105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321284132893150730224795403 481926199339726095337193105)
        ·
          refine ⟨361444649504794571502894829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481926199339726095337193105 361444649504794571502894829)
          ·
            refine ⟨135541743564297964313585561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361444649504794571502894829 135541743564297964313585561)
            ·
              refine ⟨101656307673223473235189171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135541743564297964313585561 101656307673223473235189171)
              ·
                refine ⟨152484461509835209852783757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101656307673223473235189171 152484461509835209852783757)
                ·
                  refine ⟨57181673066188203694793909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152484461509835209852783757 57181673066188203694793909)
                  ·
                    refine ⟨5360781849955144096386929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57181673066188203694793909 5360781849955144096386929)
                    ·
                      refine ⟨4020586387466358072290197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360781849955144096386929 4020586387466358072290197)
                      ·
                        rfl

theorem cell23_7830064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2].length) (baseStart_7830064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830064 prefixEnd_7830064 := by exact prefixLift 7830064
  have htrace : WordTrace (prefixWord ++ tailWord_7830064) baseStart_7830064 baseEnd_7830064 := by
    simpa [prefixWord, tailWord_7830064, baseEnd_7830064] using wordTrace_append hprefix tailTrace_7830064
  have hstable : (prefixWord ++ tailWord_7830064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830064).length < 2 ^ (prefixWord ++ tailWord_7830064).sum := by decide
  have hdescent : baseEnd_7830064 < baseStart_7830064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830074 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_7830074 : Nat := 118140960795 + 7830074 * 2 ^ 59
def prefixEnd_7830074 : Nat := 4983230072969 + 3 ^ 40 * 7830074 * 2
def baseEnd_7830074 : Nat := 1340197174090967677721717

theorem tailTrace_7830074 : CollatzResearch.WordTrace tailWord_7830074 prefixEnd_7830074 1340197174090967677721717 := by
  unfold tailWord_7830074
  simp only [CollatzResearch.WordTrace]
  refine ⟨71396565158746660754698319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190390840423324428679195517 71396565158746660754698319)
  ·
    refine ⟨107094847738119991132047479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71396565158746660754698319 107094847738119991132047479)
    ·
      refine ⟨160642271607179986698071219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107094847738119991132047479 160642271607179986698071219)
      ·
        refine ⟨240963407410769980047106829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160642271607179986698071219 240963407410769980047106829)
        ·
          refine ⟨90361277779038742517665061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240963407410769980047106829 90361277779038742517665061)
          ·
            refine ⟨16942739583569764222062199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90361277779038742517665061 16942739583569764222062199)
            ·
              refine ⟨25414109375354646333093299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16942739583569764222062199 25414109375354646333093299)
              ·
                refine ⟨38121164063031969499639949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25414109375354646333093299 38121164063031969499639949)
                ·
                  refine ⟨14295436523636988562364981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38121164063031969499639949 14295436523636988562364981)
                  ·
                    refine ⟨1340197174090967677721717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14295436523636988562364981 1340197174090967677721717)
                    ·
                      rfl

theorem cell23_7830074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_7830074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830074 prefixEnd_7830074 := by exact prefixLift 7830074
  have htrace : WordTrace (prefixWord ++ tailWord_7830074) baseStart_7830074 baseEnd_7830074 := by
    simpa [prefixWord, tailWord_7830074, baseEnd_7830074] using wordTrace_append hprefix tailTrace_7830074
  have hstable : (prefixWord ++ tailWord_7830074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830074).length < 2 ^ (prefixWord ++ tailWord_7830074).sum := by decide
  have hdescent : baseEnd_7830074 < baseStart_7830074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830104 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_7830104 : Nat := 118140960795 + 7830104 * 2 ^ 59
def prefixEnd_7830104 : Nat := 4983230072969 + 3 ^ 40 * 7830104 * 2
def baseEnd_7830104 : Nat := 1340202308897512638596671

theorem tailTrace_7830104 : CollatzResearch.WordTrace tailWord_7830104 prefixEnd_7830104 1340202308897512638596671 := by
  unfold tailWord_7830104
  simp only [CollatzResearch.WordTrace]
  refine ⟨142793677412438979071192683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190391569883251972094923577 142793677412438979071192683)
  ·
    refine ⟨214190516118658468606789025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142793677412438979071192683 214190516118658468606789025)
    ·
      refine ⟨160642887088993851455091769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214190516118658468606789025 160642887088993851455091769)
      ·
        refine ⟨120482165316745388591318827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160642887088993851455091769 120482165316745388591318827)
        ·
          refine ⟨180723247975118082886978241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120482165316745388591318827 180723247975118082886978241)
          ·
            refine ⟨135542435981338562165233681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180723247975118082886978241 135542435981338562165233681)
            ·
              refine ⟨101656826986003921623925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135542435981338562165233681 101656826986003921623925261)
              ·
                refine ⟨38121310119751470608971973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101656826986003921623925261 38121310119751470608971973)
                ·
                  refine ⟨7147745647453400739182245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38121310119751470608971973 7147745647453400739182245)
                  ·
                    refine ⟨1340202308897512638596671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147745647453400739182245 1340202308897512638596671)
                    ·
                      rfl

theorem cell23_7830104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_7830104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830104 prefixEnd_7830104 := by exact prefixLift 7830104
  have htrace : WordTrace (prefixWord ++ tailWord_7830104) baseStart_7830104 baseEnd_7830104 := by
    simpa [prefixWord, tailWord_7830104, baseEnd_7830104] using wordTrace_append hprefix tailTrace_7830104
  have hstable : (prefixWord ++ tailWord_7830104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830104).length < 2 ^ (prefixWord ++ tailWord_7830104).sum := by decide
  have hdescent : baseEnd_7830104 < baseStart_7830104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830111 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 7, 2, 2]
def baseStart_7830111 : Nat := 118140960795 + 7830111 * 2 ^ 59
def prefixEnd_7830111 : Nat := 4983230072969 + 3 ^ 40 * 7830111 * 2
def baseEnd_7830111 : Nat := 4020610521057119388402481

theorem tailTrace_7830111 : CollatzResearch.WordTrace tailWord_7830111 prefixEnd_7830111 4020610521057119388402481 := by
  unfold tailWord_7830111
  simp only [CollatzResearch.WordTrace]
  refine ⟨285587610135852598337890187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190391740090568398891926791 285587610135852598337890187)
  ·
    refine ⟨428381415203778897506835281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285587610135852598337890187 428381415203778897506835281)
    ·
      refine ⟨321286061402834173130126461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428381415203778897506835281 321286061402834173130126461)
      ·
        refine ⟨120482273026062814923797423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321286061402834173130126461 120482273026062814923797423)
        ·
          refine ⟨180723409539094222385696135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120482273026062814923797423 180723409539094222385696135)
          ·
            refine ⟨271085114308641333578544203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180723409539094222385696135 271085114308641333578544203)
            ·
              refine ⟨406627671462962000367816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271085114308641333578544203 406627671462962000367816305)
              ·
                refine ⟨304970753597221500275862229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406627671462962000367816305 304970753597221500275862229)
                ·
                  refine ⟨7147752037434878912715521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304970753597221500275862229 7147752037434878912715521)
                  ·
                    refine ⟨5360814028076159184536641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147752037434878912715521 5360814028076159184536641)
                    ·
                      refine ⟨4020610521057119388402481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360814028076159184536641 4020610521057119388402481)
                      ·
                        rfl

theorem cell23_7830111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_7830111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830111 prefixEnd_7830111 := by exact prefixLift 7830111
  have htrace : WordTrace (prefixWord ++ tailWord_7830111) baseStart_7830111 baseEnd_7830111 := by
    simpa [prefixWord, tailWord_7830111, baseEnd_7830111] using wordTrace_append hprefix tailTrace_7830111
  have hstable : (prefixWord ++ tailWord_7830111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830111).length < 2 ^ (prefixWord ++ tailWord_7830111).sum := by decide
  have hdescent : baseEnd_7830111 < baseStart_7830111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830124 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_7830124 : Nat := 118140960795 + 7830124 * 2 ^ 59
def prefixEnd_7830124 : Nat := 4983230072969 + 3 ^ 40 * 7830124 * 2
def baseEnd_7830124 : Nat := 4020617196305627837539921

theorem tailTrace_7830124 : CollatzResearch.WordTrace tailWord_7830124 prefixEnd_7830124 4020617196305627837539921 := by
  unfold tailWord_7830124
  simp only [CollatzResearch.WordTrace]
  refine ⟨142794042142402750779056713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190392056189870334372075617 142794042142402750779056713)
  ·
    refine ⟨107095531606802063084292535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142794042142402750779056713 107095531606802063084292535)
    ·
      refine ⟨160643297410203094626438803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107095531606802063084292535 160643297410203094626438803)
      ·
        refine ⟨240964946115304641939658205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160643297410203094626438803 240964946115304641939658205)
        ·
          refine ⟨90361854793239240727371827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240964946115304641939658205 90361854793239240727371827)
          ·
            refine ⟨135542782189858861091057741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90361854793239240727371827 135542782189858861091057741)
            ·
              refine ⟨50828543321197072909146653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135542782189858861091057741 50828543321197072909146653)
              ·
                refine ⟨19060703745448902340929995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50828543321197072909146653 19060703745448902340929995)
                ·
                  refine ⟨28591055618173353511394993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19060703745448902340929995 28591055618173353511394993)
                  ·
                    refine ⟨21443291713630015133546245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28591055618173353511394993 21443291713630015133546245)
                    ·
                      refine ⟨4020617196305627837539921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21443291713630015133546245 4020617196305627837539921)
                      ·
                        rfl

theorem cell23_7830124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_7830124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830124 prefixEnd_7830124 := by exact prefixLift 7830124
  have htrace : WordTrace (prefixWord ++ tailWord_7830124) baseStart_7830124 baseEnd_7830124 := by
    simpa [prefixWord, tailWord_7830124, baseEnd_7830124] using wordTrace_append hprefix tailTrace_7830124
  have hstable : (prefixWord ++ tailWord_7830124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830124).length < 2 ^ (prefixWord ++ tailWord_7830124).sum := by decide
  have hdescent : baseEnd_7830124 < baseStart_7830124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830148 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7830148 : Nat := 118140960795 + 7830148 * 2 ^ 59
def prefixEnd_7830148 : Nat := 4983230072969 + 3 ^ 40 * 7830148 * 2
def baseEnd_7830148 : Nat := 4020629519841335743639811

theorem tailTrace_7830148 : CollatzResearch.WordTrace tailWord_7830148 prefixEnd_7830148 4020629519841335743639811 := by
  unfold tailWord_7830148
  simp only [CollatzResearch.WordTrace]
  refine ⟨142794479818359276828493549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190392639757812369104658065 142794479818359276828493549)
  ·
    refine ⟨53547929931884728810685081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142794479818359276828493549 53547929931884728810685081)
    ·
      refine ⟨40160947448913546608013811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53547929931884728810685081 40160947448913546608013811)
      ·
        refine ⟨60241421173370319912020717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40160947448913546608013811 60241421173370319912020717)
        ·
          refine ⟨22590532940013869967007769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60241421173370319912020717 22590532940013869967007769)
          ·
            refine ⟨16942899705010402475255827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22590532940013869967007769 16942899705010402475255827)
            ·
              refine ⟨25414349557515603712883741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16942899705010402475255827 25414349557515603712883741)
              ·
                refine ⟨9530381084068351392331403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25414349557515603712883741 9530381084068351392331403)
                ·
                  refine ⟨14295571626102527088497105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9530381084068351392331403 14295571626102527088497105)
                  ·
                    refine ⟨10721678719576895316372829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14295571626102527088497105 10721678719576895316372829)
                    ·
                      refine ⟨4020629519841335743639811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721678719576895316372829 4020629519841335743639811)
                      ·
                        rfl

theorem cell23_7830148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7830148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830148 prefixEnd_7830148 := by exact prefixLift 7830148
  have htrace : WordTrace (prefixWord ++ tailWord_7830148) baseStart_7830148 baseEnd_7830148 := by
    simpa [prefixWord, tailWord_7830148, baseEnd_7830148] using wordTrace_append hprefix tailTrace_7830148
  have hstable : (prefixWord ++ tailWord_7830148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830148).length < 2 ^ (prefixWord ++ tailWord_7830148).sum := by decide
  have hdescent : baseEnd_7830148 < baseStart_7830148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830162 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7830162 : Nat := 118140960795 + 7830162 * 2 ^ 59
def prefixEnd_7830162 : Nat := 4983230072969 + 3 ^ 40 * 7830162 * 2
def baseEnd_7830162 : Nat := 4020636708570498688864747

theorem tailTrace_7830162 : CollatzResearch.WordTrace tailWord_7830162 prefixEnd_7830162 4020636708570498688864747 := by
  unfold tailWord_7830162
  simp only [CollatzResearch.WordTrace]
  refine ⟨71397367564666958511999185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190392980172445222698664493 71397367564666958511999185)
  ·
    refine ⟨53548025673500218883999389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71397367564666958511999185 53548025673500218883999389)
    ·
      refine ⟨20080509627562582081499771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53548025673500218883999389 20080509627562582081499771)
      ·
        refine ⟨30120764441343873122249657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20080509627562582081499771 30120764441343873122249657)
        ·
          refine ⟨22590573331007904841687243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30120764441343873122249657 22590573331007904841687243)
          ·
            refine ⟨33885859996511857262530865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22590573331007904841687243 33885859996511857262530865)
            ·
              refine ⟨25414394997383892946898149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33885859996511857262530865 25414394997383892946898149)
              ·
                refine ⟨4765199062009479927543403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25414394997383892946898149 4765199062009479927543403)
                ·
                  refine ⟨7147798593014219891315105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765199062009479927543403 7147798593014219891315105)
                  ·
                    refine ⟨5360848944760664918486329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147798593014219891315105 5360848944760664918486329)
                    ·
                      refine ⟨4020636708570498688864747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360848944760664918486329 4020636708570498688864747)
                      ·
                        rfl

theorem cell23_7830162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7830162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830162 prefixEnd_7830162 := by exact prefixLift 7830162
  have htrace : WordTrace (prefixWord ++ tailWord_7830162) baseStart_7830162 baseEnd_7830162 := by
    simpa [prefixWord, tailWord_7830162, baseEnd_7830162] using wordTrace_append hprefix tailTrace_7830162
  have hstable : (prefixWord ++ tailWord_7830162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830162).length < 2 ^ (prefixWord ++ tailWord_7830162).sum := by decide
  have hdescent : baseEnd_7830162 < baseStart_7830162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830201 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7830201 : Nat := 118140960795 + 7830201 * 2 ^ 59
def prefixEnd_7830201 : Nat := 4983230072969 + 3 ^ 40 * 7830201 * 2
def baseEnd_7830201 : Nat := 4020656734316024036277067

theorem tailTrace_7830201 : CollatzResearch.WordTrace tailWord_7830201 prefixEnd_7830201 4020656734316024036277067 := by
  unfold tailWord_7830201
  simp only [CollatzResearch.WordTrace]
  refine ⟨285590892705526543708666457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190393928470351029139110971 285590892705526543708666457)
  ·
    refine ⟨214193169529144907781499843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285590892705526543708666457 214193169529144907781499843)
    ·
      refine ⟨321289754293717361672249765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214193169529144907781499843 321289754293717361672249765)
      ·
        refine ⟨60241828930072005313546831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321289754293717361672249765 60241828930072005313546831)
        ·
          refine ⟨90362743395108007970320247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60241828930072005313546831 90362743395108007970320247)
          ·
            refine ⟨135544115092662011955480371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90362743395108007970320247 135544115092662011955480371)
            ·
              refine ⟨203316172638993017933220557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135544115092662011955480371 203316172638993017933220557)
              ·
                refine ⟨76243564739622381724957709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203316172638993017933220557 76243564739622381724957709)
                ·
                  refine ⟨28591336777358393146859141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76243564739622381724957709 28591336777358393146859141)
                  ·
                    refine ⟨5360875645754698715036089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28591336777358393146859141 5360875645754698715036089)
                    ·
                      refine ⟨4020656734316024036277067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360875645754698715036089 4020656734316024036277067)
                      ·
                        rfl

theorem cell23_7830201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7830201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830201 prefixEnd_7830201 := by exact prefixLift 7830201
  have htrace : WordTrace (prefixWord ++ tailWord_7830201) baseStart_7830201 baseEnd_7830201 := by
    simpa [prefixWord, tailWord_7830201, baseEnd_7830201] using wordTrace_append hprefix tailTrace_7830201
  have hstable : (prefixWord ++ tailWord_7830201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830201).length < 2 ^ (prefixWord ++ tailWord_7830201).sum := by decide
  have hdescent : baseEnd_7830201 < baseStart_7830201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830229 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7830229 : Nat := 118140960795 + 7830229 * 2 ^ 59
def prefixEnd_7830229 : Nat := 4983230072969 + 3 ^ 40 * 7830229 * 2
def baseEnd_7830229 : Nat := 4020671111774349926726939

theorem tailTrace_7830229 : CollatzResearch.WordTrace tailWord_7830229 prefixEnd_7830229 4020671111774349926726939 := by
  unfold tailWord_7830229
  simp only [CollatzResearch.WordTrace]
  refine ⟨285591913949425104490685741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190394609299616736327123827 285591913949425104490685741)
  ·
    refine ⟨107096967731034414184007153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285591913949425104490685741 107096967731034414184007153)
    ·
      refine ⟨80322725798275810638005365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107096967731034414184007153 80322725798275810638005365)
      ·
        refine ⟨7530255543588357247313003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80322725798275810638005365 7530255543588357247313003)
        ·
          refine ⟨11295383315382535870969505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530255543588357247313003 11295383315382535870969505)
          ·
            refine ⟨8471537486536901903227129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11295383315382535870969505 8471537486536901903227129)
            ·
              refine ⟨6353653114902676427420347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8471537486536901903227129 6353653114902676427420347)
              ·
                refine ⟨9530479672354014641130521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353653114902676427420347 9530479672354014641130521)
                ·
                  refine ⟨7147859754265510980847891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530479672354014641130521 7147859754265510980847891)
                  ·
                    refine ⟨10721789631398266471271837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7147859754265510980847891 10721789631398266471271837)
                    ·
                      refine ⟨4020671111774349926726939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10721789631398266471271837 4020671111774349926726939)
                      ·
                        rfl

theorem cell23_7830229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7830229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830229 prefixEnd_7830229 := by exact prefixLift 7830229
  have htrace : WordTrace (prefixWord ++ tailWord_7830229) baseStart_7830229 baseEnd_7830229 := by
    simpa [prefixWord, tailWord_7830229, baseEnd_7830229] using wordTrace_append hprefix tailTrace_7830229
  have hstable : (prefixWord ++ tailWord_7830229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830229).length < 2 ^ (prefixWord ++ tailWord_7830229).sum := by decide
  have hdescent : baseEnd_7830229 < baseStart_7830229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830264 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_7830264 : Nat := 118140960795 + 7830264 * 2 ^ 59
def prefixEnd_7830264 : Nat := 4983230072969 + 3 ^ 40 * 7830264 * 2
def baseEnd_7830264 : Nat := 4020689083597257289789277

theorem tailTrace_7830264 : CollatzResearch.WordTrace tailWord_7830264 prefixEnd_7830264 4020689083597257289789277 := by
  unfold tailWord_7830264
  simp only [CollatzResearch.WordTrace]
  refine ⟨142796595252149152734104923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190395460336198870312139897 142796595252149152734104923)
  ·
    refine ⟨214194892878223729101157385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142796595252149152734104923 214194892878223729101157385)
    ·
      refine ⟨160646169658667796825868039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214194892878223729101157385 160646169658667796825868039)
      ·
        refine ⟨240969254488001695238802059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160646169658667796825868039 240969254488001695238802059)
        ·
          refine ⟨361453881732002542858203089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240969254488001695238802059 361453881732002542858203089)
          ·
            refine ⟨271090411299001907143652317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361453881732002542858203089 271090411299001907143652317)
            ·
              refine ⟨101658904237125715178869619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271090411299001907143652317 101658904237125715178869619)
              ·
                refine ⟨152488356355688572768304429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101658904237125715178869619 152488356355688572768304429)
                ·
                  refine ⟨57183133633383214788114161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152488356355688572768304429 57183133633383214788114161)
                  ·
                    refine ⟨42887350225037411091085621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57183133633383214788114161 42887350225037411091085621)
                    ·
                      refine ⟨4020689083597257289789277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42887350225037411091085621 4020689083597257289789277)
                      ·
                        rfl

theorem cell23_7830264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_7830264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830264 prefixEnd_7830264 := by exact prefixLift 7830264
  have htrace : WordTrace (prefixWord ++ tailWord_7830264) baseStart_7830264 baseEnd_7830264 := by
    simpa [prefixWord, tailWord_7830264, baseEnd_7830264] using wordTrace_append hprefix tailTrace_7830264
  have hstable : (prefixWord ++ tailWord_7830264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830264).length < 2 ^ (prefixWord ++ tailWord_7830264).sum := by decide
  have hdescent : baseEnd_7830264 < baseStart_7830264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830284 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_7830284 : Nat := 118140960795 + 7830284 * 2 ^ 59
def prefixEnd_7830284 : Nat := 4983230072969 + 3 ^ 40 * 7830284 * 2
def baseEnd_7830284 : Nat := 1340233117736782403846395

theorem tailTrace_7830284 : CollatzResearch.WordTrace tailWord_7830284 prefixEnd_7830284 1340233117736782403846395 := by
  unfold tailWord_7830284
  simp only [CollatzResearch.WordTrace]
  refine ⟨142796959982112924441968953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190395946642817232589291937 142796959982112924441968953)
  ·
    refine ⟨107097719986584693331476715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142796959982112924441968953 107097719986584693331476715)
    ·
      refine ⟨160646579979877039997215073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107097719986584693331476715 160646579979877039997215073)
      ·
        refine ⟨120484934984907779997911305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160646579979877039997215073 120484934984907779997911305)
        ·
          refine ⟨90363701238680834998433479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120484934984907779997911305 90363701238680834998433479)
          ·
            refine ⟨135545551858021252497650219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90363701238680834998433479 135545551858021252497650219)
            ·
              refine ⟨203318327787031878746475329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135545551858021252497650219 203318327787031878746475329)
              ·
                refine ⟨152488745840273909059856497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203318327787031878746475329 152488745840273909059856497)
                ·
                  refine ⟨114366559380205431794892373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152488745840273909059856497 114366559380205431794892373)
                  ·
                    refine ⟨1340233117736782403846395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114366559380205431794892373 1340233117736782403846395)
                    ·
                      rfl

theorem cell23_7830284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_7830284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830284 prefixEnd_7830284 := by exact prefixLift 7830284
  have htrace : WordTrace (prefixWord ++ tailWord_7830284) baseStart_7830284 baseEnd_7830284 := by
    simpa [prefixWord, tailWord_7830284, baseEnd_7830284] using wordTrace_append hprefix tailTrace_7830284
  have hstable : (prefixWord ++ tailWord_7830284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830284).length < 2 ^ (prefixWord ++ tailWord_7830284).sum := by decide
  have hdescent : baseEnd_7830284 < baseStart_7830284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830308 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_7830308 : Nat := 118140960795 + 7830308 * 2 ^ 59
def prefixEnd_7830308 : Nat := 4983230072969 + 3 ^ 40 * 7830308 * 2
def baseEnd_7830308 : Nat := 4020711676746055117639075

theorem tailTrace_7830308 : CollatzResearch.WordTrace tailWord_7830308 prefixEnd_7830308 4020711676746055117639075 := by
  unfold tailWord_7830308
  simp only [CollatzResearch.WordTrace]
  refine ⟨142797397658069450491405789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190396530210759267321874385 142797397658069450491405789)
  ·
    refine ⟨53549024121776043934277171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142797397658069450491405789 53549024121776043934277171)
    ·
      refine ⟨80323536182664065901415757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53549024121776043934277171 80323536182664065901415757)
      ·
        refine ⟨30121326068499024713030909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80323536182664065901415757 30121326068499024713030909)
        ·
          refine ⟨11295497275687134267386591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30121326068499024713030909 11295497275687134267386591)
          ·
            refine ⟨16943245913530701401079887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295497275687134267386591 16943245913530701401079887)
            ·
              refine ⟨25414868870296052101619831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943245913530701401079887 25414868870296052101619831)
              ·
                refine ⟨38122303305444078152429747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25414868870296052101619831 38122303305444078152429747)
                ·
                  refine ⟨57183454958166117228644621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38122303305444078152429747 57183454958166117228644621)
                  ·
                    refine ⟨21443795609312293960741733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57183454958166117228644621 21443795609312293960741733)
                    ·
                      refine ⟨4020711676746055117639075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21443795609312293960741733 4020711676746055117639075)
                      ·
                        rfl

theorem cell23_7830308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_7830308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830308 prefixEnd_7830308 := by exact prefixLift 7830308
  have htrace : WordTrace (prefixWord ++ tailWord_7830308) baseStart_7830308 baseEnd_7830308 := by
    simpa [prefixWord, tailWord_7830308, baseEnd_7830308] using wordTrace_append hprefix tailTrace_7830308
  have hstable : (prefixWord ++ tailWord_7830308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830308).length < 2 ^ (prefixWord ++ tailWord_7830308).sum := by decide
  have hdescent : baseEnd_7830308 < baseStart_7830308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830335 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 1, 4]
def baseStart_7830335 : Nat := 118140960795 + 7830335 * 2 ^ 59
def prefixEnd_7830335 : Nat := 4983230072969 + 3 ^ 40 * 7830335 * 2
def baseEnd_7830335 : Nat := 1340241846907908837333817

theorem tailTrace_7830335 : CollatzResearch.WordTrace tailWord_7830335 prefixEnd_7830335 1340241846907908837333817 := by
  unfold tailWord_7830335
  simp only [CollatzResearch.WordTrace]
  refine ⟨285595780087041084594044459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190397186724694056396029639 285595780087041084594044459)
  ·
    refine ⟨428393670130561626891066689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285595780087041084594044459 428393670130561626891066689)
    ·
      refine ⟨321295252597921220168300017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428393670130561626891066689 321295252597921220168300017)
      ·
        refine ⟨240971439448440915126225013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321295252597921220168300017 240971439448440915126225013)
        ·
          refine ⟨22591072448291335793083595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240971439448440915126225013 22591072448291335793083595)
          ·
            refine ⟨33886608672437003689625393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22591072448291335793083595 33886608672437003689625393)
            ·
              refine ⟨25414956504327752767219045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33886608672437003689625393 25414956504327752767219045)
              ·
                refine ⟨4765304344561453643853571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25414956504327752767219045 4765304344561453643853571)
                ·
                  refine ⟨7147956516842180465780357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765304344561453643853571 7147956516842180465780357)
                  ·
                    refine ⟨1340241846907908837333817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147956516842180465780357 1340241846907908837333817)
                    ·
                      rfl

theorem cell23_7830335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_7830335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830335 prefixEnd_7830335 := by exact prefixLift 7830335
  have htrace : WordTrace (prefixWord ++ tailWord_7830335) baseStart_7830335 baseEnd_7830335 := by
    simpa [prefixWord, tailWord_7830335, baseEnd_7830335] using wordTrace_append hprefix tailTrace_7830335
  have hstable : (prefixWord ++ tailWord_7830335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830335).length < 2 ^ (prefixWord ++ tailWord_7830335).sum := by decide
  have hdescent : baseEnd_7830335 < baseStart_7830335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830368 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2]
def baseStart_7830368 : Nat := 118140960795 + 7830368 * 2 ^ 59
def prefixEnd_7830368 : Nat := 4983230072969 + 3 ^ 40 * 7830368 * 2
def baseEnd_7830368 : Nat := 4020742485585324882888799

theorem tailTrace_7830368 : CollatzResearch.WordTrace tailWord_7830368 prefixEnd_7830368 4020742485585324882888799 := by
  unfold tailWord_7830368
  simp only [CollatzResearch.WordTrace]
  refine ⟨142798491847960765614997879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190397989130614354153330505 142798491847960765614997879)
  ·
    refine ⟨214197737771941148422496819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142798491847960765614997879 214197737771941148422496819)
    ·
      refine ⟨321296606657911722633745229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214197737771941148422496819 321296606657911722633745229)
      ·
        refine ⟨120486227496716895987654461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321296606657911722633745229 120486227496716895987654461)
        ·
          refine ⟨45182335311268835995370423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120486227496716895987654461 45182335311268835995370423)
          ·
            refine ⟨67773502966903253993055635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45182335311268835995370423 67773502966903253993055635)
            ·
              refine ⟨101660254450354880989583453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67773502966903253993055635 101660254450354880989583453)
              ·
                refine ⟨38122595418883080371093795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101660254450354880989583453 38122595418883080371093795)
                ·
                  refine ⟨57183893128324620556640693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38122595418883080371093795 57183893128324620556640693)
                  ·
                    refine ⟨5360989980780433177185065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57183893128324620556640693 5360989980780433177185065)
                    ·
                      refine ⟨4020742485585324882888799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5360989980780433177185065 4020742485585324882888799)
                      ·
                        rfl

theorem cell23_7830368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_7830368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830368 prefixEnd_7830368 := by exact prefixLift 7830368
  have htrace : WordTrace (prefixWord ++ tailWord_7830368) baseStart_7830368 baseEnd_7830368 := by
    simpa [prefixWord, tailWord_7830368, baseEnd_7830368] using wordTrace_append hprefix tailTrace_7830368
  have hstable : (prefixWord ++ tailWord_7830368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830368).length < 2 ^ (prefixWord ++ tailWord_7830368).sum := by decide
  have hdescent : baseEnd_7830368 < baseStart_7830368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830385 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_7830385 : Nat := 118140960795 + 7830385 * 2 ^ 59
def prefixEnd_7830385 : Nat := 4983230072969 + 3 ^ 40 * 7830385 * 2
def baseEnd_7830385 : Nat := 4020751214756451316376221

theorem tailTrace_7830385 : CollatzResearch.WordTrace tailWord_7830385 prefixEnd_7830385 4020751214756451316376221 := by
  unfold tailWord_7830385
  simp only [CollatzResearch.WordTrace]
  refine ⟨285597603736859943133364609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190398402491239962088909739 285597603736859943133364609)
  ·
    refine ⟨214198202802644957350023457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285597603736859943133364609 214198202802644957350023457)
    ·
      refine ⟨160648652101983718012517593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214198202802644957350023457 160648652101983718012517593)
      ·
        refine ⟨120486489076487788509388195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160648652101983718012517593 120486489076487788509388195)
        ·
          refine ⟨180729733614731682764082293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120486489076487788509388195 180729733614731682764082293)
          ·
            refine ⟨16943412526381095259132715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180729733614731682764082293 16943412526381095259132715)
            ·
              refine ⟨25415118789571642888699073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943412526381095259132715 25415118789571642888699073)
              ·
                refine ⟨19061339092178732166524305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25415118789571642888699073 19061339092178732166524305)
                ·
                  refine ⟨14296004319134049124893229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19061339092178732166524305 14296004319134049124893229)
                  ·
                    refine ⟨5361001619675268421834961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296004319134049124893229 5361001619675268421834961)
                    ·
                      refine ⟨4020751214756451316376221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361001619675268421834961 4020751214756451316376221)
                      ·
                        rfl

theorem cell23_7830385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_7830385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830385 prefixEnd_7830385 := by exact prefixLift 7830385
  have htrace : WordTrace (prefixWord ++ tailWord_7830385) baseStart_7830385 baseEnd_7830385 := by
    simpa [prefixWord, tailWord_7830385, baseEnd_7830385] using wordTrace_append hprefix tailTrace_7830385
  have hstable : (prefixWord ++ tailWord_7830385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830385).length < 2 ^ (prefixWord ++ tailWord_7830385).sum := by decide
  have hdescent : baseEnd_7830385 < baseStart_7830385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830411 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_7830411 : Nat := 118140960795 + 7830411 * 2 ^ 59
def prefixEnd_7830411 : Nat := 4983230072969 + 3 ^ 40 * 7830411 * 2
def baseEnd_7830411 : Nat := 4020764565253468214651101

theorem tailTrace_7830411 : CollatzResearch.WordTrace tailWord_7830411 prefixEnd_7830411 4020764565253468214651101 := by
  unfold tailWord_7830411
  simp only [CollatzResearch.WordTrace]
  refine ⟨285598552034765749573811087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190399034689843833049207391 285598552034765749573811087)
  ·
    refine ⟨428397828052148624360716631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285598552034765749573811087 428397828052148624360716631)
    ·
      refine ⟨642596742078222936541074947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428397828052148624360716631 642596742078222936541074947)
      ·
        refine ⟨963895113117334404811612421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642596742078222936541074947 963895113117334404811612421)
        ·
          refine ⟨180730333709500200902177329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 963895113117334404811612421 180730333709500200902177329)
          ·
            refine ⟨135547750282125150676632997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180730333709500200902177329 135547750282125150676632997)
            ·
              refine ⟨25415203177898465751868687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135547750282125150676632997 25415203177898465751868687)
              ·
                refine ⟨38122804766847698627803031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25415203177898465751868687 38122804766847698627803031)
                ·
                  refine ⟨57184207150271547941704547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38122804766847698627803031 57184207150271547941704547)
                  ·
                    refine ⟨85776310725407321912556821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57184207150271547941704547 85776310725407321912556821)
                    ·
                      refine ⟨4020764565253468214651101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85776310725407321912556821 4020764565253468214651101)
                      ·
                        rfl

theorem cell23_7830411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_7830411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830411 prefixEnd_7830411 := by exact prefixLift 7830411
  have htrace : WordTrace (prefixWord ++ tailWord_7830411) baseStart_7830411 baseEnd_7830411 := by
    simpa [prefixWord, tailWord_7830411, baseEnd_7830411] using wordTrace_append hprefix tailTrace_7830411
  have hstable : (prefixWord ++ tailWord_7830411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830411).length < 2 ^ (prefixWord ++ tailWord_7830411).sum := by decide
  have hdescent : baseEnd_7830411 < baseStart_7830411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830421 : List Nat := [1, 3, 2, 1, 1, 4, 2, 9]
def baseStart_7830421 : Nat := 118140960795 + 7830421 * 2 ^ 59
def prefixEnd_7830421 : Nat := 4983230072969 + 3 ^ 40 * 7830421 * 2
def baseEnd_7830421 : Nat := 148917396298519006500965

theorem tailTrace_7830421 : CollatzResearch.WordTrace tailWord_7830421 prefixEnd_7830421 148917396298519006500965 := by
  unfold tailWord_7830421
  simp only [CollatzResearch.WordTrace]
  refine ⟨285598916764729521281675117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190399277843153014187783411 285598916764729521281675117)
  ·
    refine ⟨107099593786773570480628169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285598916764729521281675117 107099593786773570480628169)
    ·
      refine ⟨80324695340080177860471127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107099593786773570480628169 80324695340080177860471127)
      ·
        refine ⟨120487043010120266790706691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80324695340080177860471127 120487043010120266790706691)
        ·
          refine ⟨180730564515180400186060037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120487043010120266790706691 180730564515180400186060037)
          ·
            refine ⟨33886980846596325034886257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180730564515180400186060037 33886980846596325034886257)
            ·
              refine ⟨25415235634947243776164693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33886980846596325034886257 25415235634947243776164693)
              ·
                refine ⟨148917396298519006500965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25415235634947243776164693 148917396298519006500965)
                ·
                  rfl

theorem cell23_7830421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 9].length) (baseStart_7830421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830421 prefixEnd_7830421 := by exact prefixLift 7830421
  have htrace : WordTrace (prefixWord ++ tailWord_7830421) baseStart_7830421 baseEnd_7830421 := by
    simpa [prefixWord, tailWord_7830421, baseEnd_7830421] using wordTrace_append hprefix tailTrace_7830421
  have hstable : (prefixWord ++ tailWord_7830421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830421).length < 2 ^ (prefixWord ++ tailWord_7830421).sum := by decide
  have hdescent : baseEnd_7830421 < baseStart_7830421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830452 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7830452 : Nat := 118140960795 + 7830452 * 2 ^ 59
def prefixEnd_7830452 : Nat := 4983230072969 + 3 ^ 40 * 7830452 * 2
def baseEnd_7830452 : Nat := 4020785617960302554238413

theorem tailTrace_7830452 : CollatzResearch.WordTrace tailWord_7830452 prefixEnd_7830452 4020785617960302554238413 := by
  unfold tailWord_7830452
  simp only [CollatzResearch.WordTrace]
  refine ⟨142800023713808606788026805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190400031618411475717369073 142800023713808606788026805)
  ·
    refine ⟨13387502223169556886377513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142800023713808606788026805 13387502223169556886377513)
    ·
      refine ⟨10040626667377167664783135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13387502223169556886377513 10040626667377167664783135)
      ·
        refine ⟨15060940001065751497174703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040626667377167664783135 15060940001065751497174703)
        ·
          refine ⟨22591410001598627245762055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15060940001065751497174703 22591410001598627245762055)
          ·
            refine ⟨33887115002397940868643083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22591410001598627245762055 33887115002397940868643083)
            ·
              refine ⟨50830672503596911302964625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33887115002397940868643083 50830672503596911302964625)
              ·
                refine ⟨38123004377697683477223469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50830672503596911302964625 38123004377697683477223469)
                ·
                  refine ⟨14296126641636631303958801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38123004377697683477223469 14296126641636631303958801)
                  ·
                    refine ⟨10722094981227473477969101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14296126641636631303958801 10722094981227473477969101)
                    ·
                      refine ⟨4020785617960302554238413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722094981227473477969101 4020785617960302554238413)
                      ·
                        rfl

theorem cell23_7830452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7830452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830452 prefixEnd_7830452 := by exact prefixLift 7830452
  have htrace : WordTrace (prefixWord ++ tailWord_7830452) baseStart_7830452 baseEnd_7830452 := by
    simpa [prefixWord, tailWord_7830452, baseEnd_7830452] using wordTrace_append hprefix tailTrace_7830452
  have hstable : (prefixWord ++ tailWord_7830452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830452).length < 2 ^ (prefixWord ++ tailWord_7830452).sum := by decide
  have hdescent : baseEnd_7830452 < baseStart_7830452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830470 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7830470 : Nat := 118140960795 + 7830470 * 2 ^ 59
def prefixEnd_7830470 : Nat := 4983230072969 + 3 ^ 40 * 7830470 * 2
def baseEnd_7830470 : Nat := 4020794860612083483813331

theorem tailTrace_7830470 : CollatzResearch.WordTrace tailWord_7830470 prefixEnd_7830470 4020794860612083483813331 := by
  unfold tailWord_7830470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925021998173500082819027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190400469294368001766805909 8925021998173500082819027)
  ·
    refine ⟨13387532997260250124228541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8925021998173500082819027 13387532997260250124228541)
    ·
      refine ⟨5020324873972593796585703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13387532997260250124228541 5020324873972593796585703)
      ·
        refine ⟨7530487310958890694878555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020324873972593796585703 7530487310958890694878555)
        ·
          refine ⟨11295730966438336042317833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530487310958890694878555 11295730966438336042317833)
          ·
            refine ⟨8471798224828752031738375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11295730966438336042317833 8471798224828752031738375)
            ·
              refine ⟨12707697337243128047607563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471798224828752031738375 12707697337243128047607563)
              ·
                refine ⟨19061546005864692071411345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707697337243128047607563 19061546005864692071411345)
                ·
                  refine ⟨14296159504398519053558509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19061546005864692071411345 14296159504398519053558509)
                  ·
                    refine ⟨5361059814149444645084441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296159504398519053558509 5361059814149444645084441)
                    ·
                      refine ⟨4020794860612083483813331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361059814149444645084441 4020794860612083483813331)
                      ·
                        rfl

theorem cell23_7830470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7830470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830470 prefixEnd_7830470 := by exact prefixLift 7830470
  have htrace : WordTrace (prefixWord ++ tailWord_7830470) baseStart_7830470 baseEnd_7830470 := by
    simpa [prefixWord, tailWord_7830470, baseEnd_7830470] using wordTrace_append hprefix tailTrace_7830470
  have hstable : (prefixWord ++ tailWord_7830470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830470).length < 2 ^ (prefixWord ++ tailWord_7830470).sum := by decide
  have hdescent : baseEnd_7830470 < baseStart_7830470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830475 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 3, 3, 2]
def baseStart_7830475 : Nat := 118140960795 + 7830475 * 2 ^ 59
def prefixEnd_7830475 : Nat := 4983230072969 + 3 ^ 40 * 7830475 * 2
def baseEnd_7830475 : Nat := 4020797428015355964250807

theorem tailTrace_7830475 : CollatzResearch.WordTrace tailWord_7830475 prefixEnd_7830475 4020797428015355964250807 := by
  unfold tailWord_7830475
  simp only [CollatzResearch.WordTrace]
  refine ⟨285600886306533888504140879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190400590871022592336093919 285600886306533888504140879)
  ·
    refine ⟨428401329459800832756211319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285600886306533888504140879 428401329459800832756211319)
    ·
      refine ⟨642601994189701249134316979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428401329459800832756211319 642601994189701249134316979)
      ·
        refine ⟨963902991284551873701475469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642601994189701249134316979 963902991284551873701475469)
        ·
          refine ⟨361463621731706952638053301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 963902991284551873701475469 361463621731706952638053301)
          ·
            refine ⟨33887214537347526809817497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361463621731706952638053301 33887214537347526809817497)
            ·
              refine ⟨25415410903010645107363123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33887214537347526809817497 25415410903010645107363123)
              ·
                refine ⟨38123116354515967661044685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25415410903010645107363123 38123116354515967661044685)
                ·
                  refine ⟨14296168632943487872891757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38123116354515967661044685 14296168632943487872891757)
                  ·
                    refine ⟨5361063237353807952334409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296168632943487872891757 5361063237353807952334409)
                    ·
                      refine ⟨4020797428015355964250807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361063237353807952334409 4020797428015355964250807)
                      ·
                        rfl

theorem cell23_7830475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3, 2].length) (baseStart_7830475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830475 prefixEnd_7830475 := by exact prefixLift 7830475
  have htrace : WordTrace (prefixWord ++ tailWord_7830475) baseStart_7830475 baseEnd_7830475 := by
    simpa [prefixWord, tailWord_7830475, baseEnd_7830475] using wordTrace_append hprefix tailTrace_7830475
  have hstable : (prefixWord ++ tailWord_7830475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830475).length < 2 ^ (prefixWord ++ tailWord_7830475).sum := by decide
  have hdescent : baseEnd_7830475 < baseStart_7830475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830481 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_7830481 : Nat := 118140960795 + 7830481 * 2 ^ 59
def prefixEnd_7830481 : Nat := 4983230072969 + 3 ^ 40 * 7830481 * 2
def baseEnd_7830481 : Nat := 1340266836299760980258593

theorem tailTrace_7830481 : CollatzResearch.WordTrace tailWord_7830481 prefixEnd_7830481 1340266836299760980258593 := by
  unfold tailWord_7830481
  simp only [CollatzResearch.WordTrace]
  refine ⟨285601105144512151528859297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190400736763008101019239531 285601105144512151528859297)
  ·
    refine ⟨214200828858384113646644473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285601105144512151528859297 214200828858384113646644473)
    ·
      refine ⟨160650621643788085234983355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214200828858384113646644473 160650621643788085234983355)
      ·
        refine ⟨240975932465682127852475033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160650621643788085234983355 240975932465682127852475033)
        ·
          refine ⟨180731949349261595889356275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240975932465682127852475033 180731949349261595889356275)
          ·
            refine ⟨271097924023892393834034413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180731949349261595889356275 271097924023892393834034413)
            ·
              refine ⟨101661721508959647687762905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271097924023892393834034413 101661721508959647687762905)
              ·
                refine ⟨76246291131719735765822179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101661721508959647687762905 76246291131719735765822179)
                ·
                  refine ⟨114369436697579603648733269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76246291131719735765822179 114369436697579603648733269)
                  ·
                    refine ⟨1340266836299760980258593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114369436697579603648733269 1340266836299760980258593)
                    ·
                      rfl

theorem cell23_7830481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_7830481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830481 prefixEnd_7830481 := by exact prefixLift 7830481
  have htrace : WordTrace (prefixWord ++ tailWord_7830481) baseStart_7830481 baseEnd_7830481 := by
    simpa [prefixWord, tailWord_7830481, baseEnd_7830481] using wordTrace_append hprefix tailTrace_7830481
  have hstable : (prefixWord ++ tailWord_7830481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830481).length < 2 ^ (prefixWord ++ tailWord_7830481).sum := by decide
  have hdescent : baseEnd_7830481 < baseStart_7830481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830486 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7830486 : Nat := 118140960795 + 7830486 * 2 ^ 59
def prefixEnd_7830486 : Nat := 4983230072969 + 3 ^ 40 * 7830486 * 2
def baseEnd_7830486 : Nat := 4020803076302555421213257

theorem tailTrace_7830486 : CollatzResearch.WordTrace tailWord_7830486 prefixEnd_7830486 4020803076302555421213257 := by
  unfold tailWord_7830486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850080469343377336424457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190400858339662691588527541 17850080469343377336424457)
  ·
    refine ⟨13387560352007533002318343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17850080469343377336424457 13387560352007533002318343)
    ·
      refine ⟨20081340528011299503477515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13387560352007533002318343 20081340528011299503477515)
      ·
        refine ⟨30122010792016949255216273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20081340528011299503477515 30122010792016949255216273)
        ·
          refine ⟨22591508094012711941412205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30122010792016949255216273 22591508094012711941412205)
          ·
            refine ⟨8471815535254766978029577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22591508094012711941412205 8471815535254766978029577)
            ·
              refine ⟨6353861651441075233522183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8471815535254766978029577 6353861651441075233522183)
              ·
                refine ⟨9530792477161612850283275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353861651441075233522183 9530792477161612850283275)
                ·
                  refine ⟨14296188715742419275424913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9530792477161612850283275 14296188715742419275424913)
                  ·
                    refine ⟨10722141536806814456568685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14296188715742419275424913 10722141536806814456568685)
                    ·
                      refine ⟨4020803076302555421213257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722141536806814456568685 4020803076302555421213257)
                      ·
                        rfl

theorem cell23_7830486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7830486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830486 prefixEnd_7830486 := by exact prefixLift 7830486
  have htrace : WordTrace (prefixWord ++ tailWord_7830486) baseStart_7830486 baseEnd_7830486 := by
    simpa [prefixWord, tailWord_7830486, baseEnd_7830486] using wordTrace_append hprefix tailTrace_7830486
  have hstable : (prefixWord ++ tailWord_7830486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830486).length < 2 ^ (prefixWord ++ tailWord_7830486).sum := by decide
  have hdescent : baseEnd_7830486 < baseStart_7830486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830522 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_7830522 : Nat := 118140960795 + 7830522 * 2 ^ 59
def prefixEnd_7830522 : Nat := 4983230072969 + 3 ^ 40 * 7830522 * 2
def baseEnd_7830522 : Nat := 4020821561606117280363091

theorem tailTrace_7830522 : CollatzResearch.WordTrace tailWord_7830522 prefixEnd_7830522 4020821561606117280363091 := by
  unfold tailWord_7830522
  simp only [CollatzResearch.WordTrace]
  refine ⟨71400650134340903882775455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190401733691575743687401213 71400650134340903882775455)
  ·
    refine ⟨107100975201511355824163183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71400650134340903882775455 107100975201511355824163183)
    ·
      refine ⟨160651462802267033736244775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107100975201511355824163183 160651462802267033736244775)
      ·
        refine ⟨240977194203400550604367163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160651462802267033736244775 240977194203400550604367163)
        ·
          refine ⟨361465791305100825906550745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240977194203400550604367163 361465791305100825906550745)
          ·
            refine ⟨271099343478825619429913059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361465791305100825906550745 271099343478825619429913059)
            ·
              refine ⟨406649015218238429144869589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271099343478825619429913059 406649015218238429144869589)
              ·
                refine ⟨9530836294177463183082881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406649015218238429144869589 9530836294177463183082881)
                ·
                  refine ⟨7148127220633097387312161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530836294177463183082881 7148127220633097387312161)
                  ·
                    refine ⟨5361095415474823040484121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7148127220633097387312161 5361095415474823040484121)
                    ·
                      refine ⟨4020821561606117280363091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361095415474823040484121 4020821561606117280363091)
                      ·
                        rfl

theorem cell23_7830522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_7830522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830522 prefixEnd_7830522 := by exact prefixLift 7830522
  have htrace : WordTrace (prefixWord ++ tailWord_7830522) baseStart_7830522 baseEnd_7830522 := by
    simpa [prefixWord, tailWord_7830522, baseEnd_7830522] using wordTrace_append hprefix tailTrace_7830522
  have hstable : (prefixWord ++ tailWord_7830522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830522).length < 2 ^ (prefixWord ++ tailWord_7830522).sum := by decide
  have hdescent : baseEnd_7830522 < baseStart_7830522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830526 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7830526 : Nat := 118140960795 + 7830526 * 2 ^ 59
def prefixEnd_7830526 : Nat := 4983230072969 + 3 ^ 40 * 7830526 * 2
def baseEnd_7830526 : Nat := 4020823615528735264713073

theorem tailTrace_7830526 : CollatzResearch.WordTrace tailWord_7830526 prefixEnd_7830526 4020823615528735264713073 := by
  unfold tailWord_7830526
  simp only [CollatzResearch.WordTrace]
  refine ⟨35700343303668640526780929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190401830952899416142831621 35700343303668640526780929)
  ·
    refine ⟨26775257477751480395085697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35700343303668640526780929 26775257477751480395085697)
    ·
      refine ⟨20081443108313610296314273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26775257477751480395085697 20081443108313610296314273)
      ·
        refine ⟨15061082331235207722235705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20081443108313610296314273 15061082331235207722235705)
        ·
          refine ⟨11295811748426405791676779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15061082331235207722235705 11295811748426405791676779)
          ·
            refine ⟨16943717622639608687515169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295811748426405791676779 16943717622639608687515169)
            ·
              refine ⟨12707788216979706515636377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16943717622639608687515169 12707788216979706515636377)
              ·
                refine ⟨9530841162734779886727283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12707788216979706515636377 9530841162734779886727283)
                ·
                  refine ⟨14296261744102169830090925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9530841162734779886727283 14296261744102169830090925)
                  ·
                    refine ⟨5361098154038313686284097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296261744102169830090925 5361098154038313686284097)
                    ·
                      refine ⟨4020823615528735264713073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361098154038313686284097 4020823615528735264713073)
                      ·
                        rfl

theorem cell23_7830526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7830526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830526 prefixEnd_7830526 := by exact prefixLift 7830526
  have htrace : WordTrace (prefixWord ++ tailWord_7830526) baseStart_7830526 baseEnd_7830526 := by
    simpa [prefixWord, tailWord_7830526, baseEnd_7830526] using wordTrace_append hprefix tailTrace_7830526
  have hstable : (prefixWord ++ tailWord_7830526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830526).length < 2 ^ (prefixWord ++ tailWord_7830526).sum := by decide
  have hdescent : baseEnd_7830526 < baseStart_7830526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830565 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_7830565 : Nat := 118140960795 + 7830565 * 2 ^ 59
def prefixEnd_7830565 : Nat := 4983230072969 + 3 ^ 40 * 7830565 * 2
def baseEnd_7830565 : Nat := 4020843641274260612125393

theorem tailTrace_7830565 : CollatzResearch.WordTrace tailWord_7830565 prefixEnd_7830565 4020843641274260612125393 := by
  unfold tailWord_7830565
  simp only [CollatzResearch.WordTrace]
  refine ⟨285604168876207833874917149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190402779250805222583278099 285604168876207833874917149)
  ·
    refine ⟨107101563328577937703093931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285604168876207833874917149 107101563328577937703093931)
    ·
      refine ⟨160652344992866906554640897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107101563328577937703093931 160652344992866906554640897)
      ·
        refine ⟨120489258744650179915980673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160652344992866906554640897 120489258744650179915980673)
        ·
          refine ⟨90366944058487634936985505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120489258744650179915980673 90366944058487634936985505)
          ·
            refine ⟨67775208043865726202739129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90366944058487634936985505 67775208043865726202739129)
            ·
              refine ⟨50831406032899294652054347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67775208043865726202739129 50831406032899294652054347)
              ·
                refine ⟨76247109049348941978081521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50831406032899294652054347 76247109049348941978081521)
                ·
                  refine ⟨57185331787011706483561141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76247109049348941978081521 57185331787011706483561141)
                  ·
                    refine ⟨5361124855032347482833857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57185331787011706483561141 5361124855032347482833857)
                    ·
                      refine ⟨4020843641274260612125393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361124855032347482833857 4020843641274260612125393)
                      ·
                        rfl

theorem cell23_7830565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_7830565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830565 prefixEnd_7830565 := by exact prefixLift 7830565
  have htrace : WordTrace (prefixWord ++ tailWord_7830565) baseStart_7830565 baseEnd_7830565 := by
    simpa [prefixWord, tailWord_7830565, baseEnd_7830565] using wordTrace_append hprefix tailTrace_7830565
  have hstable : (prefixWord ++ tailWord_7830565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830565).length < 2 ^ (prefixWord ++ tailWord_7830565).sum := by decide
  have hdescent : baseEnd_7830565 < baseStart_7830565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830595 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4]
def baseStart_7830595 : Nat := 118140960795 + 7830595 * 2 ^ 59
def prefixEnd_7830595 : Nat := 4983230072969 + 3 ^ 40 * 7830595 * 2
def baseEnd_7830595 : Nat := 4020859045693895494750255

theorem tailTrace_7830595 : CollatzResearch.WordTrace tailWord_7830595 prefixEnd_7830595 4020859045693895494750255 := by
  unfold tailWord_7830595
  simp only [CollatzResearch.WordTrace]
  refine ⟨285605263066099148998509239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190403508710732765999006159 285605263066099148998509239)
  ·
    refine ⟨428407894599148723497763859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285605263066099148998509239 428407894599148723497763859)
    ·
      refine ⟨642611841898723085246645789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428407894599148723497763859 642611841898723085246645789)
      ·
        refine ⟨240979440712021156967492171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642611841898723085246645789 240979440712021156967492171)
        ·
          refine ⟨361469161068031735451238257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240979440712021156967492171 361469161068031735451238257)
          ·
            refine ⟨271101870801023801588428693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361469161068031735451238257 271101870801023801588428693)
            ·
              refine ⟨12707900193797990699457595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271101870801023801588428693 12707900193797990699457595)
              ·
                refine ⟨19061850290696986049186393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707900193797990699457595 19061850290696986049186393)
                ·
                  refine ⟨14296387718022739536889795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19061850290696986049186393 14296387718022739536889795)
                  ·
                    refine ⟨21444581577034109305334693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14296387718022739536889795 21444581577034109305334693)
                    ·
                      refine ⟨4020859045693895494750255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21444581577034109305334693 4020859045693895494750255)
                      ·
                        rfl

theorem cell23_7830595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_7830595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830595 prefixEnd_7830595 := by exact prefixLift 7830595
  have htrace : WordTrace (prefixWord ++ tailWord_7830595) baseStart_7830595 baseEnd_7830595 := by
    simpa [prefixWord, tailWord_7830595, baseEnd_7830595] using wordTrace_append hprefix tailTrace_7830595
  have hstable : (prefixWord ++ tailWord_7830595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830595).length < 2 ^ (prefixWord ++ tailWord_7830595).sum := by decide
  have hdescent : baseEnd_7830595 < baseStart_7830595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830649 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_7830649 : Nat := 118140960795 + 7830649 * 2 ^ 59
def prefixEnd_7830649 : Nat := 4983230072969 + 3 ^ 40 * 7830649 * 2
def baseEnd_7830649 : Nat := 4020886773649238283475007

theorem tailTrace_7830649 : CollatzResearch.WordTrace tailWord_7830649 prefixEnd_7830649 4020886773649238283475007 := by
  unfold tailWord_7830649
  simp only [CollatzResearch.WordTrace]
  refine ⟨285607232607903516220975001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190404821738602344147316667 285607232607903516220975001)
  ·
    refine ⟨214205424455927637165731251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285607232607903516220975001 214205424455927637165731251)
    ·
      refine ⟨321308136683891455748596877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214205424455927637165731251 321308136683891455748596877)
      ·
        refine ⟨120490551256459295905723829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321308136683891455748596877 120490551256459295905723829)
        ·
          refine ⟨11295989180293058991161609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120490551256459295905723829 11295989180293058991161609)
          ·
            refine ⟨8471991885219794243371207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11295989180293058991161609 8471991885219794243371207)
            ·
              refine ⟨12707987827829691365056811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471991885219794243371207 12707987827829691365056811)
              ·
                refine ⟨19061981741744537047585217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707987827829691365056811 19061981741744537047585217)
                ·
                  refine ⟨14296486306308402785688913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19061981741744537047585217 14296486306308402785688913)
                  ·
                    refine ⟨10722364729731302089266685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14296486306308402785688913 10722364729731302089266685)
                    ·
                      refine ⟨4020886773649238283475007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722364729731302089266685 4020886773649238283475007)
                      ·
                        rfl

theorem cell23_7830649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_7830649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830649 prefixEnd_7830649 := by exact prefixLift 7830649
  have htrace : WordTrace (prefixWord ++ tailWord_7830649) baseStart_7830649 baseEnd_7830649 := by
    simpa [prefixWord, tailWord_7830649, baseEnd_7830649] using wordTrace_append hprefix tailTrace_7830649
  have hstable : (prefixWord ++ tailWord_7830649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830649).length < 2 ^ (prefixWord ++ tailWord_7830649).sum := by decide
  have hdescent : baseEnd_7830649 < baseStart_7830649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830679 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7830679 : Nat := 118140960795 + 7830679 * 2 ^ 59
def prefixEnd_7830679 : Nat := 4983230072969 + 3 ^ 40 * 7830679 * 2
def baseEnd_7830679 : Nat := 4020902178068873166099869

theorem tailTrace_7830679 : CollatzResearch.WordTrace tailWord_7830679 prefixEnd_7830679 4020902178068873166099869 := by
  unfold tailWord_7830679
  simp only [CollatzResearch.WordTrace]
  refine ⟨285608326797794831344567091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190405551198529887563044727 285608326797794831344567091)
  ·
    refine ⟨428412490196692247016850637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285608326797794831344567091 428412490196692247016850637)
    ·
      refine ⟨160654683823759592631318989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428412490196692247016850637 160654683823759592631318989)
      ·
        refine ⟨60245506433909847236744621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160654683823759592631318989 60245506433909847236744621)
        ·
          refine ⟨22592064912716192713779233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60245506433909847236744621 22592064912716192713779233)
          ·
            refine ⟨16944048684537144535334425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22592064912716192713779233 16944048684537144535334425)
            ·
              refine ⟨12708036513402858401500819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944048684537144535334425 12708036513402858401500819)
              ·
                refine ⟨19062054770104287602251229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12708036513402858401500819 19062054770104287602251229)
                ·
                  refine ⟨7148270538789107850844211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19062054770104287602251229 7148270538789107850844211)
                  ·
                    refine ⟨10722405808183661776266317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7148270538789107850844211 10722405808183661776266317)
                    ·
                      refine ⟨4020902178068873166099869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722405808183661776266317 4020902178068873166099869)
                      ·
                        rfl

theorem cell23_7830679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7830679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830679 prefixEnd_7830679 := by exact prefixLift 7830679
  have htrace : WordTrace (prefixWord ++ tailWord_7830679) baseStart_7830679 baseEnd_7830679 := by
    simpa [prefixWord, tailWord_7830679, baseEnd_7830679] using wordTrace_append hprefix tailTrace_7830679
  have hstable : (prefixWord ++ tailWord_7830679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830679).length < 2 ^ (prefixWord ++ tailWord_7830679).sum := by decide
  have hdescent : baseEnd_7830679 < baseStart_7830679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830735 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_7830735 : Nat := 118140960795 + 7830735 * 2 ^ 59
def prefixEnd_7830735 : Nat := 4983230072969 + 3 ^ 40 * 7830735 * 2
def baseEnd_7830735 : Nat := 4020930932985524946999611

theorem tailTrace_7830735 : CollatzResearch.WordTrace tailWord_7830735 prefixEnd_7830735 4020930932985524946999611 := by
  unfold tailWord_7830735
  simp only [CollatzResearch.WordTrace]
  refine ⟨285610369285591952908605659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190406912857061301939070439 285610369285591952908605659)
  ·
    refine ⟨428415553928387929362908489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285610369285591952908605659 428415553928387929362908489)
    ·
      refine ⟨321311665446290947022181367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428415553928387929362908489 321311665446290947022181367)
      ·
        refine ⟨481967498169436420533272051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321311665446290947022181367 481967498169436420533272051)
        ·
          refine ⟨722951247254154630799908077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481967498169436420533272051 722951247254154630799908077)
          ·
            refine ⟨271106717720307986549965529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722951247254154630799908077 271106717720307986549965529)
            ·
              refine ⟨203330038290230989912474147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271106717720307986549965529 203330038290230989912474147)
              ·
                refine ⟨304995057435346484868711221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203330038290230989912474147 304995057435346484868711221)
                ·
                  refine ⟨28593286634563732956441677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304995057435346484868711221 28593286634563732956441677)
                  ·
                    refine ⟨10722482487961399858665629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28593286634563732956441677 10722482487961399858665629)
                    ·
                      refine ⟨4020930932985524946999611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722482487961399858665629 4020930932985524946999611)
                      ·
                        rfl

theorem cell23_7830735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_7830735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830735 prefixEnd_7830735 := by exact prefixLift 7830735
  have htrace : WordTrace (prefixWord ++ tailWord_7830735) baseStart_7830735 baseEnd_7830735 := by
    simpa [prefixWord, tailWord_7830735, baseEnd_7830735] using wordTrace_append hprefix tailTrace_7830735
  have hstable : (prefixWord ++ tailWord_7830735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830735).length < 2 ^ (prefixWord ++ tailWord_7830735).sum := by decide
  have hdescent : baseEnd_7830735 < baseStart_7830735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830826 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7830826 : Nat := 118140960795 + 7830826 * 2 ^ 59
def prefixEnd_7830826 : Nat := 4983230072969 + 3 ^ 40 * 7830826 * 2
def baseEnd_7830826 : Nat := 4020977659725084090961693

theorem tailTrace_7830826 : CollatzResearch.WordTrace tailWord_7830826 prefixEnd_7830826 4020977659725084090961693 := by
  unfold tailWord_7830826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71403422082065568862542083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190409125552174850300112221 71403422082065568862542083)
  ·
    refine ⟨107105133123098353293813125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71403422082065568862542083 107105133123098353293813125)
    ·
      refine ⟨20082212460580941242589961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107105133123098353293813125 20082212460580941242589961)
      ·
        refine ⟨15061659345435705931942471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20082212460580941242589961 15061659345435705931942471)
        ·
          refine ⟨22592489018153558897913707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061659345435705931942471 22592489018153558897913707)
          ·
            refine ⟨33888733527230338346870561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22592489018153558897913707 33888733527230338346870561)
            ·
              refine ⟨25416550145422753760152921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33888733527230338346870561 25416550145422753760152921)
              ·
                refine ⟨19062412609067065320114691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25416550145422753760152921 19062412609067065320114691)
                ·
                  refine ⟨28593618913600597980172037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19062412609067065320114691 28593618913600597980172037)
                  ·
                    refine ⟨5361303546300112121282257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28593618913600597980172037 5361303546300112121282257)
                    ·
                      refine ⟨4020977659725084090961693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361303546300112121282257 4020977659725084090961693)
                      ·
                        rfl

theorem cell23_7830826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7830826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830826 prefixEnd_7830826 := by exact prefixLift 7830826
  have htrace : WordTrace (prefixWord ++ tailWord_7830826) baseStart_7830826 baseEnd_7830826 := by
    simpa [prefixWord, tailWord_7830826, baseEnd_7830826] using wordTrace_append hprefix tailTrace_7830826
  have hstable : (prefixWord ++ tailWord_7830826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830826).length < 2 ^ (prefixWord ++ tailWord_7830826).sum := by decide
  have hdescent : baseEnd_7830826 < baseStart_7830826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830842 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_7830842 : Nat := 118140960795 + 7830842 * 2 ^ 59
def prefixEnd_7830842 : Nat := 4983230072969 + 3 ^ 40 * 7830842 * 2
def baseEnd_7830842 : Nat := 4020985875415556028361619

theorem tailTrace_7830842 : CollatzResearch.WordTrace tailWord_7830842 prefixEnd_7830842 4020985875415556028361619 := by
  unfold tailWord_7830842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71403567974051077545687695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190409514597469540121833853 71403567974051077545687695)
  ·
    refine ⟨107105351961076616318531543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71403567974051077545687695 107105351961076616318531543)
    ·
      refine ⟨160658027941614924477797315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107105351961076616318531543 160658027941614924477797315)
      ·
        refine ⟨240987041912422386716695973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160658027941614924477797315 240987041912422386716695973)
        ·
          refine ⟨45185070358579197509380495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240987041912422386716695973 45185070358579197509380495)
          ·
            refine ⟨67777605537868796264070743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45185070358579197509380495 67777605537868796264070743)
            ·
              refine ⟨101666408306803194396106115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67777605537868796264070743 101666408306803194396106115)
              ·
                refine ⟨152499612460204791594159173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101666408306803194396106115 152499612460204791594159173)
                ·
                  refine ⟨28593677336288398423904845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152499612460204791594159173 28593677336288398423904845)
                  ·
                    refine ⟨10722629001108149408964317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28593677336288398423904845 10722629001108149408964317)
                    ·
                      refine ⟨4020985875415556028361619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722629001108149408964317 4020985875415556028361619)
                      ·
                        rfl

theorem cell23_7830842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_7830842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830842 prefixEnd_7830842 := by exact prefixLift 7830842
  have htrace : WordTrace (prefixWord ++ tailWord_7830842) baseStart_7830842 baseEnd_7830842 := by
    simpa [prefixWord, tailWord_7830842, baseEnd_7830842] using wordTrace_append hprefix tailTrace_7830842
  have hstable : (prefixWord ++ tailWord_7830842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830842).length < 2 ^ (prefixWord ++ tailWord_7830842).sum := by decide
  have hdescent : baseEnd_7830842 < baseStart_7830842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830849 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 7]
def baseStart_7830849 : Nat := 118140960795 + 7830849 * 2 ^ 59
def prefixEnd_7830849 : Nat := 4983230072969 + 3 ^ 40 * 7830849 * 2
def baseEnd_7830849 : Nat := 446776607753348611219343

theorem tailTrace_7830849 : CollatzResearch.WordTrace tailWord_7830849 prefixEnd_7830849 446776607753348611219343 := by
  unfold tailWord_7830849
  simp only [CollatzResearch.WordTrace]
  refine ⟨285614527207178950378255601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190409684804785966918837067 285614527207178950378255601)
  ·
    refine ⟨214210895405384212783691701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285614527207178950378255601 214210895405384212783691701)
    ·
      refine ⟨20082271444254769948471097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214210895405384212783691701 20082271444254769948471097)
      ·
        refine ⟨15061703583191077461353323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20082271444254769948471097 15061703583191077461353323)
        ·
          refine ⟨22592555374786616192029985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061703583191077461353323 22592555374786616192029985)
          ·
            refine ⟨16944416531089962144022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22592555374786616192029985 16944416531089962144022489)
            ·
              refine ⟨12708312398317471608016867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944416531089962144022489 12708312398317471608016867)
              ·
                refine ⟨19062468597476207412025301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12708312398317471608016867 19062468597476207412025301)
                ·
                  refine ⟨446776607753348611219343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19062468597476207412025301 446776607753348611219343)
                  ·
                    rfl

theorem cell23_7830849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_7830849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830849 prefixEnd_7830849 := by exact prefixLift 7830849
  have htrace : WordTrace (prefixWord ++ tailWord_7830849) baseStart_7830849 baseEnd_7830849 := by
    simpa [prefixWord, tailWord_7830849, baseEnd_7830849] using wordTrace_append hprefix tailTrace_7830849
  have hstable : (prefixWord ++ tailWord_7830849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830849).length < 2 ^ (prefixWord ++ tailWord_7830849).sum := by decide
  have hdescent : baseEnd_7830849 < baseStart_7830849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7830949 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_7830949 : Nat := 118140960795 + 7830949 * 2 ^ 59
def prefixEnd_7830949 : Nat := 4983230072969 + 3 ^ 40 * 7830949 * 2
def baseEnd_7830949 : Nat := 4021040817845587109723627

theorem tailTrace_7830949 : CollatzResearch.WordTrace tailWord_7830949 prefixEnd_7830949 4021040817845587109723627 := by
  unfold tailWord_7830949
  simp only [CollatzResearch.WordTrace]
  refine ⟨285618174506816667456895901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190412116337877778304597267 285618174506816667456895901)
  ·
    refine ⟨107106815440056250296335963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285618174506816667456895901 107106815440056250296335963)
    ·
      refine ⟨160660223160084375444503945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107106815440056250296335963 160660223160084375444503945)
      ·
        refine ⟨120495167370063281583377959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160660223160084375444503945 120495167370063281583377959)
        ·
          refine ⟨180742751055094922375066939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120495167370063281583377959 180742751055094922375066939)
          ·
            refine ⟨271114126582642383562600409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180742751055094922375066939 271114126582642383562600409)
            ·
              refine ⟨203335594936981787671950307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271114126582642383562600409 203335594936981787671950307)
              ·
                refine ⟨305003392405472681507925461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203335594936981787671950307 305003392405472681507925461)
                ·
                  refine ⟨7148517009503265972842003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305003392405472681507925461 7148517009503265972842003)
                  ·
                    refine ⟨10722775514254898959263005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7148517009503265972842003 10722775514254898959263005)
                    ·
                      refine ⟨4021040817845587109723627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722775514254898959263005 4021040817845587109723627)
                      ·
                        rfl

theorem cell23_7830949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_7830949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830949 prefixEnd_7830949 := by exact prefixLift 7830949
  have htrace : WordTrace (prefixWord ++ tailWord_7830949) baseStart_7830949 baseEnd_7830949 := by
    simpa [prefixWord, tailWord_7830949, baseEnd_7830949] using wordTrace_append hprefix tailTrace_7830949
  have hstable : (prefixWord ++ tailWord_7830949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830949).length < 2 ^ (prefixWord ++ tailWord_7830949).sum := by decide
  have hdescent : baseEnd_7830949 < baseStart_7830949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
