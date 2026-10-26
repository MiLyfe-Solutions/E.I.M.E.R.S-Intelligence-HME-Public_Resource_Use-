import V185TrunkScan23Chunk1349

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7994522 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_7994522 : Nat := 118140960795 + 7994522 * 2 ^ 59
def prefixEnd_7994522 : Nat := 4983230072969 + 3 ^ 40 * 7994522 * 2
def baseEnd_7994522 : Nat := 1368344129647825209869623

theorem tailTrace_7994522 : CollatzResearch.WordTrace tailWord_7994522 prefixEnd_7994522 1368344129647825209869623 := by
  unfold tailWord_7994522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72896042985804906125298455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194389447962146416334129213 72896042985804906125298455)
  ·
    refine ⟨109344064478707359187947683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72896042985804906125298455 109344064478707359187947683)
    ·
      refine ⟨164016096718061038781921525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109344064478707359187947683 164016096718061038781921525)
      ·
        refine ⟨15376509067318222385805143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164016096718061038781921525 15376509067318222385805143)
        ·
          refine ⟨23064763600977333578707715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15376509067318222385805143 23064763600977333578707715)
          ·
            refine ⟨34597145401466000368061573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23064763600977333578707715 34597145401466000368061573)
            ·
              refine ⟨6486964762774875069011545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34597145401466000368061573 6486964762774875069011545)
              ·
                refine ⟨4865223572081156301758659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6486964762774875069011545 4865223572081156301758659)
                ·
                  refine ⟨7297835358121734452637989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865223572081156301758659 7297835358121734452637989)
                  ·
                    refine ⟨1368344129647825209869623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7297835358121734452637989 1368344129647825209869623)
                    ·
                      rfl

theorem cell23_7994522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_7994522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994522 prefixEnd_7994522 := by exact prefixLift 7994522
  have htrace : WordTrace (prefixWord ++ tailWord_7994522) baseStart_7994522 baseEnd_7994522 := by
    simpa [prefixWord, tailWord_7994522, baseEnd_7994522] using wordTrace_append hprefix tailTrace_7994522
  have hstable : (prefixWord ++ tailWord_7994522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994522).length < 2 ^ (prefixWord ++ tailWord_7994522).sum := by decide
  have hdescent : baseEnd_7994522 < baseStart_7994522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994528 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_7994528 : Nat := 118140960795 + 7994528 * 2 ^ 59
def prefixEnd_7994528 : Nat := 4983230072969 + 3 ^ 40 * 7994528 * 2
def baseEnd_7994528 : Nat := 4105035469827402606133841

theorem tailTrace_7994528 : CollatzResearch.WordTrace tailWord_7994528 prefixEnd_7994528 4105035469827402606133841 := by
  unfold tailWord_7994528
  simp only [CollatzResearch.WordTrace]
  refine ⟨145792195390598943762956119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194389593854131925017274825 145792195390598943762956119)
  ·
    refine ⟨218688293085898415644434179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145792195390598943762956119 218688293085898415644434179)
    ·
      refine ⟨328032439628847623466651269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218688293085898415644434179 328032439628847623466651269)
      ·
        refine ⟨61506082430408929399997113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328032439628847623466651269 61506082430408929399997113)
        ·
          refine ⟨46129561822806697049997835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61506082430408929399997113 46129561822806697049997835)
          ·
            refine ⟨69194342734210045574996753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46129561822806697049997835 69194342734210045574996753)
            ·
              refine ⟨51895757050657534181247565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69194342734210045574996753 51895757050657534181247565)
              ·
                refine ⟨19460908893996575317967837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51895757050657534181247565 19460908893996575317967837)
                ·
                  refine ⟨7297840835248715744237939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19460908893996575317967837 7297840835248715744237939)
                  ·
                    refine ⟨10946761252873073616356909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297840835248715744237939 10946761252873073616356909)
                    ·
                      refine ⟨4105035469827402606133841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946761252873073616356909 4105035469827402606133841)
                      ·
                        rfl

theorem cell23_7994528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_7994528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994528 prefixEnd_7994528 := by exact prefixLift 7994528
  have htrace : WordTrace (prefixWord ++ tailWord_7994528) baseStart_7994528 baseEnd_7994528 := by
    simpa [prefixWord, tailWord_7994528, baseEnd_7994528] using wordTrace_append hprefix tailTrace_7994528
  have hstable : (prefixWord ++ tailWord_7994528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994528).length < 2 ^ (prefixWord ++ tailWord_7994528).sum := by decide
  have hdescent : baseEnd_7994528 < baseStart_7994528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994544 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_7994544 : Nat := 118140960795 + 7994544 * 2 ^ 59
def prefixEnd_7994544 : Nat := 4983230072969 + 3 ^ 40 * 7994544 * 2
def baseEnd_7994544 : Nat := 1368347895172624847844589

theorem tailTrace_7994544 : CollatzResearch.WordTrace tailWord_7994544 prefixEnd_7994544 1368347895172624847844589 := by
  unfold tailWord_7994544
  simp only [CollatzResearch.WordTrace]
  refine ⟨145792487174569961129247343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194389982899426614838996457 145792487174569961129247343)
  ·
    refine ⟨218688730761854941693871015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145792487174569961129247343 218688730761854941693871015)
    ·
      refine ⟨328033096142782412540806523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218688730761854941693871015 328033096142782412540806523)
      ·
        refine ⟨492049644214173618811209785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328033096142782412540806523 492049644214173618811209785)
        ·
          refine ⟨369037233160630214108407339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492049644214173618811209785 369037233160630214108407339)
          ·
            refine ⟨553555849740945321162611009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369037233160630214108407339 553555849740945321162611009)
            ·
              refine ⟨415166887305708990871958257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553555849740945321162611009 415166887305708990871958257)
              ·
                refine ⟨311375165479281743153968693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415166887305708990871958257 311375165479281743153968693)
                ·
                  refine ⟨29191421763682663420684565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311375165479281743153968693 29191421763682663420684565)
                  ·
                    refine ⟨1368347895172624847844589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29191421763682663420684565 1368347895172624847844589)
                    ·
                      rfl

theorem cell23_7994544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_7994544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994544 prefixEnd_7994544 := by exact prefixLift 7994544
  have htrace : WordTrace (prefixWord ++ tailWord_7994544) baseStart_7994544 baseEnd_7994544 := by
    simpa [prefixWord, tailWord_7994544, baseEnd_7994544] using wordTrace_append hprefix tailTrace_7994544
  have hstable : (prefixWord ++ tailWord_7994544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994544).length < 2 ^ (prefixWord ++ tailWord_7994544).sum := by decide
  have hdescent : baseEnd_7994544 < baseStart_7994544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994545 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7994545 : Nat := 118140960795 + 7994545 * 2 ^ 59
def prefixEnd_7994545 : Nat := 4983230072969 + 3 ^ 40 * 7994545 * 2
def baseEnd_7994545 : Nat := 4105044198998529039621263

theorem tailTrace_7994545 : CollatzResearch.WordTrace tailWord_7994545 prefixEnd_7994545 4105044198998529039621263 := by
  unfold tailWord_7994545
  simp only [CollatzResearch.WordTrace]
  refine ⟨291585010822136299429281089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194390007214757532952854059 291585010822136299429281089)
  ·
    refine ⟨218688758116602224571960817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291585010822136299429281089 218688758116602224571960817)
    ·
      refine ⟨164016568587451668428970613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218688758116602224571960817 164016568587451668428970613)
      ·
        refine ⟨15376553305073593915215995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164016568587451668428970613 15376553305073593915215995)
        ·
          refine ⟨23064829957610390872823993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15376553305073593915215995 23064829957610390872823993)
          ·
            refine ⟨17298622468207793154617995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23064829957610390872823993 17298622468207793154617995)
            ·
              refine ⟨25947933702311689731926993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17298622468207793154617995 25947933702311689731926993)
              ·
                refine ⟨19460950276733767298945245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25947933702311689731926993 19460950276733767298945245)
                ·
                  refine ⟨7297856353775162737104467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19460950276733767298945245 7297856353775162737104467)
                  ·
                    refine ⟨10946784530662744105656701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297856353775162737104467 10946784530662744105656701)
                    ·
                      refine ⟨4105044198998529039621263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946784530662744105656701 4105044198998529039621263)
                      ·
                        rfl

theorem cell23_7994545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7994545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994545 prefixEnd_7994545 := by exact prefixLift 7994545
  have htrace : WordTrace (prefixWord ++ tailWord_7994545) baseStart_7994545 baseEnd_7994545 := by
    simpa [prefixWord, tailWord_7994545, baseEnd_7994545] using wordTrace_append hprefix tailTrace_7994545
  have hstable : (prefixWord ++ tailWord_7994545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994545).length < 2 ^ (prefixWord ++ tailWord_7994545).sum := by decide
  have hdescent : baseEnd_7994545 < baseStart_7994545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994551 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_7994551 : Nat := 118140960795 + 7994551 * 2 ^ 59
def prefixEnd_7994551 : Nat := 4983230072969 + 3 ^ 40 * 7994551 * 2
def baseEnd_7994551 : Nat := 4105047279882456016146235

theorem tailTrace_7994551 : CollatzResearch.WordTrace tailWord_7994551 prefixEnd_7994551 4105047279882456016146235 := by
  unfold tailWord_7994551
  simp only [CollatzResearch.WordTrace]
  refine ⟨291585229660114562453999507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194390153106743041635999671 291585229660114562453999507)
  ·
    refine ⟨437377844490171843680999261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291585229660114562453999507 437377844490171843680999261)
    ·
      refine ⟨164016691683814441380374723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437377844490171843680999261 164016691683814441380374723)
      ·
        refine ⟨246025037525721662070562085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164016691683814441380374723 246025037525721662070562085)
        ·
          refine ⟨46129694536072811638230391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246025037525721662070562085 46129694536072811638230391)
          ·
            refine ⟨69194541804109217457345587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46129694536072811638230391 69194541804109217457345587)
            ·
              refine ⟨103791812706163826186018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69194541804109217457345587 103791812706163826186018381)
              ·
                refine ⟨38921929764811434819756893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103791812706163826186018381 38921929764811434819756893)
                ·
                  refine ⟨14595723661804288057408835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38921929764811434819756893 14595723661804288057408835)
                  ·
                    refine ⟨21893585492706432086113253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14595723661804288057408835 21893585492706432086113253)
                    ·
                      refine ⟨4105047279882456016146235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21893585492706432086113253 4105047279882456016146235)
                      ·
                        rfl

theorem cell23_7994551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_7994551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994551 prefixEnd_7994551 := by exact prefixLift 7994551
  have htrace : WordTrace (prefixWord ++ tailWord_7994551) baseStart_7994551 baseEnd_7994551 := by
    simpa [prefixWord, tailWord_7994551, baseEnd_7994551] using wordTrace_append hprefix tailTrace_7994551
  have hstable : (prefixWord ++ tailWord_7994551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994551).length < 2 ^ (prefixWord ++ tailWord_7994551).sum := by decide
  have hdescent : baseEnd_7994551 < baseStart_7994551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994571 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3]
def baseStart_7994571 : Nat := 118140960795 + 7994571 * 2 ^ 59
def prefixEnd_7994571 : Nat := 4983230072969 + 3 ^ 40 * 7994571 * 2
def baseEnd_7994571 : Nat := 4105057549495545937896143

theorem tailTrace_7994571 : CollatzResearch.WordTrace tailWord_7994571 prefixEnd_7994571 4105057549495545937896143 := by
  unfold tailWord_7994571
  simp only [CollatzResearch.WordTrace]
  refine ⟨291585959120042105869727567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194390639413361403913151711 291585959120042105869727567)
  ·
    refine ⟨437378938680063158804591351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291585959120042105869727567 437378938680063158804591351)
    ·
      refine ⟨656068408020094738206887027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437378938680063158804591351 656068408020094738206887027)
      ·
        refine ⟨984102612030142107310330541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656068408020094738206887027 984102612030142107310330541)
        ·
          refine ⟨369038479511303290241373953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984102612030142107310330541 369038479511303290241373953)
          ·
            refine ⟨276778859633477467681030465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369038479511303290241373953 276778859633477467681030465)
            ·
              refine ⟨207584144725108100760772849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276778859633477467681030465 207584144725108100760772849)
              ·
                refine ⟨155688108543831075570579637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207584144725108100760772849 155688108543831075570579637)
                ·
                  refine ⟨14595760175984163334741841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155688108543831075570579637 14595760175984163334741841)
                  ·
                    refine ⟨10946820131988122501056381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14595760175984163334741841 10946820131988122501056381)
                    ·
                      refine ⟨4105057549495545937896143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946820131988122501056381 4105057549495545937896143)
                      ·
                        rfl

theorem cell23_7994571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].length) (baseStart_7994571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994571 prefixEnd_7994571 := by exact prefixLift 7994571
  have htrace : WordTrace (prefixWord ++ tailWord_7994571) baseStart_7994571 baseEnd_7994571 := by
    simpa [prefixWord, tailWord_7994571, baseEnd_7994571] using wordTrace_append hprefix tailTrace_7994571
  have hstable : (prefixWord ++ tailWord_7994571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994571).length < 2 ^ (prefixWord ++ tailWord_7994571).sum := by decide
  have hdescent : baseEnd_7994571 < baseStart_7994571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994578 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7994578 : Nat := 118140960795 + 7994578 * 2 ^ 59
def prefixEnd_7994578 : Nat := 4983230072969 + 3 ^ 40 * 7994578 * 2
def baseEnd_7994578 : Nat := 1368353714620042470169537

theorem tailTrace_7994578 : CollatzResearch.WordTrace tailWord_7994578 prefixEnd_7994578 1368353714620042470169537 := by
  unfold tailWord_7994578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72896553607754186516308097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194390809620677830710154925 72896553607754186516308097)
  ·
    refine ⟨54672415205815639887231073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72896553607754186516308097 54672415205815639887231073)
    ·
      refine ⟨41004311404361729915423305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54672415205815639887231073 41004311404361729915423305)
      ·
        refine ⟨30753233553271297436567479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41004311404361729915423305 30753233553271297436567479)
        ·
          refine ⟨46129850329906946154851219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30753233553271297436567479 46129850329906946154851219)
          ·
            refine ⟨69194775494860419232276829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46129850329906946154851219 69194775494860419232276829)
            ·
              refine ⟨25948040810572657212103811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69194775494860419232276829 25948040810572657212103811)
              ·
                refine ⟨38922061215858985818155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25948040810572657212103811 38922061215858985818155717)
                ·
                  refine ⟨7297886477973559840904197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38922061215858985818155717 7297886477973559840904197)
                  ·
                    refine ⟨1368353714620042470169537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7297886477973559840904197 1368353714620042470169537)
                    ·
                      rfl

theorem cell23_7994578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7994578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994578 prefixEnd_7994578 := by exact prefixLift 7994578
  have htrace : WordTrace (prefixWord ++ tailWord_7994578) baseStart_7994578 baseEnd_7994578 := by
    simpa [prefixWord, tailWord_7994578, baseEnd_7994578] using wordTrace_append hprefix tailTrace_7994578
  have hstable : (prefixWord ++ tailWord_7994578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994578).length < 2 ^ (prefixWord ++ tailWord_7994578).sum := by decide
  have hdescent : baseEnd_7994578 < baseStart_7994578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994605 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7994605 : Nat := 118140960795 + 7994605 * 2 ^ 59
def prefixEnd_7994605 : Nat := 4983230072969 + 3 ^ 40 * 7994605 * 2
def baseEnd_7994605 : Nat := 4105075007837798804870987

theorem tailTrace_7994605 : CollatzResearch.WordTrace tailWord_7994605 prefixEnd_7994605 4105075007837798804870987 := by
  unfold tailWord_7994605
  simp only [CollatzResearch.WordTrace]
  refine ⟨291587199201918929676465269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194391466134612619784310179 291587199201918929676465269)
  ·
    refine ⟨27336299925179899657168619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291587199201918929676465269 27336299925179899657168619)
    ·
      refine ⟨41004449887769849485752929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27336299925179899657168619 41004449887769849485752929)
      ·
        refine ⟨30753337415827387114314697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41004449887769849485752929 30753337415827387114314697)
        ·
          refine ⟨23065003061870540335736023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30753337415827387114314697 23065003061870540335736023)
          ·
            refine ⟨34597504592805810503604035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23065003061870540335736023 34597504592805810503604035)
            ·
              refine ⟨51896256889208715755406053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34597504592805810503604035 51896256889208715755406053)
              ·
                refine ⟨9730548166726634204138635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51896256889208715755406053 9730548166726634204138635)
                ·
                  refine ⟨14595822250089951306207953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730548166726634204138635 14595822250089951306207953)
                  ·
                    refine ⟨10946866687567463479655965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14595822250089951306207953 10946866687567463479655965)
                    ·
                      refine ⟨4105075007837798804870987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946866687567463479655965 4105075007837798804870987)
                      ·
                        rfl

theorem cell23_7994605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7994605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994605 prefixEnd_7994605 := by exact prefixLift 7994605
  have htrace : WordTrace (prefixWord ++ tailWord_7994605) baseStart_7994605 baseEnd_7994605 := by
    simpa [prefixWord, tailWord_7994605, baseEnd_7994605] using wordTrace_append hprefix tailTrace_7994605
  have hstable : (prefixWord ++ tailWord_7994605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994605).length < 2 ^ (prefixWord ++ tailWord_7994605).sum := by decide
  have hdescent : baseEnd_7994605 < baseStart_7994605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994618 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_7994618 : Nat := 118140960795 + 7994618 * 2 ^ 59
def prefixEnd_7994618 : Nat := 4983230072969 + 3 ^ 40 * 7994618 * 2
def baseEnd_7994618 : Nat := 4105081683086307254008427

theorem tailTrace_7994618 : CollatzResearch.WordTrace tailWord_7994618 prefixEnd_7994618 4105081683086307254008427 := by
  unfold tailWord_7994618
  simp only [CollatzResearch.WordTrace]
  refine ⟨72896918337717958224172127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194391782233914555264459005 72896918337717958224172127)
  ·
    refine ⟨109345377506576937336258191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72896918337717958224172127 109345377506576937336258191)
    ·
      refine ⟨164018066259865406004387287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109345377506576937336258191 164018066259865406004387287)
      ·
        refine ⟨246027099389798109006580931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164018066259865406004387287 246027099389798109006580931)
        ·
          refine ⟨369040649084697163509871397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246027099389798109006580931 369040649084697163509871397)
          ·
            refine ⟨69195121703380718158100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369040649084697163509871397 69195121703380718158100887)
            ·
              refine ⟨103792682555071077237151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69195121703380718158100887 103792682555071077237151331)
              ·
                refine ⟨155689023832606615855726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103792682555071077237151331 155689023832606615855726997)
                ·
                  refine ⟨7297922992153435118237203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155689023832606615855726997 7297922992153435118237203)
                  ·
                    refine ⟨10946884488230152677355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297922992153435118237203 10946884488230152677355805)
                    ·
                      refine ⟨4105081683086307254008427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946884488230152677355805 4105081683086307254008427)
                      ·
                        rfl

theorem cell23_7994618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_7994618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994618 prefixEnd_7994618 := by exact prefixLift 7994618
  have htrace : WordTrace (prefixWord ++ tailWord_7994618) baseStart_7994618 baseEnd_7994618 := by
    simpa [prefixWord, tailWord_7994618, baseEnd_7994618] using wordTrace_append hprefix tailTrace_7994618
  have hstable : (prefixWord ++ tailWord_7994618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994618).length < 2 ^ (prefixWord ++ tailWord_7994618).sum := by decide
  have hdescent : baseEnd_7994618 < baseStart_7994618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994641 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_7994641 : Nat := 118140960795 + 7994641 * 2 ^ 59
def prefixEnd_7994641 : Nat := 4983230072969 + 3 ^ 40 * 7994641 * 2
def baseEnd_7994641 : Nat := 4105093493141360664020821

theorem tailTrace_7994641 : CollatzResearch.WordTrace tailWord_7994641 prefixEnd_7994641 4105093493141360664020821 := by
  unfold tailWord_7994641
  simp only [CollatzResearch.WordTrace]
  refine ⟨291588512229788507824775777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194392341486525671883183851 291588512229788507824775777)
  ·
    refine ⟨218691384172341380868581833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291588512229788507824775777 218691384172341380868581833)
    ·
      refine ⟨164018538129256035651436375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218691384172341380868581833 164018538129256035651436375)
      ·
        refine ⟨246027807193884053477154563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164018538129256035651436375 246027807193884053477154563)
        ·
          refine ⟨369041710790826080215731845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246027807193884053477154563 369041710790826080215731845)
          ·
            refine ⟨69195320773279890040449721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369041710790826080215731845 69195320773279890040449721)
            ·
              refine ⟨51896490579959917530337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69195320773279890040449721 51896490579959917530337291)
              ·
                refine ⟨77844735869939876295505937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51896490579959917530337291 77844735869939876295505937)
                ·
                  refine ⟨58383551902454907221629453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77844735869939876295505937 58383551902454907221629453)
                  ·
                    refine ⟨21893831963420590208111045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58383551902454907221629453 21893831963420590208111045)
                    ·
                      refine ⟨4105093493141360664020821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21893831963420590208111045 4105093493141360664020821)
                      ·
                        rfl

theorem cell23_7994641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_7994641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994641 prefixEnd_7994641 := by exact prefixLift 7994641
  have htrace : WordTrace (prefixWord ++ tailWord_7994641) baseStart_7994641 baseEnd_7994641 := by
    simpa [prefixWord, tailWord_7994641, baseEnd_7994641] using wordTrace_append hprefix tailTrace_7994641
  have hstable : (prefixWord ++ tailWord_7994641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994641).length < 2 ^ (prefixWord ++ tailWord_7994641).sum := by decide
  have hdescent : baseEnd_7994641 < baseStart_7994641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994652 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7994652 : Nat := 118140960795 + 7994652 * 2 ^ 59
def prefixEnd_7994652 : Nat := 4983230072969 + 3 ^ 40 * 7994652 * 2
def baseEnd_7994652 : Nat := 4105099141428560120983271

theorem tailTrace_7994652 : CollatzResearch.WordTrace tailWord_7994652 prefixEnd_7994652 4105099141428560120983271 := by
  unfold tailWord_7994652
  simp only [CollatzResearch.WordTrace]
  refine ⟨145794456716374328351713105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194392608955165771135617473 145794456716374328351713105)
  ·
    refine ⟨109345842537280746263784829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145794456716374328351713105 109345842537280746263784829)
    ·
      refine ⟨41004690951480279848919311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109345842537280746263784829 41004690951480279848919311)
      ·
        refine ⟨61507036427220419773378967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41004690951480279848919311 61507036427220419773378967)
        ·
          refine ⟨92260554640830629660068451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61507036427220419773378967 92260554640830629660068451)
          ·
            refine ⟨138390831961245944490102677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92260554640830629660068451 138390831961245944490102677)
            ·
              refine ⟨6487070248183403647973563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138390831961245944490102677 6487070248183403647973563)
              ·
                refine ⟨9730605372275105471960345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487070248183403647973563 9730605372275105471960345)
                ·
                  refine ⟨7297954029206329103970259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9730605372275105471960345 7297954029206329103970259)
                  ·
                    refine ⟨10946931043809493655955389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297954029206329103970259 10946931043809493655955389)
                    ·
                      refine ⟨4105099141428560120983271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946931043809493655955389 4105099141428560120983271)
                      ·
                        rfl

theorem cell23_7994652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7994652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994652 prefixEnd_7994652 := by exact prefixLift 7994652
  have htrace : WordTrace (prefixWord ++ tailWord_7994652) baseStart_7994652 baseEnd_7994652 := by
    simpa [prefixWord, tailWord_7994652, baseEnd_7994652] using wordTrace_append hprefix tailTrace_7994652
  have hstable : (prefixWord ++ tailWord_7994652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994652).length < 2 ^ (prefixWord ++ tailWord_7994652).sum := by decide
  have hdescent : baseEnd_7994652 < baseStart_7994652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994671 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_7994671 : Nat := 118140960795 + 7994671 * 2 ^ 59
def prefixEnd_7994671 : Nat := 4983230072969 + 3 ^ 40 * 7994671 * 2
def baseEnd_7994671 : Nat := 4105108897560995546645683

theorem tailTrace_7994671 : CollatzResearch.WordTrace tailWord_7994671 prefixEnd_7994671 4105108897560995546645683 := by
  unfold tailWord_7994671
  simp only [CollatzResearch.WordTrace]
  refine ⟨291589606419679822948367867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194393070946453215298911911 291589606419679822948367867)
  ·
    refine ⟨437384409629519734422551801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291589606419679822948367867 437384409629519734422551801)
    ·
      refine ⟨328038307222139800816913851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437384409629519734422551801 328038307222139800816913851)
      ·
        refine ⟨492057460833209701225370777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328038307222139800816913851 492057460833209701225370777)
        ·
          refine ⟨369043095624907275919028083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492057460833209701225370777 369043095624907275919028083)
          ·
            refine ⟨553564643437360913878542125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369043095624907275919028083 553564643437360913878542125)
            ·
              refine ⟨207586741289010342704453297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553564643437360913878542125 207586741289010342704453297)
              ·
                refine ⟨155690055966757757028339973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207586741289010342704453297 155690055966757757028339973)
                ·
                  refine ⟨29191885493767079442813745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155690055966757757028339973 29191885493767079442813745)
                  ·
                    refine ⟨21893914120325309582110309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29191885493767079442813745 21893914120325309582110309)
                    ·
                      refine ⟨4105108897560995546645683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21893914120325309582110309 4105108897560995546645683)
                      ·
                        rfl

theorem cell23_7994671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_7994671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994671 prefixEnd_7994671 := by exact prefixLift 7994671
  have htrace : WordTrace (prefixWord ++ tailWord_7994671) baseStart_7994671 baseEnd_7994671 := by
    simpa [prefixWord, tailWord_7994671, baseEnd_7994671] using wordTrace_append hprefix tailTrace_7994671
  have hstable : (prefixWord ++ tailWord_7994671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994671).length < 2 ^ (prefixWord ++ tailWord_7994671).sum := by decide
  have hdescent : baseEnd_7994671 < baseStart_7994671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994675 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 4, 2]
def baseStart_7994675 : Nat := 118140960795 + 7994675 * 2 ^ 59
def prefixEnd_7994675 : Nat := 4983230072969 + 3 ^ 40 * 7994675 * 2
def baseEnd_7994675 : Nat := 4105110951483613530995665

theorem tailTrace_7994675 : CollatzResearch.WordTrace tailWord_7994675 prefixEnd_7994675 4105110951483613530995665 := by
  unfold tailWord_7994675
  simp only [CollatzResearch.WordTrace]
  refine ⟨291589752311665331631513479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194393168207776887754342319 291589752311665331631513479)
  ·
    refine ⟨437384628467497997447270219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291589752311665331631513479 437384628467497997447270219)
    ·
      refine ⟨656076942701246996170905329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437384628467497997447270219 656076942701246996170905329)
      ·
        refine ⟨492057707025935247128178997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656076942701246996170905329 492057707025935247128178997)
        ·
          refine ⟨46130410033681429418266781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492057707025935247128178997 46130410033681429418266781)
          ·
            refine ⟨17298903762630536031850043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46130410033681429418266781 17298903762630536031850043)
            ·
              refine ⟨25948355643945804047775065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17298903762630536031850043 25948355643945804047775065)
              ·
                refine ⟨19461266732959353035831299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25948355643945804047775065 19461266732959353035831299)
                ·
                  refine ⟨29191900099439029553746949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19461266732959353035831299 29191900099439029553746949)
                  ·
                    refine ⟨5473481268644818041327553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29191900099439029553746949 5473481268644818041327553)
                    ·
                      refine ⟨4105110951483613530995665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473481268644818041327553 4105110951483613530995665)
                      ·
                        rfl

theorem cell23_7994675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4, 2].length) (baseStart_7994675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994675 prefixEnd_7994675 := by exact prefixLift 7994675
  have htrace : WordTrace (prefixWord ++ tailWord_7994675) baseStart_7994675 baseEnd_7994675 := by
    simpa [prefixWord, tailWord_7994675, baseEnd_7994675] using wordTrace_append hprefix tailTrace_7994675
  have hstable : (prefixWord ++ tailWord_7994675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994675).length < 2 ^ (prefixWord ++ tailWord_7994675).sum := by decide
  have hdescent : baseEnd_7994675 < baseStart_7994675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994721 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7994721 : Nat := 118140960795 + 7994721 * 2 ^ 59
def prefixEnd_7994721 : Nat := 4983230072969 + 3 ^ 40 * 7994721 * 2
def baseEnd_7994721 : Nat := 4105134571593720351020453

theorem tailTrace_7994721 : CollatzResearch.WordTrace tailWord_7994721 prefixEnd_7994721 4105134571593720351020453 := by
  unfold tailWord_7994721
  simp only [CollatzResearch.WordTrace]
  refine ⟨291591430069498681487688017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194394286712999120991792011 291591430069498681487688017)
  ·
    refine ⟨218693572552124011115766013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291591430069498681487688017 218693572552124011115766013)
    ·
      refine ⟨82010089707046504168412255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218693572552124011115766013 82010089707046504168412255)
      ·
        refine ⟨123015134560569756252618383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82010089707046504168412255 123015134560569756252618383)
        ·
          refine ⟨184522701840854634378927575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123015134560569756252618383 184522701840854634378927575)
          ·
            refine ⟨276784052761281951568391363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184522701840854634378927575 276784052761281951568391363)
            ·
              refine ⟨415176079141922927352587045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276784052761281951568391363 415176079141922927352587045)
              ·
                refine ⟨77845514839110548878610071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415176079141922927352587045 77845514839110548878610071)
                ·
                  refine ⟨116768272258665823317915107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77845514839110548878610071 116768272258665823317915107)
                  ·
                    refine ⟨175152408387998734976872661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116768272258665823317915107 175152408387998734976872661)
                    ·
                      refine ⟨4105134571593720351020453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175152408387998734976872661 4105134571593720351020453)
                      ·
                        rfl

theorem cell23_7994721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7994721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994721 prefixEnd_7994721 := by exact prefixLift 7994721
  have htrace : WordTrace (prefixWord ++ tailWord_7994721) baseStart_7994721 baseEnd_7994721 := by
    simpa [prefixWord, tailWord_7994721, baseEnd_7994721] using wordTrace_append hprefix tailTrace_7994721
  have hstable : (prefixWord ++ tailWord_7994721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994721).length < 2 ^ (prefixWord ++ tailWord_7994721).sum := by decide
  have hdescent : baseEnd_7994721 < baseStart_7994721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994748 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_7994748 : Nat := 118140960795 + 7994748 * 2 ^ 59
def prefixEnd_7994748 : Nat := 4983230072969 + 3 ^ 40 * 7994748 * 2
def baseEnd_7994748 : Nat := 4105148435571391745382829

theorem tailTrace_7994748 : CollatzResearch.WordTrace tailWord_7994748 prefixEnd_7994748 4105148435571391745382829 := by
  unfold tailWord_7994748
  simp only [CollatzResearch.WordTrace]
  refine ⟨145796207420200432549460449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194394943226933910065947265 145796207420200432549460449)
  ·
    refine ⟨109347155565150324412095337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145796207420200432549460449 109347155565150324412095337)
    ·
      refine ⟨82010366673862743309071503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109347155565150324412095337 82010366673862743309071503)
      ·
        refine ⟨123015550010794114963607255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82010366673862743309071503 123015550010794114963607255)
        ·
          refine ⟨184523325016191172445410883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123015550010794114963607255 184523325016191172445410883)
          ·
            refine ⟨276784987524286758668116325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184523325016191172445410883 276784987524286758668116325)
            ·
              refine ⟨51897185160803767250271811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276784987524286758668116325 51897185160803767250271811)
              ·
                refine ⟨77845777741205650875407717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51897185160803767250271811 77845777741205650875407717)
                ·
                  refine ⟨14596083326476059539138947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77845777741205650875407717 14596083326476059539138947)
                  ·
                    refine ⟨21894124989714089308708421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14596083326476059539138947 21894124989714089308708421)
                    ·
                      refine ⟨4105148435571391745382829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21894124989714089308708421 4105148435571391745382829)
                      ·
                        rfl

theorem cell23_7994748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_7994748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994748 prefixEnd_7994748 := by exact prefixLift 7994748
  have htrace : WordTrace (prefixWord ++ tailWord_7994748) baseStart_7994748 baseEnd_7994748 := by
    simpa [prefixWord, tailWord_7994748, baseEnd_7994748] using wordTrace_append hprefix tailTrace_7994748
  have hstable : (prefixWord ++ tailWord_7994748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994748).length < 2 ^ (prefixWord ++ tailWord_7994748).sum := by decide
  have hdescent : baseEnd_7994748 < baseStart_7994748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994778 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7994778 : Nat := 118140960795 + 7994778 * 2 ^ 59
def prefixEnd_7994778 : Nat := 4983230072969 + 3 ^ 40 * 7994778 * 2
def baseEnd_7994778 : Nat := 4105163839991026628007691

theorem tailTrace_7994778 : CollatzResearch.WordTrace tailWord_7994778 prefixEnd_7994778 4105163839991026628007691 := by
  unfold tailWord_7994778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72898377257573045055628247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194395672686861453481675325 72898377257573045055628247)
  ·
    refine ⟨109347565886359567583442371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72898377257573045055628247 109347565886359567583442371)
    ·
      refine ⟨164021348829539351375163557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109347565886359567583442371 164021348829539351375163557)
      ·
        refine ⟨30754002905538628382843167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164021348829539351375163557 30754002905538628382843167)
        ·
          refine ⟨46131004358307942574264751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30754002905538628382843167 46131004358307942574264751)
          ·
            refine ⟨69196506537461913861397127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46131004358307942574264751 69196506537461913861397127)
            ·
              refine ⟨103794759806192870792095691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69196506537461913861397127 103794759806192870792095691)
              ·
                refine ⟨155692139709289306188143537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103794759806192870792095691 155692139709289306188143537)
                ·
                  refine ⟨116769104781966979641107653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155692139709289306188143537 116769104781966979641107653)
                  ·
                    refine ⟨21894207146618808682707685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116769104781966979641107653 21894207146618808682707685)
                    ·
                      refine ⟨4105163839991026628007691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21894207146618808682707685 4105163839991026628007691)
                      ·
                        rfl

theorem cell23_7994778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7994778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994778 prefixEnd_7994778 := by exact prefixLift 7994778
  have htrace : WordTrace (prefixWord ++ tailWord_7994778) baseStart_7994778 baseEnd_7994778 := by
    simpa [prefixWord, tailWord_7994778, baseEnd_7994778] using wordTrace_append hprefix tailTrace_7994778
  have hstable : (prefixWord ++ tailWord_7994778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994778).length < 2 ^ (prefixWord ++ tailWord_7994778).sum := by decide
  have hdescent : baseEnd_7994778 < baseStart_7994778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994809 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_7994809 : Nat := 118140960795 + 7994809 * 2 ^ 59
def prefixEnd_7994809 : Nat := 4983230072969 + 3 ^ 40 * 7994809 * 2
def baseEnd_7994809 : Nat := 1368393252630438668906683

theorem tailTrace_7994809 : CollatzResearch.WordTrace tailWord_7994809 prefixEnd_7994809 1368393252630438668906683 := by
  unfold tailWord_7994809
  simp only [CollatzResearch.WordTrace]
  refine ⟨291594639693179872516891481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194396426462119915011260987 291594639693179872516891481)
  ·
    refine ⟨218695979769884904387668611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291594639693179872516891481 218695979769884904387668611)
    ·
      refine ⟨328043969654827356581502917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218695979769884904387668611 328043969654827356581502917)
      ·
        refine ⟨61508244310280129359031797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328043969654827356581502917 61508244310280129359031797)
        ·
          refine ⟨5766397904088762127409231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61508244310280129359031797 5766397904088762127409231)
          ·
            refine ⟨8649596856133143191113847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766397904088762127409231 8649596856133143191113847)
            ·
              refine ⟨12974395284199714786670771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8649596856133143191113847 12974395284199714786670771)
              ·
                refine ⟨19461592926299572180006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12974395284199714786670771 19461592926299572180006157)
                ·
                  refine ⟨7298097347362339567502309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19461592926299572180006157 7298097347362339567502309)
                  ·
                    refine ⟨1368393252630438668906683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298097347362339567502309 1368393252630438668906683)
                    ·
                      rfl

theorem cell23_7994809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_7994809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994809 prefixEnd_7994809 := by exact prefixLift 7994809
  have htrace : WordTrace (prefixWord ++ tailWord_7994809) baseStart_7994809 baseEnd_7994809 := by
    simpa [prefixWord, tailWord_7994809, baseEnd_7994809] using wordTrace_append hprefix tailTrace_7994809
  have hstable : (prefixWord ++ tailWord_7994809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994809).length < 2 ^ (prefixWord ++ tailWord_7994809).sum := by decide
  have hdescent : baseEnd_7994809 < baseStart_7994809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994825 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 6, 3, 2]
def baseStart_7994825 : Nat := 118140960795 + 7994825 * 2 ^ 59
def prefixEnd_7994825 : Nat := 4983230072969 + 3 ^ 40 * 7994825 * 2
def baseEnd_7994825 : Nat := 4105187973581787944119975

theorem tailTrace_7994825 : CollatzResearch.WordTrace tailWord_7994825 prefixEnd_7994825 4105187973581787944119975 := by
  unfold tailWord_7994825
  simp only [CollatzResearch.WordTrace]
  refine ⟨291595223261121907249473929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194396815507414604832982619 291595223261121907249473929)
  ·
    refine ⟨218696417445841430437105447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291595223261121907249473929 218696417445841430437105447)
    ·
      refine ⟨328044626168762145655658171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218696417445841430437105447 328044626168762145655658171)
      ·
        refine ⟨492066939253143218483487257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328044626168762145655658171 492066939253143218483487257)
        ·
          refine ⟨369050204439857413862615443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492066939253143218483487257 369050204439857413862615443)
          ·
            refine ⟨553575306659786120793923165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369050204439857413862615443 553575306659786120793923165)
            ·
              refine ⟨207590739997419795297721187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553575306659786120793923165 207590739997419795297721187)
              ·
                refine ⟨311386109996129692946581781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207590739997419795297721187 311386109996129692946581781)
                ·
                  refine ⟨14596223906068579356871021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311386109996129692946581781 14596223906068579356871021)
                  ·
                    refine ⟨5473583964775717258826633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14596223906068579356871021 5473583964775717258826633)
                    ·
                      refine ⟨4105187973581787944119975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473583964775717258826633 4105187973581787944119975)
                      ·
                        rfl

theorem cell23_7994825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3, 2].length) (baseStart_7994825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994825 prefixEnd_7994825 := by exact prefixLift 7994825
  have htrace : WordTrace (prefixWord ++ tailWord_7994825) baseStart_7994825 baseEnd_7994825 := by
    simpa [prefixWord, tailWord_7994825, baseEnd_7994825] using wordTrace_append hprefix tailTrace_7994825
  have hstable : (prefixWord ++ tailWord_7994825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994825).length < 2 ^ (prefixWord ++ tailWord_7994825).sum := by decide
  have hdescent : baseEnd_7994825 < baseStart_7994825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994842 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_7994842 : Nat := 118140960795 + 7994842 * 2 ^ 59
def prefixEnd_7994842 : Nat := 4983230072969 + 3 ^ 40 * 7994842 * 2
def baseEnd_7994842 : Nat := 4105196702752914377607397

theorem tailTrace_7994842 : CollatzResearch.WordTrace tailWord_7994842 prefixEnd_7994842 4105196702752914377607397 := by
  unfold tailWord_7994842
  simp only [CollatzResearch.WordTrace]
  refine ⟨72898960825515079788210695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194397228868040212768561853 72898960825515079788210695)
  ·
    refine ⟨109348441238272619682316043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72898960825515079788210695 109348441238272619682316043)
    ·
      refine ⟨164022661857408929523474065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109348441238272619682316043 164022661857408929523474065)
      ·
        refine ⟨123016996393056697142605549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164022661857408929523474065 123016996393056697142605549)
        ·
          refine ⟨46131373647396261428477081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123016996393056697142605549 46131373647396261428477081)
          ·
            refine ⟨34598530235547196071357811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46131373647396261428477081 34598530235547196071357811)
            ·
              refine ⟨51897795353320794107036717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34598530235547196071357811 51897795353320794107036717)
              ·
                refine ⟨19461673257495297790138769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51897795353320794107036717 19461673257495297790138769)
                ·
                  refine ⟨14596254943121473342604077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19461673257495297790138769 14596254943121473342604077)
                  ·
                    refine ⟨5473595603670552503476529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14596254943121473342604077 5473595603670552503476529)
                    ·
                      refine ⟨4105196702752914377607397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473595603670552503476529 4105196702752914377607397)
                      ·
                        rfl

theorem cell23_7994842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_7994842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994842 prefixEnd_7994842 := by exact prefixLift 7994842
  have htrace : WordTrace (prefixWord ++ tailWord_7994842) baseStart_7994842 baseEnd_7994842 := by
    simpa [prefixWord, tailWord_7994842, baseEnd_7994842] using wordTrace_append hprefix tailTrace_7994842
  have hstable : (prefixWord ++ tailWord_7994842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994842).length < 2 ^ (prefixWord ++ tailWord_7994842).sum := by decide
  have hdescent : baseEnd_7994842 < baseStart_7994842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994866 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7994866 : Nat := 118140960795 + 7994866 * 2 ^ 59
def prefixEnd_7994866 : Nat := 4983230072969 + 3 ^ 40 * 7994866 * 2
def baseEnd_7994866 : Nat := 4105209026288622283707287

theorem tailTrace_7994866 : CollatzResearch.WordTrace tailWord_7994866 prefixEnd_7994866 4105209026288622283707287 := by
  unfold tailWord_7994866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72899179663493342812929113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194397812435982247501144301 72899179663493342812929113)
  ·
    refine ⟨54674384747620007109696835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72899179663493342812929113 54674384747620007109696835)
    ·
      refine ⟨82011577121430010664545253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54674384747620007109696835 82011577121430010664545253)
      ·
        refine ⟨15377170710268126999602235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82011577121430010664545253 15377170710268126999602235)
        ·
          refine ⟨23065756065402190499403353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15377170710268126999602235 23065756065402190499403353)
          ·
            refine ⟨17299317049051642874552515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23065756065402190499403353 17299317049051642874552515)
            ·
              refine ⟨25948975573577464311828773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299317049051642874552515 25948975573577464311828773)
              ·
                refine ⟨4865432920045774558467895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25948975573577464311828773 4865432920045774558467895)
                ·
                  refine ⟨7298149380068661837701843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865432920045774558467895 7298149380068661837701843)
                  ·
                    refine ⟨10947224070102992756552765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298149380068661837701843 10947224070102992756552765)
                    ·
                      refine ⟨4105209026288622283707287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947224070102992756552765 4105209026288622283707287)
                      ·
                        rfl

theorem cell23_7994866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7994866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994866 prefixEnd_7994866 := by exact prefixLift 7994866
  have htrace : WordTrace (prefixWord ++ tailWord_7994866) baseStart_7994866 baseEnd_7994866 := by
    simpa [prefixWord, tailWord_7994866, baseEnd_7994866] using wordTrace_append hprefix tailTrace_7994866
  have hstable : (prefixWord ++ tailWord_7994866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994866).length < 2 ^ (prefixWord ++ tailWord_7994866).sum := by decide
  have hdescent : baseEnd_7994866 < baseStart_7994866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994882 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7994882 : Nat := 118140960795 + 7994882 * 2 ^ 59
def prefixEnd_7994882 : Nat := 4983230072969 + 3 ^ 40 * 7994882 * 2
def baseEnd_7994882 : Nat := 1368405747326364740369071

theorem tailTrace_7994882 : CollatzResearch.WordTrace tailWord_7994882 prefixEnd_7994882 1368405747326364740369071 := by
  unfold tailWord_7994882
  simp only [CollatzResearch.WordTrace]
  refine ⟨72899325555478851496074725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194398201481276937322865933 72899325555478851496074725)
  ·
    refine ⟨13668623541652284655514011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72899325555478851496074725 13668623541652284655514011)
    ·
      refine ⟨20502935312478426983271017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668623541652284655514011 20502935312478426983271017)
      ·
        refine ⟨15377201484358820237453263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20502935312478426983271017 15377201484358820237453263)
        ·
          refine ⟨23065802226538230356179895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15377201484358820237453263 23065802226538230356179895)
          ·
            refine ⟨34598703339807345534269843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23065802226538230356179895 34598703339807345534269843)
            ·
              refine ⟨51898055009711018301404765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34598703339807345534269843 51898055009711018301404765)
              ·
                refine ⟨19461770628641631863026787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51898055009711018301404765 19461770628641631863026787)
                ·
                  refine ⟨29192655942962447794540181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19461770628641631863026787 29192655942962447794540181)
                  ·
                    refine ⟨1368405747326364740369071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29192655942962447794540181 1368405747326364740369071)
                    ·
                      rfl

theorem cell23_7994882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7994882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994882 prefixEnd_7994882 := by exact prefixLift 7994882
  have htrace : WordTrace (prefixWord ++ tailWord_7994882) baseStart_7994882 baseEnd_7994882 := by
    simpa [prefixWord, tailWord_7994882, baseEnd_7994882] using wordTrace_append hprefix tailTrace_7994882
  have hstable : (prefixWord ++ tailWord_7994882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994882).length < 2 ^ (prefixWord ++ tailWord_7994882).sum := by decide
  have hdescent : baseEnd_7994882 < baseStart_7994882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994949 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_7994949 : Nat := 118140960795 + 7994949 * 2 ^ 59
def prefixEnd_7994949 : Nat := 4983230072969 + 3 ^ 40 * 7994949 * 2
def baseEnd_7994949 : Nat := 4105251645182945458969405

theorem tailTrace_7994949 : CollatzResearch.WordTrace tailWord_7994949 prefixEnd_7994949 4105251645182945458969405 := by
  unfold tailWord_7994949
  simp only [CollatzResearch.WordTrace]
  refine ⟨291599745912672676426987901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194399830608448450951325267 291599745912672676426987901)
  ·
    refine ⟨109349904717252253660120463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291599745912672676426987901 109349904717252253660120463)
    ·
      refine ⟨164024857075878380490180695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109349904717252253660120463 164024857075878380490180695)
      ·
        refine ⟨246037285613817570735271043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164024857075878380490180695 246037285613817570735271043)
        ·
          refine ⟨369055928420726356102906565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246037285613817570735271043 369055928420726356102906565)
          ·
            refine ⟨69197986578886191769294981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369055928420726356102906565 69197986578886191769294981)
            ·
              refine ⟨12974622483541160956742809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69197986578886191769294981 12974622483541160956742809)
              ·
                refine ⟨9730966862655870717557107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12974622483541160956742809 9730966862655870717557107)
                ·
                  refine ⟨14596450293983806076335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730966862655870717557107 14596450293983806076335661)
                  ·
                    refine ⟨5473668860243927278625873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14596450293983806076335661 5473668860243927278625873)
                    ·
                      refine ⟨4105251645182945458969405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473668860243927278625873 4105251645182945458969405)
                      ·
                        rfl

theorem cell23_7994949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_7994949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994949 prefixEnd_7994949 := by exact prefixLift 7994949
  have htrace : WordTrace (prefixWord ++ tailWord_7994949) baseStart_7994949 baseEnd_7994949 := by
    simpa [prefixWord, tailWord_7994949, baseEnd_7994949] using wordTrace_append hprefix tailTrace_7994949
  have hstable : (prefixWord ++ tailWord_7994949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994949).length < 2 ^ (prefixWord ++ tailWord_7994949).sum := by decide
  have hdescent : baseEnd_7994949 < baseStart_7994949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994957 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7994957 : Nat := 118140960795 + 7994957 * 2 ^ 59
def prefixEnd_7994957 : Nat := 4983230072969 + 3 ^ 40 * 7994957 * 2
def baseEnd_7994957 : Nat := 4105255753028181427669369

theorem tailTrace_7994957 : CollatzResearch.WordTrace tailWord_7994957 prefixEnd_7994957 4105255753028181427669369 := by
  unfold tailWord_7994957
  simp only [CollatzResearch.WordTrace]
  refine ⟨291600037696643693793279125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194400025131095795862186083 291600037696643693793279125)
  ·
    refine ⟨13668751767030173146559959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291600037696643693793279125 13668751767030173146559959)
    ·
      refine ⟨20503127650545259719839939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668751767030173146559959 20503127650545259719839939)
      ·
        refine ⟨30754691475817889579759909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20503127650545259719839939 30754691475817889579759909)
        ·
          refine ⟨5766504651715854296204983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30754691475817889579759909 5766504651715854296204983)
          ·
            refine ⟨8649756977573781444307475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766504651715854296204983 8649756977573781444307475)
            ·
              refine ⟨12974635466360672166461213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8649756977573781444307475 12974635466360672166461213)
              ·
                refine ⟨4865488299885252062422955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12974635466360672166461213 4865488299885252062422955)
                ·
                  refine ⟨7298232449827878093634433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865488299885252062422955 7298232449827878093634433)
                  ·
                    refine ⟨5473674337370908570225825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7298232449827878093634433 5473674337370908570225825)
                    ·
                      refine ⟨4105255753028181427669369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473674337370908570225825 4105255753028181427669369)
                      ·
                        rfl

theorem cell23_7994957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7994957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994957 prefixEnd_7994957 := by exact prefixLift 7994957
  have htrace : WordTrace (prefixWord ++ tailWord_7994957) baseStart_7994957 baseEnd_7994957 := by
    simpa [prefixWord, tailWord_7994957, baseEnd_7994957] using wordTrace_append hprefix tailTrace_7994957
  have hstable : (prefixWord ++ tailWord_7994957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994957).length < 2 ^ (prefixWord ++ tailWord_7994957).sum := by decide
  have hdescent : baseEnd_7994957 < baseStart_7994957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7994965 : Nat := 118140960795 + 7994965 * 2 ^ 59
def prefixEnd_7994965 : Nat := 4983230072969 + 3 ^ 40 * 7994965 * 2
def baseEnd_7994965 : Nat := 4105259860873417396369331

theorem tailTrace_7994965 : CollatzResearch.WordTrace tailWord_7994965 prefixEnd_7994965 4105259860873417396369331 := by
  unfold tailWord_7994965
  simp only [CollatzResearch.WordTrace]
  refine ⟨291600329480614711159570349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194400219653743140773046899 291600329480614711159570349)
  ·
    refine ⟨109350123555230516684838881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291600329480614711159570349 109350123555230516684838881)
    ·
      refine ⟨82012592666422887513629161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109350123555230516684838881 82012592666422887513629161)
      ·
        refine ⟨61509444499817165635221871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82012592666422887513629161 61509444499817165635221871)
        ·
          refine ⟨92264166749725748452832807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61509444499817165635221871 92264166749725748452832807)
          ·
            refine ⟨138396250124588622679249211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92264166749725748452832807 138396250124588622679249211)
            ·
              refine ⟨207594375186882934018873817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138396250124588622679249211 207594375186882934018873817)
              ·
                refine ⟨155695781390162200514155363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207594375186882934018873817 155695781390162200514155363)
                ·
                  refine ⟨233543672085243300771233045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155695781390162200514155363 233543672085243300771233045)
                  ·
                    refine ⟨10947359628995779723651549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 233543672085243300771233045 10947359628995779723651549)
                    ·
                      refine ⟨4105259860873417396369331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947359628995779723651549 4105259860873417396369331)
                      ·
                        rfl

theorem cell23_7994965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7994965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994965 prefixEnd_7994965 := by exact prefixLift 7994965
  have htrace : WordTrace (prefixWord ++ tailWord_7994965) baseStart_7994965 baseEnd_7994965 := by
    simpa [prefixWord, tailWord_7994965, baseEnd_7994965] using wordTrace_append hprefix tailTrace_7994965
  have hstable : (prefixWord ++ tailWord_7994965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994965).length < 2 ^ (prefixWord ++ tailWord_7994965).sum := by decide
  have hdescent : baseEnd_7994965 < baseStart_7994965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994979 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7994979 : Nat := 118140960795 + 7994979 * 2 ^ 59
def prefixEnd_7994979 : Nat := 4983230072969 + 3 ^ 40 * 7994979 * 2
def baseEnd_7994979 : Nat := 4105267049602580341594267

theorem tailTrace_7994979 : CollatzResearch.WordTrace tailWord_7994979 prefixEnd_7994979 4105267049602580341594267 := by
  unfold tailWord_7994979
  simp only [CollatzResearch.WordTrace]
  refine ⟨291600840102563991550579991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194400560068375994367053327 291600840102563991550579991)
  ·
    refine ⟨437401260153845987325869987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291600840102563991550579991 437401260153845987325869987)
    ·
      refine ⟨656101890230768980988804981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437401260153845987325869987 656101890230768980988804981)
      ·
        refine ⟨61509552209134591967700467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656101890230768980988804981 61509552209134591967700467)
        ·
          refine ⟨92264328313701887951550701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61509552209134591967700467 92264328313701887951550701)
          ·
            refine ⟨34599123117638207981831513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92264328313701887951550701 34599123117638207981831513)
            ·
              refine ⟨25949342338228655986373635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34599123117638207981831513 25949342338228655986373635)
              ·
                refine ⟨38924013507342983979560453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25949342338228655986373635 38924013507342983979560453)
                ·
                  refine ⟨7298252532626809496167585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38924013507342983979560453 7298252532626809496167585)
                  ·
                    refine ⟨5473689399470107122125689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7298252532626809496167585 5473689399470107122125689)
                    ·
                      refine ⟨4105267049602580341594267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473689399470107122125689 4105267049602580341594267)
                      ·
                        rfl

theorem cell23_7994979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7994979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994979 prefixEnd_7994979 := by exact prefixLift 7994979
  have htrace : WordTrace (prefixWord ++ tailWord_7994979) baseStart_7994979 baseEnd_7994979 := by
    simpa [prefixWord, tailWord_7994979, baseEnd_7994979] using wordTrace_append hprefix tailTrace_7994979
  have hstable : (prefixWord ++ tailWord_7994979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994979).length < 2 ^ (prefixWord ++ tailWord_7994979).sum := by decide
  have hdescent : baseEnd_7994979 < baseStart_7994979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994985 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 7]
def baseStart_7994985 : Nat := 118140960795 + 7994985 * 2 ^ 59
def prefixEnd_7994985 : Nat := 4983230072969 + 3 ^ 40 * 7994985 * 2
def baseEnd_7994985 : Nat := 456141125609611924235471

theorem tailTrace_7994985 : CollatzResearch.WordTrace tailWord_7994985 prefixEnd_7994985 456141125609611924235471 := by
  unfold tailWord_7994985
  simp only [CollatzResearch.WordTrace]
  refine ⟨291601058940542254575298409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194400705960361503050198939 291601058940542254575298409)
  ·
    refine ⟨218700794205406690931473807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291601058940542254575298409 218700794205406690931473807)
    ·
      refine ⟨328051191308110036397210711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218700794205406690931473807 328051191308110036397210711)
      ·
        refine ⟨492076786962165054595816067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328051191308110036397210711 492076786962165054595816067)
        ·
          refine ⟨738115180443247581893724101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492076786962165054595816067 738115180443247581893724101)
          ·
            refine ⟨138396596333108921605073269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 738115180443247581893724101 138396596333108921605073269)
            ·
              refine ⟨12974680906228961400475619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138396596333108921605073269 12974680906228961400475619)
              ·
                refine ⟨19462021359343442100713429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12974680906228961400475619 19462021359343442100713429)
                ·
                  refine ⟨456141125609611924235471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19462021359343442100713429 456141125609611924235471)
                  ·
                    rfl

theorem cell23_7994985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_7994985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994985 prefixEnd_7994985 := by exact prefixLift 7994985
  have htrace : WordTrace (prefixWord ++ tailWord_7994985) baseStart_7994985 baseEnd_7994985 := by
    simpa [prefixWord, tailWord_7994985, baseEnd_7994985] using wordTrace_append hprefix tailTrace_7994985
  have hstable : (prefixWord ++ tailWord_7994985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994985).length < 2 ^ (prefixWord ++ tailWord_7994985).sum := by decide
  have hdescent : baseEnd_7994985 < baseStart_7994985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994990 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7994990 : Nat := 118140960795 + 7994990 * 2 ^ 59
def prefixEnd_7994990 : Nat := 4983230072969 + 3 ^ 40 * 7994990 * 2
def baseEnd_7994990 : Nat := 4105272697889779798556717

theorem tailTrace_7994990 : CollatzResearch.WordTrace tailWord_7994990 prefixEnd_7994990 4105272697889779798556717 := by
  unfold tailWord_7994990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450155163190517553653803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194400827537016093619486949 36450155163190517553653803)
  ·
    refine ⟨54675232744785776330480705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36450155163190517553653803 54675232744785776330480705)
    ·
      refine ⟨41006424558589332247860529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54675232744785776330480705 41006424558589332247860529)
      ·
        refine ⟨30754818418941999185895397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41006424558589332247860529 30754818418941999185895397)
        ·
          refine ⟨5766528453551624847355387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30754818418941999185895397 5766528453551624847355387)
          ·
            refine ⟨8649792680327437271033081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766528453551624847355387 8649792680327437271033081)
            ·
              refine ⟨6487344510245577953274811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649792680327437271033081 6487344510245577953274811)
              ·
                refine ⟨9731016765368366929912217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487344510245577953274811 9731016765368366929912217)
                ·
                  refine ⟨7298262574026275197434163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9731016765368366929912217 7298262574026275197434163)
                  ·
                    refine ⟨10947393861039412796151245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298262574026275197434163 10947393861039412796151245)
                    ·
                      refine ⟨4105272697889779798556717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947393861039412796151245 4105272697889779798556717)
                      ·
                        rfl

theorem cell23_7994990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7994990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994990 prefixEnd_7994990 := by exact prefixLift 7994990
  have htrace : WordTrace (prefixWord ++ tailWord_7994990) baseStart_7994990 baseEnd_7994990 := by
    simpa [prefixWord, tailWord_7994990, baseEnd_7994990] using wordTrace_append hprefix tailTrace_7994990
  have hstable : (prefixWord ++ tailWord_7994990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994990).length < 2 ^ (prefixWord ++ tailWord_7994990).sum := by decide
  have hdescent : baseEnd_7994990 < baseStart_7994990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994995 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3]
def baseStart_7994995 : Nat := 118140960795 + 7994995 * 2 ^ 59
def prefixEnd_7994995 : Nat := 4983230072969 + 3 ^ 40 * 7994995 * 2
def baseEnd_7994995 : Nat := 4105275265293052278994193

theorem tailTrace_7994995 : CollatzResearch.WordTrace tailWord_7994995 prefixEnd_7994995 4105275265293052278994193 := by
  unfold tailWord_7994995
  simp only [CollatzResearch.WordTrace]
  refine ⟨291601423670506026283162439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194400949113670684188774959 291601423670506026283162439)
  ·
    refine ⟨437402135505759039424743659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291601423670506026283162439 437402135505759039424743659)
    ·
      refine ⟨656103203258638559137115489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437402135505759039424743659 656103203258638559137115489)
      ·
        refine ⟨492077402443978919352836617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656103203258638559137115489 492077402443978919352836617)
        ·
          refine ⟨369058051832984189514627463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492077402443978919352836617 369058051832984189514627463)
          ·
            refine ⟨553587077749476284271941195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369058051832984189514627463 553587077749476284271941195)
            ·
              refine ⟨830380616624214426407911793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553587077749476284271941195 830380616624214426407911793)
              ·
                refine ⟨622785462468160819805933845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830380616624214426407911793 622785462468160819805933845)
                ·
                  refine ⟨29193068553195038428403149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 622785462468160819805933845 29193068553195038428403149)
                  ·
                    refine ⟨10947400707448139410651181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29193068553195038428403149 10947400707448139410651181)
                    ·
                      refine ⟨4105275265293052278994193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947400707448139410651181 4105275265293052278994193)
                      ·
                        rfl

theorem cell23_7994995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_7994995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994995 prefixEnd_7994995 := by exact prefixLift 7994995
  have htrace : WordTrace (prefixWord ++ tailWord_7994995) baseStart_7994995 baseEnd_7994995 := by
    simpa [prefixWord, tailWord_7994995, baseEnd_7994995] using wordTrace_append hprefix tailTrace_7994995
  have hstable : (prefixWord ++ tailWord_7994995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994995).length < 2 ^ (prefixWord ++ tailWord_7994995).sum := by decide
  have hdescent : baseEnd_7994995 < baseStart_7994995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995032 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_7995032 : Nat := 118140960795 + 7995032 * 2 ^ 59
def prefixEnd_7995032 : Nat := 4983230072969 + 3 ^ 40 * 7995032 * 2
def baseEnd_7995032 : Nat := 1368431421359089544743841

theorem tailTrace_7995032 : CollatzResearch.WordTrace tailWord_7995032 prefixEnd_7995032 1368431421359089544743841 := by
  unfold tailWord_7995032
  simp only [CollatzResearch.WordTrace]
  refine ⟨145801386585685990801129675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194401848780914654401506233 145801386585685990801129675)
  ·
    refine ⟨218702079878528986201694513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145801386585685990801129675 218702079878528986201694513)
    ·
      refine ⟨164026559908896739651270885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218702079878528986201694513 164026559908896739651270885)
      ·
        refine ⟨30754979982918138684613291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164026559908896739651270885 30754979982918138684613291)
        ·
          refine ⟨46132469974377208026919937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30754979982918138684613291 46132469974377208026919937)
          ·
            refine ⟨34599352480782906020189953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46132469974377208026919937 34599352480782906020189953)
            ·
              refine ⟨25949514360587179515142465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34599352480782906020189953 25949514360587179515142465)
              ·
                refine ⟨19462135770440384636356849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25949514360587179515142465 19462135770440384636356849)
                ·
                  refine ⟨14596601827830288477267637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19462135770440384636356849 14596601827830288477267637)
                  ·
                    refine ⟨1368431421359089544743841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14596601827830288477267637 1368431421359089544743841)
                    ·
                      rfl

theorem cell23_7995032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_7995032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995032 prefixEnd_7995032 := by exact prefixLift 7995032
  have htrace : WordTrace (prefixWord ++ tailWord_7995032) baseStart_7995032 baseEnd_7995032 := by
    simpa [prefixWord, tailWord_7995032, baseEnd_7995032] using wordTrace_append hprefix tailTrace_7995032
  have hstable : (prefixWord ++ tailWord_7995032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995032).length < 2 ^ (prefixWord ++ tailWord_7995032).sum := by decide
  have hdescent : baseEnd_7995032 < baseStart_7995032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995072 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_7995072 : Nat := 118140960795 + 7995072 * 2 ^ 59
def prefixEnd_7995072 : Nat := 4983230072969 + 3 ^ 40 * 7995072 * 2
def baseEnd_7995072 : Nat := 4105314803303448477731339

theorem tailTrace_7995072 : CollatzResearch.WordTrace tailWord_7995072 prefixEnd_7995072 4105314803303448477731339 := by
  unfold tailWord_7995072
  simp only [CollatzResearch.WordTrace]
  refine ⟨145802116045613534216857735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194402821394151378955810313 145802116045613534216857735)
  ·
    refine ⟨218703174068420301325286603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145802116045613534216857735 218703174068420301325286603)
    ·
      refine ⟨328054761102630451987929905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218703174068420301325286603 328054761102630451987929905)
      ·
        refine ⟨246041070826972838990947429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328054761102630451987929905 246041070826972838990947429)
        ·
          refine ⟨46132700780057407310802643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246041070826972838990947429 46132700780057407310802643)
          ·
            refine ⟨69199051170086110966203965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46132700780057407310802643 69199051170086110966203965)
            ·
              refine ⟨25949644188782291612326487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69199051170086110966203965 25949644188782291612326487)
              ·
                refine ⟨38924466283173437418489731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25949644188782291612326487 38924466283173437418489731)
                ·
                  refine ⟨58386699424760156127734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38924466283173437418489731 58386699424760156127734597)
                  ·
                    refine ⟨10947506142142529273950237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58386699424760156127734597 10947506142142529273950237)
                    ·
                      refine ⟨4105314803303448477731339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947506142142529273950237 4105314803303448477731339)
                      ·
                        rfl

theorem cell23_7995072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_7995072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995072 prefixEnd_7995072 := by exact prefixLift 7995072
  have htrace : WordTrace (prefixWord ++ tailWord_7995072) baseStart_7995072 baseEnd_7995072 := by
    simpa [prefixWord, tailWord_7995072, baseEnd_7995072] using wordTrace_append hprefix tailTrace_7995072
  have hstable : (prefixWord ++ tailWord_7995072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995072).length < 2 ^ (prefixWord ++ tailWord_7995072).sum := by decide
  have hdescent : baseEnd_7995072 < baseStart_7995072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995095 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7995095 : Nat := 118140960795 + 7995095 * 2 ^ 59
def prefixEnd_7995095 : Nat := 4983230072969 + 3 ^ 40 * 7995095 * 2
def baseEnd_7995095 : Nat := 4105326613358501887743733

theorem tailTrace_7995095 : CollatzResearch.WordTrace tailWord_7995095 prefixEnd_7995095 4105326613358501887743733 := by
  unfold tailWord_7995095
  simp only [CollatzResearch.WordTrace]
  refine ⟨291605070970143743361802739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194403380646762495574535159 291605070970143743361802739)
  ·
    refine ⟨437407606455215615042704109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291605070970143743361802739 437407606455215615042704109)
    ·
      refine ⟨164027852420705855641014041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437407606455215615042704109 164027852420705855641014041)
      ·
        refine ⟨123020889315529391730760531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164027852420705855641014041 123020889315529391730760531)
        ·
          refine ⟨184531333973294087596140797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123020889315529391730760531 184531333973294087596140797)
          ·
            refine ⟨69199250239985282848552799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184531333973294087596140797 69199250239985282848552799)
            ·
              refine ⟨103798875359977924272829199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69199250239985282848552799 103798875359977924272829199)
              ·
                refine ⟨155698313039966886409243799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103798875359977924272829199 155698313039966886409243799)
                ·
                  refine ⟨233547469559950329613865699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155698313039966886409243799 233547469559950329613865699)
                  ·
                    refine ⟨350321204339925494420798549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233547469559950329613865699 350321204339925494420798549)
                    ·
                      refine ⟨4105326613358501887743733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 350321204339925494420798549 4105326613358501887743733)
                      ·
                        rfl

theorem cell23_7995095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7995095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995095 prefixEnd_7995095 := by exact prefixLift 7995095
  have htrace : WordTrace (prefixWord ++ tailWord_7995095) baseStart_7995095 baseEnd_7995095 := by
    simpa [prefixWord, tailWord_7995095, baseEnd_7995095] using wordTrace_append hprefix tailTrace_7995095
  have hstable : (prefixWord ++ tailWord_7995095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995095).length < 2 ^ (prefixWord ++ tailWord_7995095).sum := by decide
  have hdescent : baseEnd_7995095 < baseStart_7995095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995109 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 6]
def baseStart_7995109 : Nat := 118140960795 + 7995109 * 2 ^ 59
def prefixEnd_7995109 : Nat := 4983230072969 + 3 ^ 40 * 7995109 * 2
def baseEnd_7995109 : Nat := 456148200231962759218741

theorem tailTrace_7995109 : CollatzResearch.WordTrace tailWord_7995109 prefixEnd_7995109 456148200231962759218741 := by
  unfold tailWord_7995109
  simp only [CollatzResearch.WordTrace]
  refine ⟨291605581592093023752812381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194403721061395349168541587 291605581592093023752812381)
  ·
    refine ⟨109352093097034883907304643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291605581592093023752812381 109352093097034883907304643)
    ·
      refine ⟨164028139645552325860956965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109352093097034883907304643 164028139645552325860956965)
      ·
        refine ⟨30755276183541061098929431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164028139645552325860956965 30755276183541061098929431)
        ·
          refine ⟨46132914275311591648394147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30755276183541061098929431 46132914275311591648394147)
          ·
            refine ⟨69199371412967387472591221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46132914275311591648394147 69199371412967387472591221)
            ·
              refine ⟨6487441069965692575555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69199371412967387472591221 6487441069965692575555427)
              ·
                refine ⟨9731161604948538863333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487441069965692575555427 9731161604948538863333141)
                ·
                  refine ⟨456148200231962759218741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9731161604948538863333141 456148200231962759218741)
                  ·
                    rfl

theorem cell23_7995109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_7995109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995109 prefixEnd_7995109 := by exact prefixLift 7995109
  have htrace : WordTrace (prefixWord ++ tailWord_7995109) baseStart_7995109 baseEnd_7995109 := by
    simpa [prefixWord, tailWord_7995109, baseEnd_7995109] using wordTrace_append hprefix tailTrace_7995109
  have hstable : (prefixWord ++ tailWord_7995109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995109).length < 2 ^ (prefixWord ++ tailWord_7995109).sum := by decide
  have hdescent : baseEnd_7995109 < baseStart_7995109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995115 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_7995115 : Nat := 118140960795 + 7995115 * 2 ^ 59
def prefixEnd_7995115 : Nat := 4983230072969 + 3 ^ 40 * 7995115 * 2
def baseEnd_7995115 : Nat := 4105336882971591809493641

theorem tailTrace_7995115 : CollatzResearch.WordTrace tailWord_7995115 prefixEnd_7995115 4105336882971591809493641 := by
  unfold tailWord_7995115
  simp only [CollatzResearch.WordTrace]
  refine ⟨291605800430071286777530799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194403866953380857851687199 291605800430071286777530799)
  ·
    refine ⟨437408700645106930166296199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291605800430071286777530799 437408700645106930166296199)
    ·
      refine ⟨656113050967660395249444299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437408700645106930166296199 656113050967660395249444299)
      ·
        refine ⟨984169576451490592874166449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656113050967660395249444299 984169576451490592874166449)
        ·
          refine ⟨738127182338617944655624837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984169576451490592874166449 738127182338617944655624837)
          ·
            refine ⟨138398846688490864622929657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 738127182338617944655624837 138398846688490864622929657)
            ·
              refine ⟨103799135016368148467197243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138398846688490864622929657 103799135016368148467197243)
              ·
                refine ⟨155698702524552222700795865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103799135016368148467197243 155698702524552222700795865)
                ·
                  refine ⟨116774026893414167025596899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155698702524552222700795865 116774026893414167025596899)
                  ·
                    refine ⟨175161040340121250538395349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116774026893414167025596899 175161040340121250538395349)
                    ·
                      refine ⟨4105336882971591809493641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175161040340121250538395349 4105336882971591809493641)
                      ·
                        rfl

theorem cell23_7995115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_7995115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995115 prefixEnd_7995115 := by exact prefixLift 7995115
  have htrace : WordTrace (prefixWord ++ tailWord_7995115) baseStart_7995115 baseEnd_7995115 := by
    simpa [prefixWord, tailWord_7995115, baseEnd_7995115] using wordTrace_append hprefix tailTrace_7995115
  have hstable : (prefixWord ++ tailWord_7995115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995115).length < 2 ^ (prefixWord ++ tailWord_7995115).sum := by decide
  have hdescent : baseEnd_7995115 < baseStart_7995115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995119 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_7995119 : Nat := 118140960795 + 7995119 * 2 ^ 59
def prefixEnd_7995119 : Nat := 4983230072969 + 3 ^ 40 * 7995119 * 2
def baseEnd_7995119 : Nat := 4105338936894209793843623

theorem tailTrace_7995119 : CollatzResearch.WordTrace tailWord_7995119 prefixEnd_7995119 4105338936894209793843623 := by
  unfold tailWord_7995119
  simp only [CollatzResearch.WordTrace]
  refine ⟨291605946322056795460676411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194403964214704530307117607 291605946322056795460676411)
  ·
    refine ⟨437408919483085193191014617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291605946322056795460676411 437408919483085193191014617)
    ·
      refine ⟨328056689612313894893260963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437408919483085193191014617 328056689612313894893260963)
      ·
        refine ⟨492085034418470842339891445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328056689612313894893260963 492085034418470842339891445)
        ·
          refine ⟨46132971976731641469364823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492085034418470842339891445 46132971976731641469364823)
          ·
            refine ⟨69199457965097462204047235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46132971976731641469364823 69199457965097462204047235)
            ·
              refine ⟨103799186947646193306070853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69199457965097462204047235 103799186947646193306070853)
              ·
                refine ⟨19462347552683661244888285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103799186947646193306070853 19462347552683661244888285)
                ·
                  refine ⟨7298380332256372966833107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19462347552683661244888285 7298380332256372966833107)
                  ·
                    refine ⟨10947570498384559450249661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298380332256372966833107 10947570498384559450249661)
                    ·
                      refine ⟨4105338936894209793843623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947570498384559450249661 4105338936894209793843623)
                      ·
                        rfl

theorem cell23_7995119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_7995119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995119 prefixEnd_7995119 := by exact prefixLift 7995119
  have htrace : WordTrace (prefixWord ++ tailWord_7995119) baseStart_7995119 baseEnd_7995119 := by
    simpa [prefixWord, tailWord_7995119, baseEnd_7995119] using wordTrace_append hprefix tailTrace_7995119
  have hstable : (prefixWord ++ tailWord_7995119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995119).length < 2 ^ (prefixWord ++ tailWord_7995119).sum := by decide
  have hdescent : baseEnd_7995119 < baseStart_7995119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995146 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7995146 : Nat := 118140960795 + 7995146 * 2 ^ 59
def prefixEnd_7995146 : Nat := 4983230072969 + 3 ^ 40 * 7995146 * 2
def baseEnd_7995146 : Nat := 4105352800871881188205999

theorem tailTrace_7995146 : CollatzResearch.WordTrace tailWord_7995146 prefixEnd_7995146 4105352800871881188205999 := by
  unfold tailWord_7995146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72901732773239744767977323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194404620728639319381272861 72901732773239744767977323)
  ·
    refine ⟨109352599159859617151965985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72901732773239744767977323 109352599159859617151965985)
    ·
      refine ⟨82014449369894712863974489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109352599159859617151965985 82014449369894712863974489)
      ·
        refine ⟨61510837027421034647980867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82014449369894712863974489 61510837027421034647980867)
        ·
          refine ⟨92266255541131551971971301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61510837027421034647980867 92266255541131551971971301)
          ·
            refine ⟨17299922913962165994744619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92266255541131551971971301 17299922913962165994744619)
            ·
              refine ⟨25949884370943248992116929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299922913962165994744619 25949884370943248992116929)
              ·
                refine ⟨19462413278207436744087697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25949884370943248992116929 19462413278207436744087697)
                ·
                  refine ⟨14596809958655577558065773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19462413278207436744087697 14596809958655577558065773)
                  ·
                    refine ⟨5473803734495841584274665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14596809958655577558065773 5473803734495841584274665)
                    ·
                      refine ⟨4105352800871881188205999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473803734495841584274665 4105352800871881188205999)
                      ·
                        rfl

theorem cell23_7995146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7995146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995146 prefixEnd_7995146 := by exact prefixLift 7995146
  have htrace : WordTrace (prefixWord ++ tailWord_7995146) baseStart_7995146 baseEnd_7995146 := by
    simpa [prefixWord, tailWord_7995146, baseEnd_7995146] using wordTrace_append hprefix tailTrace_7995146
  have hstable : (prefixWord ++ tailWord_7995146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995146).length < 2 ^ (prefixWord ++ tailWord_7995146).sum := by decide
  have hdescent : baseEnd_7995146 < baseStart_7995146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995176 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7995176 : Nat := 118140960795 + 7995176 * 2 ^ 59
def prefixEnd_7995176 : Nat := 4983230072969 + 3 ^ 40 * 7995176 * 2
def baseEnd_7995176 : Nat := 4105368205291516070830861

theorem tailTrace_7995176 : CollatzResearch.WordTrace tailWord_7995176 prefixEnd_7995176 4105368205291516070830861 := by
  unfold tailWord_7995176
  simp only [CollatzResearch.WordTrace]
  refine ⟨145804012641425147097750691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194405350188566862797000921 145804012641425147097750691)
  ·
    refine ⟨218706018962137720646626037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145804012641425147097750691 218706018962137720646626037)
    ·
      refine ⟨20503689277700411310621191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218706018962137720646626037 20503689277700411310621191)
      ·
        refine ⟨30755533916550616965931787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20503689277700411310621191 30755533916550616965931787)
        ·
          refine ⟨46133300874825925448897681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30755533916550616965931787 46133300874825925448897681)
          ·
            refine ⟨34599975656119444086673261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46133300874825925448897681 34599975656119444086673261)
            ·
              refine ⟨12974990871044791532502473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34599975656119444086673261 12974990871044791532502473)
              ·
                refine ⟨9731243153283593649376855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12974990871044791532502473 9731243153283593649376855)
                ·
                  refine ⟨14596864729925390474065283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731243153283593649376855 14596864729925390474065283)
                  ·
                    refine ⟨21895297094888085711097925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14596864729925390474065283 21895297094888085711097925)
                    ·
                      refine ⟨4105368205291516070830861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21895297094888085711097925 4105368205291516070830861)
                      ·
                        rfl

theorem cell23_7995176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7995176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995176 prefixEnd_7995176 := by exact prefixLift 7995176
  have htrace : WordTrace (prefixWord ++ tailWord_7995176) baseStart_7995176 baseEnd_7995176 := by
    simpa [prefixWord, tailWord_7995176, baseEnd_7995176] using wordTrace_append hprefix tailTrace_7995176
  have hstable : (prefixWord ++ tailWord_7995176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995176).length < 2 ^ (prefixWord ++ tailWord_7995176).sum := by decide
  have hdescent : baseEnd_7995176 < baseStart_7995176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995226 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_7995226 : Nat := 118140960795 + 7995226 * 2 ^ 59
def prefixEnd_7995226 : Nat := 4983230072969 + 3 ^ 40 * 7995226 * 2
def baseEnd_7995226 : Nat := 4105393879324240875205631

theorem tailTrace_7995226 : CollatzResearch.WordTrace tailWord_7995226 prefixEnd_7995226 4105393879324240875205631 := by
  unfold tailWord_7995226
  simp only [CollatzResearch.WordTrace]
  refine ⟨72902462233167288183705383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194406565955112768489881021 72902462233167288183705383)
  ·
    refine ⟨109353693349750932275558075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72902462233167288183705383 109353693349750932275558075)
    ·
      refine ⟨164030540024626398413337113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109353693349750932275558075 164030540024626398413337113)
      ·
        refine ⟨123022905018469798810002835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164030540024626398413337113 123022905018469798810002835)
        ·
          refine ⟨184534357527704698215004253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123022905018469798810002835 184534357527704698215004253)
          ·
            refine ⟨69200384072889261830626595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184534357527704698215004253 69200384072889261830626595)
            ·
              refine ⟨103800576109333892745939893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69200384072889261830626595 103800576109333892745939893)
              ·
                refine ⟨9731304010250052444931865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103800576109333892745939893 9731304010250052444931865)
                ·
                  refine ⟨7298478007687539333698899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9731304010250052444931865 7298478007687539333698899)
                  ·
                    refine ⟨10947717011531309000548349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298478007687539333698899 10947717011531309000548349)
                    ·
                      refine ⟨4105393879324240875205631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947717011531309000548349 4105393879324240875205631)
                      ·
                        rfl

theorem cell23_7995226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_7995226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995226 prefixEnd_7995226 := by exact prefixLift 7995226
  have htrace : WordTrace (prefixWord ++ tailWord_7995226) baseStart_7995226 baseEnd_7995226 := by
    simpa [prefixWord, tailWord_7995226, baseEnd_7995226] using wordTrace_append hprefix tailTrace_7995226
  have hstable : (prefixWord ++ tailWord_7995226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995226).length < 2 ^ (prefixWord ++ tailWord_7995226).sum := by decide
  have hdescent : baseEnd_7995226 < baseStart_7995226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995253 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7995253 : Nat := 118140960795 + 7995253 * 2 ^ 59
def prefixEnd_7995253 : Nat := 4983230072969 + 3 ^ 40 * 7995253 * 2
def baseEnd_7995253 : Nat := 4105407743301912269568007

theorem tailTrace_7995253 : CollatzResearch.WordTrace tailWord_7995253 prefixEnd_7995253 4105407743301912269568007 := by
  unfold tailWord_7995253
  simp only [CollatzResearch.WordTrace]
  refine ⟨291610833703571336346054413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194407222469047557564036275 291610833703571336346054413)
  ·
    refine ⟨109354062638839251129770405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291610833703571336346054413 109354062638839251129770405)
    ·
      refine ⟨20503886744782359586831951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109354062638839251129770405 20503886744782359586831951)
      ·
        refine ⟨30755830117173539380247927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20503886744782359586831951 30755830117173539380247927)
        ·
          refine ⟨46133745175760309070371891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30755830117173539380247927 46133745175760309070371891)
          ·
            refine ⟨69200617763640463605557837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46133745175760309070371891 69200617763640463605557837)
            ·
              refine ⟨25950231661365173852084189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69200617763640463605557837 25950231661365173852084189)
              ·
                refine ⟨9731336873011940194531571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25950231661365173852084189 9731336873011940194531571)
                ·
                  refine ⟨14597005309517910291797357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731336873011940194531571 14597005309517910291797357)
                  ·
                    refine ⟨5473876991069216359424009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14597005309517910291797357 5473876991069216359424009)
                    ·
                      refine ⟨4105407743301912269568007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473876991069216359424009 4105407743301912269568007)
                      ·
                        rfl

theorem cell23_7995253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7995253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995253 prefixEnd_7995253 := by exact prefixLift 7995253
  have htrace : WordTrace (prefixWord ++ tailWord_7995253) baseStart_7995253 baseEnd_7995253 := by
    simpa [prefixWord, tailWord_7995253, baseEnd_7995253] using wordTrace_append hprefix tailTrace_7995253
  have hstable : (prefixWord ++ tailWord_7995253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995253).length < 2 ^ (prefixWord ++ tailWord_7995253).sum := by decide
  have hdescent : baseEnd_7995253 < baseStart_7995253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995312 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_7995312 : Nat := 118140960795 + 7995312 * 2 ^ 59
def prefixEnd_7995312 : Nat := 4983230072969 + 3 ^ 40 * 7995312 * 2
def baseEnd_7995312 : Nat := 4105438038660527538730235

theorem tailTrace_7995312 : CollatzResearch.WordTrace tailWord_7995312 prefixEnd_7995312 4105438038660527538730235 := by
  unfold tailWord_7995312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145806492805178794711226095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194408657073571726281634793 145806492805178794711226095)
  ·
    refine ⟨218709739207768192066839143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145806492805178794711226095 218709739207768192066839143)
    ·
      refine ⟨328064608811652288100258715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218709739207768192066839143 328064608811652288100258715)
      ·
        refine ⟨492096913217478432150388073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328064608811652288100258715 492096913217478432150388073)
        ·
          refine ⟨369072684913108824112791055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492096913217478432150388073 369072684913108824112791055)
          ·
            refine ⟨553609027369663236169186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369072684913108824112791055 553609027369663236169186583)
            ·
              refine ⟨830413541054494854253779875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553609027369663236169186583 830413541054494854253779875)
              ·
                refine ⟨1245620311581742281380669813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830413541054494854253779875 1245620311581742281380669813)
                ·
                  refine ⟨116776904210788338879437795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245620311581742281380669813 116776904210788338879437795)
                  ·
                    refine ⟨175165356316182508319156693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116776904210788338879437795 175165356316182508319156693)
                    ·
                      refine ⟨4105438038660527538730235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175165356316182508319156693 4105438038660527538730235)
                      ·
                        rfl

theorem cell23_7995312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_7995312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995312 prefixEnd_7995312 := by exact prefixLift 7995312
  have htrace : WordTrace (prefixWord ++ tailWord_7995312) baseStart_7995312 baseEnd_7995312 := by
    simpa [prefixWord, tailWord_7995312, baseEnd_7995312] using wordTrace_append hprefix tailTrace_7995312
  have hstable : (prefixWord ++ tailWord_7995312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995312).length < 2 ^ (prefixWord ++ tailWord_7995312).sum := by decide
  have hdescent : baseEnd_7995312 < baseStart_7995312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995339 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4]
def baseStart_7995339 : Nat := 118140960795 + 7995339 * 2 ^ 59
def prefixEnd_7995339 : Nat := 4983230072969 + 3 ^ 40 * 7995339 * 2
def baseEnd_7995339 : Nat := 4105451902638198933092611

theorem tailTrace_7995339 : CollatzResearch.WordTrace tailWord_7995339 prefixEnd_7995339 4105451902638198933092611 := by
  unfold tailWord_7995339
  simp only [CollatzResearch.WordTrace]
  refine ⟨291613970381259773033685071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194409313587506515355790047 291613970381259773033685071)
  ·
    refine ⟨437420955571889659550527607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291613970381259773033685071 437420955571889659550527607)
    ·
      refine ⟨656131433357834489325791411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437420955571889659550527607 656131433357834489325791411)
      ·
        refine ⟨984197150036751733988687117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656131433357834489325791411 984197150036751733988687117)
        ·
          refine ⟨369073931263781900245757669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984197150036751733988687117 369073931263781900245757669)
          ·
            refine ⟨69201362111959106296079563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369073931263781900245757669 69201362111959106296079563)
            ·
              refine ⟨103802043167938659444119345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69201362111959106296079563 103802043167938659444119345)
              ·
                refine ⟨77851532375953994583089509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103802043167938659444119345 77851532375953994583089509)
                ·
                  refine ⟨14597162320491373984329283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77851532375953994583089509 14597162320491373984329283)
                  ·
                    refine ⟨21895743480737060976493925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14597162320491373984329283 21895743480737060976493925)
                    ·
                      refine ⟨4105451902638198933092611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21895743480737060976493925 4105451902638198933092611)
                      ·
                        rfl

theorem cell23_7995339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_7995339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995339 prefixEnd_7995339 := by exact prefixLift 7995339
  have htrace : WordTrace (prefixWord ++ tailWord_7995339) baseStart_7995339 baseEnd_7995339 := by
    simpa [prefixWord, tailWord_7995339, baseEnd_7995339] using wordTrace_append hprefix tailTrace_7995339
  have hstable : (prefixWord ++ tailWord_7995339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995339).length < 2 ^ (prefixWord ++ tailWord_7995339).sum := by decide
  have hdescent : baseEnd_7995339 < baseStart_7995339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995376 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_7995376 : Nat := 118140960795 + 7995376 * 2 ^ 59
def prefixEnd_7995376 : Nat := 4983230072969 + 3 ^ 40 * 7995376 * 2
def baseEnd_7995376 : Nat := 4105470901422415288329941

theorem tailTrace_7995376 : CollatzResearch.WordTrace tailWord_7995376 prefixEnd_7995376 4105470901422415288329941 := by
  unfold tailWord_7995376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145807659941062864176390991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194410213254750485568521321 145807659941062864176390991)
  ·
    refine ⟨218711489911594296264586487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145807659941062864176390991 218711489911594296264586487)
    ·
      refine ⟨328067234867391444396879731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218711489911594296264586487 328067234867391444396879731)
      ·
        refine ⟨492100852301087166595319597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328067234867391444396879731 492100852301087166595319597)
        ·
          refine ⟨184537819612907687473244849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492100852301087166595319597 184537819612907687473244849)
          ·
            refine ⟨138403364709680765604933637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184537819612907687473244849 138403364709680765604933637)
            ·
              refine ⟨25950630883065143550925057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138403364709680765604933637 25950630883065143550925057)
              ·
                refine ⟨19462973162298857663193793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25950630883065143550925057 19462973162298857663193793)
                ·
                  refine ⟨14597229871724143247395345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19462973162298857663193793 14597229871724143247395345)
                  ·
                    refine ⟨10947922403793107435546509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14597229871724143247395345 10947922403793107435546509)
                    ·
                      refine ⟨4105470901422415288329941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10947922403793107435546509 4105470901422415288329941)
                      ·
                        rfl

theorem cell23_7995376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_7995376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995376 prefixEnd_7995376 := by exact prefixLift 7995376
  have htrace : WordTrace (prefixWord ++ tailWord_7995376) baseStart_7995376 baseEnd_7995376 := by
    simpa [prefixWord, tailWord_7995376, baseEnd_7995376] using wordTrace_append hprefix tailTrace_7995376
  have hstable : (prefixWord ++ tailWord_7995376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995376).length < 2 ^ (prefixWord ++ tailWord_7995376).sum := by decide
  have hdescent : baseEnd_7995376 < baseStart_7995376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995390 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7995390 : Nat := 118140960795 + 7995390 * 2 ^ 59
def prefixEnd_7995390 : Nat := 4983230072969 + 3 ^ 40 * 7995390 * 2
def baseEnd_7995390 : Nat := 4105478090151578233554877

theorem tailTrace_7995390 : CollatzResearch.WordTrace tailWord_7995390 prefixEnd_7995390 4105478090151578233554877 := by
  unfold tailWord_7995390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36451978813009376092973953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194410553669383339162527749 36451978813009376092973953)
  ·
    refine ⟨27338984109757032069730465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36451978813009376092973953 27338984109757032069730465)
    ·
      refine ⟨20504238082317774052297849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27338984109757032069730465 20504238082317774052297849)
      ·
        refine ⟨15378178561738330539223387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20504238082317774052297849 15378178561738330539223387)
        ·
          refine ⟨23067267842607495808835081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378178561738330539223387 23067267842607495808835081)
          ·
            refine ⟨17300450881955621856626311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23067267842607495808835081 17300450881955621856626311)
            ·
              refine ⟨25950676322933432784939467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17300450881955621856626311 25950676322933432784939467)
              ·
                refine ⟨38926014484400149177409201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25950676322933432784939467 38926014484400149177409201)
                ·
                  refine ⟨29194510863300111883056901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38926014484400149177409201 29194510863300111883056901)
                  ·
                    refine ⟨5473970786868770978073169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29194510863300111883056901 5473970786868770978073169)
                    ·
                      refine ⟨4105478090151578233554877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473970786868770978073169 4105478090151578233554877)
                      ·
                        rfl

theorem cell23_7995390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7995390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995390 prefixEnd_7995390 := by exact prefixLift 7995390
  have htrace : WordTrace (prefixWord ++ tailWord_7995390) baseStart_7995390 baseEnd_7995390 := by
    simpa [prefixWord, tailWord_7995390, baseEnd_7995390] using wordTrace_append hprefix tailTrace_7995390
  have hstable : (prefixWord ++ tailWord_7995390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995390).length < 2 ^ (prefixWord ++ tailWord_7995390).sum := by decide
  have hdescent : baseEnd_7995390 < baseStart_7995390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995440 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 1, 1, 3]
def baseStart_7995440 : Nat := 118140960795 + 7995440 * 2 ^ 59
def prefixEnd_7995440 : Nat := 4983230072969 + 3 ^ 40 * 7995440 * 2
def baseEnd_7995440 : Nat := 4105503764184303037929647

theorem tailTrace_7995440 : CollatzResearch.WordTrace tailWord_7995440 prefixEnd_7995440 4105503764184303037929647 := by
  unfold tailWord_7995440
  simp only [CollatzResearch.WordTrace]
  refine ⟨145808827076946933641555887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194411769435929244855407849 145808827076946933641555887)
  ·
    refine ⟨218713240615420400462333831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145808827076946933641555887 218713240615420400462333831)
    ·
      refine ⟨328069860923130600693500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218713240615420400462333831 328069860923130600693500747)
      ·
        refine ⟨492104791384695901040251121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328069860923130600693500747 492104791384695901040251121)
        ·
          refine ⟨369078593538521925780188341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492104791384695901040251121 369078593538521925780188341)
          ·
            refine ⟨34601118144236430541892657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369078593538521925780188341 34601118144236430541892657)
            ·
              refine ⟨25950838608177322906419493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34601118144236430541892657 25950838608177322906419493)
              ·
                refine ⟨4865782239033248044953655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25950838608177322906419493 4865782239033248044953655)
                ·
                  refine ⟨7298673358549872067430483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865782239033248044953655 7298673358549872067430483)
                  ·
                    refine ⟨10948010037824808101145725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298673358549872067430483 10948010037824808101145725)
                    ·
                      refine ⟨4105503764184303037929647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948010037824808101145725 4105503764184303037929647)
                      ·
                        rfl

theorem cell23_7995440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 1, 3].length) (baseStart_7995440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995440 prefixEnd_7995440 := by exact prefixLift 7995440
  have htrace : WordTrace (prefixWord ++ tailWord_7995440) baseStart_7995440 baseEnd_7995440 := by
    simpa [prefixWord, tailWord_7995440, baseEnd_7995440] using wordTrace_append hprefix tailTrace_7995440
  have hstable : (prefixWord ++ tailWord_7995440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995440).length < 2 ^ (prefixWord ++ tailWord_7995440).sum := by decide
  have hdescent : baseEnd_7995440 < baseStart_7995440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995456 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_7995456 : Nat := 118140960795 + 7995456 * 2 ^ 59
def prefixEnd_7995456 : Nat := 4983230072969 + 3 ^ 40 * 7995456 * 2
def baseEnd_7995456 : Nat := 1368503993291591658443191

theorem tailTrace_7995456 : CollatzResearch.WordTrace tailWord_7995456 prefixEnd_7995456 1368503993291591658443191 := by
  unfold tailWord_7995456
  simp only [CollatzResearch.WordTrace]
  refine ⟨145809118860917951007847111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194412158481223934677129481 145809118860917951007847111)
  ·
    refine ⟨218713678291376926511770667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145809118860917951007847111 218713678291376926511770667)
    ·
      refine ⟨328070517437065389767656001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218713678291376926511770667 328070517437065389767656001)
      ·
        refine ⟨246052888077799042325742001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328070517437065389767656001 246052888077799042325742001)
        ·
          refine ⟨184539666058349281744306501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246052888077799042325742001 184539666058349281744306501)
          ·
            refine ⟨34601187385940490327057469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184539666058349281744306501 34601187385940490327057469)
            ·
              refine ⟨12975445269727683872646551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34601187385940490327057469 12975445269727683872646551)
              ·
                refine ⟨19463167904591525808969827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975445269727683872646551 19463167904591525808969827)
                ·
                  refine ⟨29194751856887288713454741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19463167904591525808969827 29194751856887288713454741)
                  ·
                    refine ⟨1368503993291591658443191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29194751856887288713454741 1368503993291591658443191)
                    ·
                      rfl

theorem cell23_7995456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_7995456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995456 prefixEnd_7995456 := by exact prefixLift 7995456
  have htrace : WordTrace (prefixWord ++ tailWord_7995456) baseStart_7995456 baseEnd_7995456 := by
    simpa [prefixWord, tailWord_7995456, baseEnd_7995456] using wordTrace_append hprefix tailTrace_7995456
  have hstable : (prefixWord ++ tailWord_7995456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995456).length < 2 ^ (prefixWord ++ tailWord_7995456).sum := by decide
  have hdescent : baseEnd_7995456 < baseStart_7995456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995463 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_7995463 : Nat := 118140960795 + 7995463 * 2 ^ 59
def prefixEnd_7995463 : Nat := 4983230072969 + 3 ^ 40 * 7995463 * 2
def baseEnd_7995463 : Nat := 4105515574239356447942041

theorem tailTrace_7995463 : CollatzResearch.WordTrace tailWord_7995463 prefixEnd_7995463 4105515574239356447942041 := by
  unfold tailWord_7995463
  simp only [CollatzResearch.WordTrace]
  refine ⟨291618493032810542211199043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194412328688540361474132695 291618493032810542211199043)
  ·
    refine ⟨437427739549215813316798565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291618493032810542211199043 437427739549215813316798565)
    ·
      refine ⟨82017701165477964996899731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437427739549215813316798565 82017701165477964996899731)
      ·
        refine ⟨123026551748216947495349597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82017701165477964996899731 123026551748216947495349597)
        ·
          refine ⟨46134956905581355310756099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123026551748216947495349597 46134956905581355310756099)
          ·
            refine ⟨69202435358372032966134149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46134956905581355310756099 69202435358372032966134149)
            ·
              refine ⟨12975456629694756181150153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69202435358372032966134149 12975456629694756181150153)
              ·
                refine ⟨9731592472271067135862615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12975456629694756181150153 9731592472271067135862615)
                ·
                  refine ⟨14597388708406600703793923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731592472271067135862615 14597388708406600703793923)
                  ·
                    refine ⟨21896083062609901055690885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14597388708406600703793923 21896083062609901055690885)
                    ·
                      refine ⟨4105515574239356447942041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21896083062609901055690885 4105515574239356447942041)
                      ·
                        rfl

theorem cell23_7995463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_7995463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995463 prefixEnd_7995463 := by exact prefixLift 7995463
  have htrace : WordTrace (prefixWord ++ tailWord_7995463) baseStart_7995463 baseEnd_7995463 := by
    simpa [prefixWord, tailWord_7995463, baseEnd_7995463] using wordTrace_append hprefix tailTrace_7995463
  have hstable : (prefixWord ++ tailWord_7995463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995463).length < 2 ^ (prefixWord ++ tailWord_7995463).sum := by decide
  have hdescent : baseEnd_7995463 < baseStart_7995463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995474 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_7995474 : Nat := 118140960795 + 7995474 * 2 ^ 59
def prefixEnd_7995474 : Nat := 4983230072969 + 3 ^ 40 * 7995474 * 2
def baseEnd_7995474 : Nat := 4105521222526555904904491

theorem tailTrace_7995474 : CollatzResearch.WordTrace tailWord_7995474 prefixEnd_7995474 4105521222526555904904491 := by
  unfold tailWord_7995474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72904723558942672772462369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194412596157180460726566317 72904723558942672772462369)
  ·
    refine ⟨54678542669207004579346777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72904723558942672772462369 54678542669207004579346777)
    ·
      refine ⟨41008907001905253434510083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54678542669207004579346777 41008907001905253434510083)
      ·
        refine ⟨61513360502857880151765125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41008907001905253434510083 61513360502857880151765125)
        ·
          refine ⟨11533755094285852528455961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61513360502857880151765125 11533755094285852528455961)
          ·
            refine ⟨8650316320714389396341971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533755094285852528455961 8650316320714389396341971)
            ·
              refine ⟨12975474481071584094512957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650316320714389396341971 12975474481071584094512957)
              ·
                refine ⟨4865802930401844035442359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12975474481071584094512957 4865802930401844035442359)
                ·
                  refine ⟨7298704395602766053163539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865802930401844035442359 7298704395602766053163539)
                  ·
                    refine ⟨10948056593404149079745309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298704395602766053163539 10948056593404149079745309)
                    ·
                      refine ⟨4105521222526555904904491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948056593404149079745309 4105521222526555904904491)
                      ·
                        rfl

theorem cell23_7995474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_7995474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995474 prefixEnd_7995474 := by exact prefixLift 7995474
  have htrace : WordTrace (prefixWord ++ tailWord_7995474) baseStart_7995474 baseEnd_7995474 := by
    simpa [prefixWord, tailWord_7995474, baseEnd_7995474] using wordTrace_append hprefix tailTrace_7995474
  have hstable : (prefixWord ++ tailWord_7995474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995474).length < 2 ^ (prefixWord ++ tailWord_7995474).sum := by decide
  have hdescent : baseEnd_7995474 < baseStart_7995474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995476 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7995476 : Nat := 118140960795 + 7995476 * 2 ^ 59
def prefixEnd_7995476 : Nat := 4983230072969 + 3 ^ 40 * 7995476 * 2
def baseEnd_7995476 : Nat := 4105522249487864897079481

theorem tailTrace_7995476 : CollatzResearch.WordTrace tailWord_7995476 prefixEnd_7995476 4105522249487864897079481 := by
  unfold tailWord_7995476
  simp only [CollatzResearch.WordTrace]
  refine ⟨145809483590881722715711141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194412644787842296954281521 145809483590881722715711141)
  ·
    refine ⟨27339278173290323009195839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145809483590881722715711141 27339278173290323009195839)
    ·
      refine ⟨41008917259935484513793759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27339278173290323009195839 41008917259935484513793759)
      ·
        refine ⟨61513375889903226770690639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41008917259935484513793759 61513375889903226770690639)
        ·
          refine ⟨92270063834854840156035959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61513375889903226770690639 92270063834854840156035959)
          ·
            refine ⟨138405095752282260234053939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92270063834854840156035959 138405095752282260234053939)
            ·
              refine ⟨207607643628423390351080909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138405095752282260234053939 207607643628423390351080909)
              ·
                refine ⟨77852866360658771381655341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207607643628423390351080909 77852866360658771381655341)
                ·
                  refine ⟨29194824885247039268120753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77852866360658771381655341 29194824885247039268120753)
                  ·
                    refine ⟨21896118663935279451090565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29194824885247039268120753 21896118663935279451090565)
                    ·
                      refine ⟨4105522249487864897079481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21896118663935279451090565 4105522249487864897079481)
                      ·
                        rfl

theorem cell23_7995476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7995476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995476 prefixEnd_7995476 := by exact prefixLift 7995476
  have htrace : WordTrace (prefixWord ++ tailWord_7995476) baseStart_7995476 baseEnd_7995476 := by
    simpa [prefixWord, tailWord_7995476, baseEnd_7995476] using wordTrace_append hprefix tailTrace_7995476
  have hstable : (prefixWord ++ tailWord_7995476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995476).length < 2 ^ (prefixWord ++ tailWord_7995476).sum := by decide
  have hdescent : baseEnd_7995476 < baseStart_7995476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995542 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7995542 : Nat := 118140960795 + 7995542 * 2 ^ 59
def prefixEnd_7995542 : Nat := 4983230072969 + 3 ^ 40 * 7995542 * 2
def baseEnd_7995542 : Nat := 4105556139211061638854179

theorem tailTrace_7995542 : CollatzResearch.WordTrace tailWord_7995542 prefixEnd_7995542 4105556139211061638854179 := by
  unfold tailWord_7995542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226335899970271168957805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194414249599682892468883253 18226335899970271168957805)
  ·
    refine ⟨6834875962488851688359177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18226335899970271168957805 6834875962488851688359177)
    ·
      refine ⟨5126156971866638766269383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834875962488851688359177 5126156971866638766269383)
      ·
        refine ⟨7689235457799958149404075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126156971866638766269383 7689235457799958149404075)
        ·
          refine ⟨11533853186699937224106113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689235457799958149404075 11533853186699937224106113)
          ·
            refine ⟨8650389890024952918079585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533853186699937224106113 8650389890024952918079585)
            ·
              refine ⟨6487792417518714688559689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650389890024952918079585 6487792417518714688559689)
              ·
                refine ⟨4865844313139036016419767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487792417518714688559689 4865844313139036016419767)
                ·
                  refine ⟨7298766469708554024629651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865844313139036016419767 7298766469708554024629651)
                  ·
                    refine ⟨10948149704562831036944477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298766469708554024629651 10948149704562831036944477)
                    ·
                      refine ⟨4105556139211061638854179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948149704562831036944477 4105556139211061638854179)
                      ·
                        rfl

theorem cell23_7995542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7995542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995542 prefixEnd_7995542 := by exact prefixLift 7995542
  have htrace : WordTrace (prefixWord ++ tailWord_7995542) baseStart_7995542 baseEnd_7995542 := by
    simpa [prefixWord, tailWord_7995542, baseEnd_7995542] using wordTrace_append hprefix tailTrace_7995542
  have hstable : (prefixWord ++ tailWord_7995542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995542).length < 2 ^ (prefixWord ++ tailWord_7995542).sum := by decide
  have hdescent : baseEnd_7995542 < baseStart_7995542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995570 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_7995570 : Nat := 118140960795 + 7995570 * 2 ^ 59
def prefixEnd_7995570 : Nat := 4983230072969 + 3 ^ 40 * 7995570 * 2
def baseEnd_7995570 : Nat := 4105570516669387529304049

theorem tailTrace_7995570 : CollatzResearch.WordTrace tailWord_7995570 prefixEnd_7995570 4105570516669387529304049 := by
  unfold tailWord_7995570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72905598910855724871336041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194414930428948599656896109 72905598910855724871336041)
  ·
    refine ⟨54679199183141793653502031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72905598910855724871336041 54679199183141793653502031)
    ·
      refine ⟨82018798774712690480253047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54679199183141793653502031 82018798774712690480253047)
      ·
        refine ⟨123028198162069035720379571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82018798774712690480253047 123028198162069035720379571)
        ·
          refine ⟨184542297243103553580569357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123028198162069035720379571 184542297243103553580569357)
          ·
            refine ⟨69203361466163832592713509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184542297243103553580569357 69203361466163832592713509)
            ·
              refine ⟨12975630274905718611133783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69203361466163832592713509 12975630274905718611133783)
              ·
                refine ⟨19463445412358577916700675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975630274905718611133783 19463445412358577916700675)
                ·
                  refine ⟨29195168118537866875051013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19463445412358577916700675 29195168118537866875051013)
                  ·
                    refine ⟨5474094022225850039072065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29195168118537866875051013 5474094022225850039072065)
                    ·
                      refine ⟨4105570516669387529304049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474094022225850039072065 4105570516669387529304049)
                      ·
                        rfl

theorem cell23_7995570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_7995570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995570 prefixEnd_7995570 := by exact prefixLift 7995570
  have htrace : WordTrace (prefixWord ++ tailWord_7995570) baseStart_7995570 baseEnd_7995570 := by
    simpa [prefixWord, tailWord_7995570, baseEnd_7995570] using wordTrace_append hprefix tailTrace_7995570
  have hstable : (prefixWord ++ tailWord_7995570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995570).length < 2 ^ (prefixWord ++ tailWord_7995570).sum := by decide
  have hdescent : baseEnd_7995570 < baseStart_7995570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995576 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 7]
def baseStart_7995576 : Nat := 118140960795 + 7995576 * 2 ^ 59
def prefixEnd_7995576 : Nat := 4983230072969 + 3 ^ 40 * 7995576 * 2
def baseEnd_7995576 : Nat := 456174844172590500647669

theorem tailTrace_7995576 : CollatzResearch.WordTrace tailWord_7995576 prefixEnd_7995576 456174844172590500647669 := by
  unfold tailWord_7995576
  simp only [CollatzResearch.WordTrace]
  refine ⟨145811307240700581255031291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194415076320934108340041721 145811307240700581255031291)
  ·
    refine ⟨218716960861050871882546937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145811307240700581255031291 218716960861050871882546937)
    ·
      refine ⟨164037720645788153911910203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218716960861050871882546937 164037720645788153911910203)
      ·
        refine ⟨246056580968682230867865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164037720645788153911910203 246056580968682230867865305)
        ·
          refine ⟨184542435726511673150898979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246056580968682230867865305 184542435726511673150898979)
          ·
            refine ⟨276813653589767509726348469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184542435726511673150898979 276813653589767509726348469)
            ·
              refine ⟨25951280024040704036845169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276813653589767509726348469 25951280024040704036845169)
              ·
                refine ⟨19463460018030528027633877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25951280024040704036845169 19463460018030528027633877)
                ·
                  refine ⟨456174844172590500647669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19463460018030528027633877 456174844172590500647669)
                  ·
                    rfl

theorem cell23_7995576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_7995576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995576 prefixEnd_7995576 := by exact prefixLift 7995576
  have htrace : WordTrace (prefixWord ++ tailWord_7995576) baseStart_7995576 baseEnd_7995576 := by
    simpa [prefixWord, tailWord_7995576, baseEnd_7995576] using wordTrace_append hprefix tailTrace_7995576
  have hstable : (prefixWord ++ tailWord_7995576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995576).length < 2 ^ (prefixWord ++ tailWord_7995576).sum := by decide
  have hdescent : baseEnd_7995576 < baseStart_7995576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995616 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_7995616 : Nat := 118140960795 + 7995616 * 2 ^ 59
def prefixEnd_7995616 : Nat := 4983230072969 + 3 ^ 40 * 7995616 * 2
def baseEnd_7995616 : Nat := 4105594136779494349328837

theorem tailTrace_7995616 : CollatzResearch.WordTrace tailWord_7995616 prefixEnd_7995616 4105594136779494349328837 := by
  unfold tailWord_7995616
  simp only [CollatzResearch.WordTrace]
  refine ⟨145812036700628124670759351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194416048934170832894345801 145812036700628124670759351)
  ·
    refine ⟨218718055050942187006139027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145812036700628124670759351 218718055050942187006139027)
    ·
      refine ⟨328077082576413280509208541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218718055050942187006139027 328077082576413280509208541)
      ·
        refine ⟨123028905966154980190953203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328077082576413280509208541 123028905966154980190953203)
        ·
          refine ⟨184543358949232470286429805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123028905966154980190953203 184543358949232470286429805)
          ·
            refine ⟨69203759605962176357411177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184543358949232470286429805 69203759605962176357411177)
            ·
              refine ⟨51902819704471632268058383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69203759605962176357411177 51902819704471632268058383)
              ·
                refine ⟨77854229556707448402087575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51902819704471632268058383 77854229556707448402087575)
                ·
                  refine ⟨116781344335061172603131363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77854229556707448402087575 116781344335061172603131363)
                  ·
                    refine ⟨175172016502591758904697045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116781344335061172603131363 175172016502591758904697045)
                    ·
                      refine ⟨4105594136779494349328837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175172016502591758904697045 4105594136779494349328837)
                      ·
                        rfl

theorem cell23_7995616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_7995616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995616 prefixEnd_7995616 := by exact prefixLift 7995616
  have htrace : WordTrace (prefixWord ++ tailWord_7995616) baseStart_7995616 baseEnd_7995616 := by
    simpa [prefixWord, tailWord_7995616, baseEnd_7995616] using wordTrace_append hprefix tailTrace_7995616
  have hstable : (prefixWord ++ tailWord_7995616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995616).length < 2 ^ (prefixWord ++ tailWord_7995616).sum := by decide
  have hdescent : baseEnd_7995616 < baseStart_7995616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995623 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 7]
def baseStart_7995623 : Nat := 118140960795 + 7995623 * 2 ^ 59
def prefixEnd_7995623 : Nat := 4983230072969 + 3 ^ 40 * 7995623 * 2
def baseEnd_7995623 : Nat := 1368532577048025273980435

theorem tailTrace_7995623 : CollatzResearch.WordTrace tailWord_7995623 prefixEnd_7995623 1368532577048025273980435 := by
  unfold tailWord_7995623
  simp only [CollatzResearch.WordTrace]
  refine ⟨291624328712230889537023523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194416219141487259691349015 291624328712230889537023523)
  ·
    refine ⟨437436493068346334305535285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291624328712230889537023523 437436493068346334305535285)
    ·
      refine ⟨41009671225157468841143933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 437436493068346334305535285 41009671225157468841143933)
      ·
        refine ⟨15378626709434050815428975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41009671225157468841143933 15378626709434050815428975)
        ·
          refine ⟨23067940064151076223143463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378626709434050815428975 23067940064151076223143463)
          ·
            refine ⟨34601910096226614334715195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23067940064151076223143463 34601910096226614334715195)
            ·
              refine ⟨51902865144339921502072793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34601910096226614334715195 51902865144339921502072793)
              ·
                refine ⟨38927148858254941126554595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51902865144339921502072793 38927148858254941126554595)
                ·
                  refine ⟨58390723287382411689831893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38927148858254941126554595 58390723287382411689831893)
                  ·
                    refine ⟨1368532577048025273980435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58390723287382411689831893 1368532577048025273980435)
                    ·
                      rfl

theorem cell23_7995623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_7995623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995623 prefixEnd_7995623 := by exact prefixLift 7995623
  have htrace : WordTrace (prefixWord ++ tailWord_7995623) baseStart_7995623 baseEnd_7995623 := by
    simpa [prefixWord, tailWord_7995623, baseEnd_7995623] using wordTrace_append hprefix tailTrace_7995623
  have hstable : (prefixWord ++ tailWord_7995623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995623).length < 2 ^ (prefixWord ++ tailWord_7995623).sum := by decide
  have hdescent : baseEnd_7995623 < baseStart_7995623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995683 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 6]
def baseStart_7995683 : Nat := 118140960795 + 7995683 * 2 ^ 59
def prefixEnd_7995683 : Nat := 4983230072969 + 3 ^ 40 * 7995683 * 2
def baseEnd_7995683 : Nat := 456180948887038398576781

theorem tailTrace_7995683 : CollatzResearch.WordTrace tailWord_7995683 prefixEnd_7995683 456180948887038398576781 := by
  unfold tailWord_7995683
  simp only [CollatzResearch.WordTrace]
  refine ⟨291626517092013519784207703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194417678061342346522805135 291626517092013519784207703)
  ·
    refine ⟨437439775638020279676311555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291626517092013519784207703 437439775638020279676311555)
    ·
      refine ⟨656159663457030419514467333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437439775638020279676311555 656159663457030419514467333)
      ·
        refine ⟨123029936898193203658962625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 656159663457030419514467333 123029936898193203658962625)
        ·
          refine ⟨92272452673644902744221969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123029936898193203658962625 92272452673644902744221969)
          ·
            refine ⟨69204339505233677058166477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92272452673644902744221969 69204339505233677058166477)
            ·
              refine ⟨25951627314462628896812429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69204339505233677058166477 25951627314462628896812429)
              ·
                refine ⟨9731860242923485836304661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25951627314462628896812429 9731860242923485836304661)
                ·
                  refine ⟨456180948887038398576781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9731860242923485836304661 456180948887038398576781)
                  ·
                    rfl

theorem cell23_7995683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 6].length) (baseStart_7995683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995683 prefixEnd_7995683 := by exact prefixLift 7995683
  have htrace : WordTrace (prefixWord ++ tailWord_7995683) baseStart_7995683 baseEnd_7995683 := by
    simpa [prefixWord, tailWord_7995683, baseEnd_7995683] using wordTrace_append hprefix tailTrace_7995683
  have hstable : (prefixWord ++ tailWord_7995683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995683).length < 2 ^ (prefixWord ++ tailWord_7995683).sum := by decide
  have hdescent : baseEnd_7995683 < baseStart_7995683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995694 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7995694 : Nat := 118140960795 + 7995694 * 2 ^ 59
def prefixEnd_7995694 : Nat := 4983230072969 + 3 ^ 40 * 7995694 * 2
def baseEnd_7995694 : Nat := 4105634188270545044153479

theorem tailTrace_7995694 : CollatzResearch.WordTrace tailWord_7995694 prefixEnd_7995694 4105634188270545044153479 := by
  unfold tailWord_7995694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453364786871708582857267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194417945529982445775238757 36453364786871708582857267)
  ·
    refine ⟨54680047180307562874285901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36453364786871708582857267 54680047180307562874285901)
    ·
      refine ⟨20505017692615336077857213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54680047180307562874285901 20505017692615336077857213)
      ·
        refine ⟨7689381634730751029196455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20505017692615336077857213 7689381634730751029196455)
        ·
          refine ⟨11534072452096126543794683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689381634730751029196455 11534072452096126543794683)
          ·
            refine ⟨17301108678144189815692025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534072452096126543794683 17301108678144189815692025)
            ·
              refine ⟨12975831508608142361769019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301108678144189815692025 12975831508608142361769019)
              ·
                refine ⟨19463747262912213542653529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975831508608142361769019 19463747262912213542653529)
                ·
                  refine ⟨14597810447184160156990147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19463747262912213542653529 14597810447184160156990147)
                  ·
                    refine ⟨21896715670776240235485221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14597810447184160156990147 21896715670776240235485221)
                    ·
                      refine ⟨4105634188270545044153479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21896715670776240235485221 4105634188270545044153479)
                      ·
                        rfl

theorem cell23_7995694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7995694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995694 prefixEnd_7995694 := by exact prefixLift 7995694
  have htrace : WordTrace (prefixWord ++ tailWord_7995694) baseStart_7995694 baseEnd_7995694 := by
    simpa [prefixWord, tailWord_7995694, baseEnd_7995694] using wordTrace_append hprefix tailTrace_7995694
  have hstable : (prefixWord ++ tailWord_7995694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995694).length < 2 ^ (prefixWord ++ tailWord_7995694).sum := by decide
  have hdescent : baseEnd_7995694 < baseStart_7995694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995697 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_7995697 : Nat := 118140960795 + 7995697 * 2 ^ 59
def prefixEnd_7995697 : Nat := 4983230072969 + 3 ^ 40 * 7995697 * 2
def baseEnd_7995697 : Nat := 4105635728712508532415965

theorem tailTrace_7995697 : CollatzResearch.WordTrace tailWord_7995697 prefixEnd_7995697 4105635728712508532415965 := by
  unfold tailWord_7995697
  simp only [CollatzResearch.WordTrace]
  refine ⟨291627027713962800175217345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194418018475975200116811563 291627027713962800175217345)
  ·
    refine ⟨218720270785472100131413009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291627027713962800175217345 218720270785472100131413009)
    ·
      refine ⟨164040203089104075098559757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218720270785472100131413009 164040203089104075098559757)
      ·
        refine ⟨61515076158414028161959909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164040203089104075098559757 61515076158414028161959909)
        ·
          refine ⟨11534076779702630280367483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61515076158414028161959909 11534076779702630280367483)
          ·
            refine ⟨17301115169553945420551225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534076779702630280367483 17301115169553945420551225)
            ·
              refine ⟨12975836377165459065413419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301115169553945420551225 12975836377165459065413419)
              ·
                refine ⟨19463754565748188598120129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975836377165459065413419 19463754565748188598120129)
                ·
                  refine ⟨14597815924311141448590097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19463754565748188598120129 14597815924311141448590097)
                  ·
                    refine ⟨10948361943233356086442573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14597815924311141448590097 10948361943233356086442573)
                    ·
                      refine ⟨4105635728712508532415965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948361943233356086442573 4105635728712508532415965)
                      ·
                        rfl

theorem cell23_7995697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_7995697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995697 prefixEnd_7995697 := by exact prefixLift 7995697
  have htrace : WordTrace (prefixWord ++ tailWord_7995697) baseStart_7995697 baseEnd_7995697 := by
    simpa [prefixWord, tailWord_7995697, baseEnd_7995697] using wordTrace_append hprefix tailTrace_7995697
  have hstable : (prefixWord ++ tailWord_7995697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995697).length < 2 ^ (prefixWord ++ tailWord_7995697).sum := by decide
  have hdescent : baseEnd_7995697 < baseStart_7995697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995743 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 6]
def baseStart_7995743 : Nat := 118140960795 + 7995743 * 2 ^ 59
def prefixEnd_7995743 : Nat := 4983230072969 + 3 ^ 40 * 7995743 * 2
def baseEnd_7995743 : Nat := 1368553116274205117480251

theorem tailTrace_7995743 : CollatzResearch.WordTrace tailWord_7995743 prefixEnd_7995743 1368553116274205117480251 := by
  unfold tailWord_7995743
  simp only [CollatzResearch.WordTrace]
  refine ⟨291628705471796150031391883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194419136981197433354261255 291628705471796150031391883)
  ·
    refine ⟨437443058207694225047087825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291628705471796150031391883 437443058207694225047087825)
    ·
      refine ⟨328082293655770668785315869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437443058207694225047087825 328082293655770668785315869)
      ·
        refine ⟨123030860120914000794493451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328082293655770668785315869 123030860120914000794493451)
        ·
          refine ⟨184546290181371001191740177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123030860120914000794493451 184546290181371001191740177)
          ·
            refine ⟨138409717636028250893805133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184546290181371001191740177 138409717636028250893805133)
            ·
              refine ⟨51903644113510594085176925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138409717636028250893805133 51903644113510594085176925)
              ·
                refine ⟨19463866542566472781941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51903644113510594085176925 19463866542566472781941347)
                ·
                  refine ⟨29195799813849709172912021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19463866542566472781941347 29195799813849709172912021)
                  ·
                    refine ⟨1368553116274205117480251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29195799813849709172912021 1368553116274205117480251)
                    ·
                      rfl

theorem cell23_7995743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_7995743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995743 prefixEnd_7995743 := by exact prefixLift 7995743
  have htrace : WordTrace (prefixWord ++ tailWord_7995743) baseStart_7995743 baseEnd_7995743 := by
    simpa [prefixWord, tailWord_7995743, baseEnd_7995743] using wordTrace_append hprefix tailTrace_7995743
  have hstable : (prefixWord ++ tailWord_7995743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995743).length < 2 ^ (prefixWord ++ tailWord_7995743).sum := by decide
  have hdescent : baseEnd_7995743 < baseStart_7995743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995754 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7995754 : Nat := 118140960795 + 7995754 * 2 ^ 59
def prefixEnd_7995754 : Nat := 4983230072969 + 3 ^ 40 * 7995754 * 2
def baseEnd_7995754 : Nat := 4105664997109814809403203

theorem tailTrace_7995754 : CollatzResearch.WordTrace tailWord_7995754 prefixEnd_7995754 4105664997109814809403203 := by
  unfold tailWord_7995754
  simp only [CollatzResearch.WordTrace]
  refine ⟨72907276668689074727510579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194419404449837532606694877 72907276668689074727510579)
  ·
    refine ⟨109360915003033612091265869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72907276668689074727510579 109360915003033612091265869)
    ·
      refine ⟨41010343126137604534224701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109360915003033612091265869 41010343126137604534224701)
      ·
        refine ⟨15378878672301601700334263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41010343126137604534224701 15378878672301601700334263)
        ·
          refine ⟨23068318008452402550501395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378878672301601700334263 23068318008452402550501395)
          ·
            refine ⟨34602477012678603825752093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23068318008452402550501395 34602477012678603825752093)
            ·
              refine ⟨12975928879754476434657035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34602477012678603825752093 12975928879754476434657035)
              ·
                refine ⟨19463893319631714651985553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975928879754476434657035 19463893319631714651985553)
                ·
                  refine ⟨14597919989723785988989165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19463893319631714651985553 14597919989723785988989165)
                  ·
                    refine ⟨5474219996146419745870937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14597919989723785988989165 5474219996146419745870937)
                    ·
                      refine ⟨4105664997109814809403203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474219996146419745870937 4105664997109814809403203)
                      ·
                        rfl

theorem cell23_7995754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7995754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995754 prefixEnd_7995754 := by exact prefixLift 7995754
  have htrace : WordTrace (prefixWord ++ tailWord_7995754) baseStart_7995754 baseEnd_7995754 := by
    simpa [prefixWord, tailWord_7995754, baseEnd_7995754] using wordTrace_append hprefix tailTrace_7995754
  have hstable : (prefixWord ++ tailWord_7995754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995754).length < 2 ^ (prefixWord ++ tailWord_7995754).sum := by decide
  have hdescent : baseEnd_7995754 < baseStart_7995754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995773 : List Nat := [1, 4, 1, 1, 2, 4, 10]
def baseStart_7995773 : Nat := 118140960795 + 7995773 * 2 ^ 59
def prefixEnd_7995773 : Nat := 4983230072969 + 3 ^ 40 * 7995773 * 2
def baseEnd_7995773 : Nat := 50687342632620373272415

theorem tailTrace_7995773 : CollatzResearch.WordTrace tailWord_7995773 prefixEnd_7995773 50687342632620373272415 := by
  unfold tailWord_7995773
  simp only [CollatzResearch.WordTrace]
  refine ⟨291629799661687465154983973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194419866441124976769989315 291629799661687465154983973)
  ·
    refine ⟨54680587436566399716559495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291629799661687465154983973 54680587436566399716559495)
    ·
      refine ⟨82020881154849599574839243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54680587436566399716559495 82020881154849599574839243)
      ·
        refine ⟨123031321732274399362258865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82020881154849599574839243 123031321732274399362258865)
        ·
          refine ⟨92273491299205799521694149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123031321732274399362258865 92273491299205799521694149)
          ·
            refine ⟨17301279618601087410317653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92273491299205799521694149 17301279618601087410317653)
            ·
              refine ⟨50687342632620373272415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17301279618601087410317653 50687342632620373272415)
              ·
                rfl

theorem cell23_7995773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 10].length) (baseStart_7995773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995773 prefixEnd_7995773 := by exact prefixLift 7995773
  have htrace : WordTrace (prefixWord ++ tailWord_7995773) baseStart_7995773 baseEnd_7995773 := by
    simpa [prefixWord, tailWord_7995773, baseEnd_7995773] using wordTrace_append hprefix tailTrace_7995773
  have hstable : (prefixWord ++ tailWord_7995773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995773).length < 2 ^ (prefixWord ++ tailWord_7995773).sum := by decide
  have hdescent : baseEnd_7995773 < baseStart_7995773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995777 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7995777 : Nat := 118140960795 + 7995777 * 2 ^ 59
def prefixEnd_7995777 : Nat := 4983230072969 + 3 ^ 40 * 7995777 * 2
def baseEnd_7995777 : Nat := 1368558935721622739805199

theorem tailTrace_7995777 : CollatzResearch.WordTrace tailWord_7995777 prefixEnd_7995777 1368558935721622739805199 := by
  unfold tailWord_7995777
  simp only [CollatzResearch.WordTrace]
  refine ⟨291629945553672973838129585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194419963702448649225419723 291629945553672973838129585)
  ·
    refine ⟨218722459165254730378597189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291629945553672973838129585 218722459165254730378597189)
    ·
      refine ⟨41010461093485261945986973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218722459165254730378597189 41010461093485261945986973)
      ·
        refine ⟨15378922910056973229745115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41010461093485261945986973 15378922910056973229745115)
        ·
          refine ⟨23068384365085459844617673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378922910056973229745115 23068384365085459844617673)
          ·
            refine ⟨17301288273814094883463255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23068384365085459844617673 17301288273814094883463255)
            ·
              refine ⟨25951932410721142325194883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17301288273814094883463255 25951932410721142325194883)
              ·
                refine ⟨38927898616081713487792325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25951932410721142325194883 38927898616081713487792325)
                ·
                  refine ⟨7298980990515321278961061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38927898616081713487792325 7298980990515321278961061)
                  ·
                    refine ⟨1368558935721622739805199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298980990515321278961061 1368558935721622739805199)
                    ·
                      rfl

theorem cell23_7995777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7995777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995777 prefixEnd_7995777 := by exact prefixLift 7995777
  have htrace : WordTrace (prefixWord ++ tailWord_7995777) baseStart_7995777 baseEnd_7995777 := by
    simpa [prefixWord, tailWord_7995777, baseEnd_7995777] using wordTrace_append hprefix tailTrace_7995777
  have hstable : (prefixWord ++ tailWord_7995777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995777).length < 2 ^ (prefixWord ++ tailWord_7995777).sum := by decide
  have hdescent : baseEnd_7995777 < baseStart_7995777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995784 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7995784 : Nat := 118140960795 + 7995784 * 2 ^ 59
def prefixEnd_7995784 : Nat := 4983230072969 + 3 ^ 40 * 7995784 * 2
def baseEnd_7995784 : Nat := 4105680401529449692028065

theorem tailTrace_7995784 : CollatzResearch.WordTrace tailWord_7995784 prefixEnd_7995784 4105680401529449692028065 := by
  unfold tailWord_7995784
  simp only [CollatzResearch.WordTrace]
  refine ⟨145815100432323807016817203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194420133909765076022422937 145815100432323807016817203)
  ·
    refine ⟨218722650648485710525225805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145815100432323807016817203 218722650648485710525225805)
    ·
      refine ⟨82020993993182141446959677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218722650648485710525225805 82020993993182141446959677)
      ·
        refine ⟨30757872747443303042609879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82020993993182141446959677 30757872747443303042609879)
        ·
          refine ⟨46136809121164954563914819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30757872747443303042609879 46136809121164954563914819)
          ·
            refine ⟨69205213681747431845872229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46136809121164954563914819 69205213681747431845872229)
            ·
              refine ⟨12975977565327643471101043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69205213681747431845872229 12975977565327643471101043)
              ·
                refine ⟨19463966347991465206651565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975977565327643471101043 19463966347991465206651565)
                ·
                  refine ⟨7298987380496799452494337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19463966347991465206651565 7298987380496799452494337)
                  ·
                    refine ⟨5474240535372599589370753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7298987380496799452494337 5474240535372599589370753)
                    ·
                      refine ⟨4105680401529449692028065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474240535372599589370753 4105680401529449692028065)
                      ·
                        rfl

theorem cell23_7995784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7995784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995784 prefixEnd_7995784 := by exact prefixLift 7995784
  have htrace : WordTrace (prefixWord ++ tailWord_7995784) baseStart_7995784 baseEnd_7995784 := by
    simpa [prefixWord, tailWord_7995784, baseEnd_7995784] using wordTrace_append hprefix tailTrace_7995784
  have hstable : (prefixWord ++ tailWord_7995784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995784).length < 2 ^ (prefixWord ++ tailWord_7995784).sum := by decide
  have hdescent : baseEnd_7995784 < baseStart_7995784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995798 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7995798 : Nat := 118140960795 + 7995798 * 2 ^ 59
def prefixEnd_7995798 : Nat := 4983230072969 + 3 ^ 40 * 7995798 * 2
def baseEnd_7995798 : Nat := 1368562530086204212417667

theorem tailTrace_7995798 : CollatzResearch.WordTrace tailWord_7995798 prefixEnd_7995798 1368562530086204212417667 := by
  unfold tailWord_7995798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226919467912305901540253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194420474324397929616429365 18226919467912305901540253)
  ·
    refine ⟨6835094800467114713077595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18226919467912305901540253 6835094800467114713077595)
    ·
      refine ⟨10252642200700672069616393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835094800467114713077595 10252642200700672069616393)
      ·
        refine ⟨7689481650525504052212295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10252642200700672069616393 7689481650525504052212295)
        ·
          refine ⟨11534222475788256078318443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689481650525504052212295 11534222475788256078318443)
          ·
            refine ⟨17301333713682384117477665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534222475788256078318443 17301333713682384117477665)
            ·
              refine ⟨12976000285261788088108249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301333713682384117477665 12976000285261788088108249)
              ·
                refine ⟨9732000213946341066081187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12976000285261788088108249 9732000213946341066081187)
                ·
                  refine ⟨14598000320919511599121781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9732000213946341066081187 14598000320919511599121781)
                  ·
                    refine ⟨1368562530086204212417667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14598000320919511599121781 1368562530086204212417667)
                    ·
                      rfl

theorem cell23_7995798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7995798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995798 prefixEnd_7995798 := by exact prefixLift 7995798
  have htrace : WordTrace (prefixWord ++ tailWord_7995798) baseStart_7995798 baseEnd_7995798 := by
    simpa [prefixWord, tailWord_7995798, baseEnd_7995798] using wordTrace_append hprefix tailTrace_7995798
  have hstable : (prefixWord ++ tailWord_7995798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995798).length < 2 ^ (prefixWord ++ tailWord_7995798).sum := by decide
  have hdescent : baseEnd_7995798 < baseStart_7995798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995813 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_7995813 : Nat := 118140960795 + 7995813 * 2 ^ 59
def prefixEnd_7995813 : Nat := 4983230072969 + 3 ^ 40 * 7995813 * 2
def baseEnd_7995813 : Nat := 4105695292468430078565431

theorem tailTrace_7995813 : CollatzResearch.WordTrace tailWord_7995813 prefixEnd_7995813 4105695292468430078565431 := by
  unfold tailWord_7995813
  simp only [CollatzResearch.WordTrace]
  refine ⟨291631258581542551986440093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194420839054361701324293395 291631258581542551986440093)
  ·
    refine ⟨109361721968078456994915035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291631258581542551986440093 109361721968078456994915035)
    ·
      refine ⟨164042582952117685492372553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109361721968078456994915035 164042582952117685492372553)
      ·
        refine ⟨123031937214088264119279415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164042582952117685492372553 123031937214088264119279415)
        ·
          refine ⟨184547905821132396178919123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123031937214088264119279415 184547905821132396178919123)
          ·
            refine ⟨276821858731698594268378685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184547905821132396178919123 276821858731698594268378685)
            ·
              refine ⟨103808197024386972850642007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276821858731698594268378685 103808197024386972850642007)
              ·
                refine ⟨155712295536580459275963011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103808197024386972850642007 155712295536580459275963011)
                ·
                  refine ⟨233568443304870688913944517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155712295536580459275963011 233568443304870688913944517)
                  ·
                    refine ⟨43794083119663254171364597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233568443304870688913944517 43794083119663254171364597)
                    ·
                      refine ⟨4105695292468430078565431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43794083119663254171364597 4105695292468430078565431)
                      ·
                        rfl

theorem cell23_7995813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_7995813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995813 prefixEnd_7995813 := by exact prefixLift 7995813
  have htrace : WordTrace (prefixWord ++ tailWord_7995813) baseStart_7995813 baseEnd_7995813 := by
    simpa [prefixWord, tailWord_7995813, baseEnd_7995813] using wordTrace_append hprefix tailTrace_7995813
  have hstable : (prefixWord ++ tailWord_7995813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995813).length < 2 ^ (prefixWord ++ tailWord_7995813).sum := by decide
  have hdescent : baseEnd_7995813 < baseStart_7995813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995823 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_7995823 : Nat := 118140960795 + 7995823 * 2 ^ 59
def prefixEnd_7995823 : Nat := 4983230072969 + 3 ^ 40 * 7995823 * 2
def baseEnd_7995823 : Nat := 4105700427274975039440385

theorem tailTrace_7995823 : CollatzResearch.WordTrace tailWord_7995823 prefixEnd_7995823 4105700427274975039440385 := by
  unfold tailWord_7995823
  simp only [CollatzResearch.WordTrace]
  refine ⟨291631623311506323694304123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194421082207670882462869415 291631623311506323694304123)
  ·
    refine ⟨437447434967259485541456185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291631623311506323694304123 437447434967259485541456185)
    ·
      refine ⟨328085576225444614156092139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437447434967259485541456185 328085576225444614156092139)
      ·
        refine ⟨492128364338166921234138209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328085576225444614156092139 492128364338166921234138209)
        ·
          refine ⟨369096273253625190925603657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492128364338166921234138209 369096273253625190925603657)
          ·
            refine ⟨276822204940218893194202743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369096273253625190925603657 276822204940218893194202743)
            ·
              refine ⟨415233307410328339791304115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276822204940218893194202743 415233307410328339791304115)
              ·
                refine ⟨622849961115492509686956173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415233307410328339791304115 622849961115492509686956173)
                ·
                  refine ⟨233568735418309691132608565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622849961115492509686956173 233568735418309691132608565)
                  ·
                    refine ⟨21897068945466533543682053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233568735418309691132608565 21897068945466533543682053)
                    ·
                      refine ⟨4105700427274975039440385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21897068945466533543682053 4105700427274975039440385)
                      ·
                        rfl

theorem cell23_7995823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_7995823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995823 prefixEnd_7995823 := by exact prefixLift 7995823
  have htrace : WordTrace (prefixWord ++ tailWord_7995823) baseStart_7995823 baseEnd_7995823 := by
    simpa [prefixWord, tailWord_7995823, baseEnd_7995823] using wordTrace_append hprefix tailTrace_7995823
  have hstable : (prefixWord ++ tailWord_7995823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995823).length < 2 ^ (prefixWord ++ tailWord_7995823).sum := by decide
  have hdescent : baseEnd_7995823 < baseStart_7995823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995843 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_7995843 : Nat := 118140960795 + 7995843 * 2 ^ 59
def prefixEnd_7995843 : Nat := 4983230072969 + 3 ^ 40 * 7995843 * 2
def baseEnd_7995843 : Nat := 4105710696888064961190293

theorem tailTrace_7995843 : CollatzResearch.WordTrace tailWord_7995843 prefixEnd_7995843 4105710696888064961190293 := by
  unfold tailWord_7995843
  simp only [CollatzResearch.WordTrace]
  refine ⟨291632352771433867110032183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194421568514289244740021455 291632352771433867110032183)
  ·
    refine ⟨437448529157150800665048275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291632352771433867110032183 437448529157150800665048275)
    ·
      refine ⟨656172793735726200997572413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437448529157150800665048275 656172793735726200997572413)
      ·
        refine ⟨246064797650897325374089655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656172793735726200997572413 246064797650897325374089655)
        ·
          refine ⟨369097196476345988061134483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246064797650897325374089655 369097196476345988061134483)
          ·
            refine ⟨553645794714518982091701725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369097196476345988061134483 553645794714518982091701725)
            ·
              refine ⟨207617173017944618284388147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553645794714518982091701725 207617173017944618284388147)
              ·
                refine ⟨311425759526916927426582221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207617173017944618284388147 311425759526916927426582221)
                ·
                  refine ⟨116784659822593847784968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311425759526916927426582221 116784659822593847784968333)
                  ·
                    refine ⟨43794247433472692919363125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116784659822593847784968333 43794247433472692919363125)
                    ·
                      refine ⟨4105710696888064961190293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43794247433472692919363125 4105710696888064961190293)
                      ·
                        rfl

theorem cell23_7995843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_7995843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995843 prefixEnd_7995843 := by exact prefixLift 7995843
  have htrace : WordTrace (prefixWord ++ tailWord_7995843) baseStart_7995843 baseEnd_7995843 := by
    simpa [prefixWord, tailWord_7995843, baseEnd_7995843] using wordTrace_append hprefix tailTrace_7995843
  have hstable : (prefixWord ++ tailWord_7995843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995843).length < 2 ^ (prefixWord ++ tailWord_7995843).sum := by decide
  have hdescent : baseEnd_7995843 < baseStart_7995843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995861 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7995861 : Nat := 118140960795 + 7995861 * 2 ^ 59
def prefixEnd_7995861 : Nat := 4983230072969 + 3 ^ 40 * 7995861 * 2
def baseEnd_7995861 : Nat := 4105719939539845890765211

theorem tailTrace_7995861 : CollatzResearch.WordTrace tailWord_7995861 prefixEnd_7995861 4105719939539845890765211 := by
  unfold tailWord_7995861
  simp only [CollatzResearch.WordTrace]
  refine ⟨291633009285368656184187437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194422006190245770789458291 291633009285368656184187437)
  ·
    refine ⟨109362378482013246069070289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291633009285368656184187437 109362378482013246069070289)
    ·
      refine ⟨82021783861509934551802717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109362378482013246069070289 82021783861509934551802717)
      ·
        refine ⟨30758168948066225456926019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82021783861509934551802717 30758168948066225456926019)
        ·
          refine ⟨46137253422099338185389029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30758168948066225456926019 46137253422099338185389029)
          ·
            refine ⟨8650735016643625909760443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46137253422099338185389029 8650735016643625909760443)
            ·
              refine ⟨12976102524965438864640665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650735016643625909760443 12976102524965438864640665)
              ·
                refine ⟨9732076893724079148480499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12976102524965438864640665 9732076893724079148480499)
                ·
                  refine ⟨14598115340586118722720749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9732076893724079148480499 14598115340586118722720749)
                  ·
                    refine ⟨5474293252719794521020281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14598115340586118722720749 5474293252719794521020281)
                    ·
                      refine ⟨4105719939539845890765211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474293252719794521020281 4105719939539845890765211)
                      ·
                        rfl

theorem cell23_7995861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7995861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995861 prefixEnd_7995861 := by exact prefixLift 7995861
  have htrace : WordTrace (prefixWord ++ tailWord_7995861) baseStart_7995861 baseEnd_7995861 := by
    simpa [prefixWord, tailWord_7995861, baseEnd_7995861] using wordTrace_append hprefix tailTrace_7995861
  have hstable : (prefixWord ++ tailWord_7995861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995861).length < 2 ^ (prefixWord ++ tailWord_7995861).sum := by decide
  have hdescent : baseEnd_7995861 < baseStart_7995861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995960 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_7995960 : Nat := 118140960795 + 7995960 * 2 ^ 59
def prefixEnd_7995960 : Nat := 4983230072969 + 3 ^ 40 * 7995960 * 2
def baseEnd_7995960 : Nat := 4105770774124641003427255

theorem tailTrace_7995960 : CollatzResearch.WordTrace tailWord_7995960 prefixEnd_7995960 4105770774124641003427255 := by
  unfold tailWord_7995960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145818310056004998046020667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194424413408006664061360889 145818310056004998046020667)
  ·
    refine ⟨218727465084007497069031001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145818310056004998046020667 218727465084007497069031001)
    ·
      refine ⟨164045598813005622801773251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218727465084007497069031001 164045598813005622801773251)
      ·
        refine ⟨246068398219508434202659877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164045598813005622801773251 246068398219508434202659877)
        ·
          refine ⟨46137824666157831412998727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246068398219508434202659877 46137824666157831412998727)
          ·
            refine ⟨69206736999236747119498091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46137824666157831412998727 69206736999236747119498091)
            ·
              refine ⟨103810105498855120679247137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69206736999236747119498091 103810105498855120679247137)
              ·
                refine ⟨77857579124141340509435353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103810105498855120679247137 77857579124141340509435353)
                ·
                  refine ⟨58393184343106005382076515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77857579124141340509435353 58393184343106005382076515)
                  ·
                    refine ⟨87589776514659008073114773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58393184343106005382076515 87589776514659008073114773)
                    ·
                      refine ⟨4105770774124641003427255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87589776514659008073114773 4105770774124641003427255)
                      ·
                        rfl

theorem cell23_7995960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_7995960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995960 prefixEnd_7995960 := by exact prefixLift 7995960
  have htrace : WordTrace (prefixWord ++ tailWord_7995960) baseStart_7995960 baseEnd_7995960 := by
    simpa [prefixWord, tailWord_7995960, baseEnd_7995960] using wordTrace_append hprefix tailTrace_7995960
  have hstable : (prefixWord ++ tailWord_7995960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995960).length < 2 ^ (prefixWord ++ tailWord_7995960).sum := by decide
  have hdescent : baseEnd_7995960 < baseStart_7995960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7995964 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_7995964 : Nat := 118140960795 + 7995964 * 2 ^ 59
def prefixEnd_7995964 : Nat := 4983230072969 + 3 ^ 40 * 7995964 * 2
def baseEnd_7995964 : Nat := 4105772828047258987777237

theorem tailTrace_7995964 : CollatzResearch.WordTrace tailWord_7995964 prefixEnd_7995964 4105772828047258987777237 := by
  unfold tailWord_7995964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145818383001997752387593473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194424510669330336516791297 145818383001997752387593473)
  ·
    refine ⟨109363787251498314290695105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145818383001997752387593473 109363787251498314290695105)
    ·
      refine ⟨82022840438623735718021329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109363787251498314290695105 82022840438623735718021329)
      ·
        refine ⟨61517130328967801788515997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82022840438623735718021329 61517130328967801788515997)
        ·
          refine ⟨23068923873362925670693499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61517130328967801788515997 23068923873362925670693499)
          ·
            refine ⟨34603385810044388506040249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23068923873362925670693499 34603385810044388506040249)
            ·
              refine ⟨25952539357533291379530187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34603385810044388506040249 25952539357533291379530187)
              ·
                refine ⟨38928809036299937069295281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25952539357533291379530187 38928809036299937069295281)
                ·
                  refine ⟨29196606777224952801971461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38928809036299937069295281 29196606777224952801971461)
                  ·
                    refine ⟨5474363770729678650369649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29196606777224952801971461 5474363770729678650369649)
                    ·
                      refine ⟨4105772828047258987777237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474363770729678650369649 4105772828047258987777237)
                      ·
                        rfl

theorem cell23_7995964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_7995964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7995964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7995964 prefixEnd_7995964 := by exact prefixLift 7995964
  have htrace : WordTrace (prefixWord ++ tailWord_7995964) baseStart_7995964 baseEnd_7995964 := by
    simpa [prefixWord, tailWord_7995964, baseEnd_7995964] using wordTrace_append hprefix tailTrace_7995964
  have hstable : (prefixWord ++ tailWord_7995964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7995964).length < 2 ^ (prefixWord ++ tailWord_7995964).sum := by decide
  have hdescent : baseEnd_7995964 < baseStart_7995964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7995964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996008 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_7996008 : Nat := 118140960795 + 7996008 * 2 ^ 59
def prefixEnd_7996008 : Nat := 4983230072969 + 3 ^ 40 * 7996008 * 2
def baseEnd_7996008 : Nat := 1368598473732018938542345

theorem tailTrace_7996008 : CollatzResearch.WordTrace tailWord_7996008 prefixEnd_7996008 1368598473732018938542345 := by
  unfold tailWord_7996008
  simp only [CollatzResearch.WordTrace]
  refine ⟨145819185407918050144894339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194425580543890733526525785 145819185407918050144894339)
  ·
    refine ⟨218728778111877075217341509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145819185407918050144894339 218728778111877075217341509)
    ·
      refine ⟨41011645895976951603251533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218728778111877075217341509 41011645895976951603251533)
      ·
        refine ⟨15379367210991356851219325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41011645895976951603251533 15379367210991356851219325)
        ·
          refine ⟨5767262704121758819207247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15379367210991356851219325 5767262704121758819207247)
          ·
            refine ⟨8650894056182638228810871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767262704121758819207247 8650894056182638228810871)
            ·
              refine ⟨12976341084273957343216307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650894056182638228810871 12976341084273957343216307)
              ·
                refine ⟨19464511626410936014824461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976341084273957343216307 19464511626410936014824461)
                ·
                  refine ⟨7299191859904101005559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19464511626410936014824461 7299191859904101005559173)
                  ·
                    refine ⟨1368598473732018938542345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299191859904101005559173 1368598473732018938542345)
                    ·
                      rfl

theorem cell23_7996008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_7996008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996008 prefixEnd_7996008 := by exact prefixLift 7996008
  have htrace : WordTrace (prefixWord ++ tailWord_7996008) baseStart_7996008 baseEnd_7996008 := by
    simpa [prefixWord, tailWord_7996008, baseEnd_7996008] using wordTrace_append hprefix tailTrace_7996008
  have hstable : (prefixWord ++ tailWord_7996008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996008).length < 2 ^ (prefixWord ++ tailWord_7996008).sum := by decide
  have hdescent : baseEnd_7996008 < baseStart_7996008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996081 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_7996081 : Nat := 118140960795 + 7996081 * 2 ^ 59
def prefixEnd_7996081 : Nat := 4983230072969 + 3 ^ 40 * 7996081 * 2
def baseEnd_7996081 : Nat := 1368610968427945010004733

theorem tailTrace_7996081 : CollatzResearch.WordTrace tailWord_7996081 prefixEnd_7996081 1368610968427945010004733 := by
  unfold tailWord_7996081
  simp only [CollatzResearch.WordTrace]
  refine ⟨291641033344571633757196097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194427355563047755838130731 291641033344571633757196097)
  ·
    refine ⟨218730775008428725317897073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291641033344571633757196097 218730775008428725317897073)
    ·
      refine ⟨164048081256321543988422805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218730775008428725317897073 164048081256321543988422805)
      ·
        refine ⟨7689753808890072374457319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164048081256321543988422805 7689753808890072374457319)
        ·
          refine ⟨11534630713335108561685979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689753808890072374457319 11534630713335108561685979)
          ·
            refine ⟨17301946070002662842528969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534630713335108561685979 17301946070002662842528969)
            ·
              refine ⟨12976459552501997131896727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301946070002662842528969 12976459552501997131896727)
              ·
                refine ⟨19464689328752995697845091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976459552501997131896727 19464689328752995697845091)
                ·
                  refine ⟨29197033993129493546767637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19464689328752995697845091 29197033993129493546767637)
                  ·
                    refine ⟨1368610968427945010004733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29197033993129493546767637 1368610968427945010004733)
                    ·
                      rfl

theorem cell23_7996081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_7996081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996081 prefixEnd_7996081 := by exact prefixLift 7996081
  have htrace : WordTrace (prefixWord ++ tailWord_7996081) baseStart_7996081 baseEnd_7996081 := by
    simpa [prefixWord, tailWord_7996081, baseEnd_7996081] using wordTrace_append hprefix tailTrace_7996081
  have hstable : (prefixWord ++ tailWord_7996081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996081).length < 2 ^ (prefixWord ++ tailWord_7996081).sum := by decide
  have hdescent : baseEnd_7996081 < baseStart_7996081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996094 : List Nat := [4, 2, 1, 1, 2, 1, 5, 7]
def baseStart_7996094 : Nat := 118140960795 + 7996094 * 2 ^ 59
def prefixEnd_7996094 : Nat := 4983230072969 + 3 ^ 40 * 7996094 * 2
def baseEnd_7996094 : Nat := 152068132612309017746357

theorem tailTrace_7996094 : CollatzResearch.WordTrace tailWord_7996094 prefixEnd_7996094 152068132612309017746357 := by
  unfold tailWord_7996094
  simp only [CollatzResearch.WordTrace]
  refine ⟨36455188436690567122177417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194427671662349691318279557 36455188436690567122177417)
  ·
    refine ⟨27341391327517925341633063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36455188436690567122177417 27341391327517925341633063)
    ·
      refine ⟨41012086991276888012449595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27341391327517925341633063 41012086991276888012449595)
      ·
        refine ⟨61518130486915332018674393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41012086991276888012449595 61518130486915332018674393)
        ·
          refine ⟨46138597865186499014005795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61518130486915332018674393 46138597865186499014005795)
          ·
            refine ⟨69207896797779748521008693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46138597865186499014005795 69207896797779748521008693)
            ·
              refine ⟨6488240324791851423844565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69207896797779748521008693 6488240324791851423844565)
              ·
                refine ⟨152068132612309017746357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6488240324791851423844565 152068132612309017746357)
                ·
                  rfl

theorem cell23_7996094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_7996094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996094 prefixEnd_7996094 := by exact prefixLift 7996094
  have htrace : WordTrace (prefixWord ++ tailWord_7996094) baseStart_7996094 baseEnd_7996094 := by
    simpa [prefixWord, tailWord_7996094, baseEnd_7996094] using wordTrace_append hprefix tailTrace_7996094
  have hstable : (prefixWord ++ tailWord_7996094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996094).length < 2 ^ (prefixWord ++ tailWord_7996094).sum := by decide
  have hdescent : baseEnd_7996094 < baseStart_7996094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996102 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7996102 : Nat := 118140960795 + 7996102 * 2 ^ 59
def prefixEnd_7996102 : Nat := 4983230072969 + 3 ^ 40 * 7996102 * 2
def baseEnd_7996102 : Nat := 1368614562792526482617201

theorem tailTrace_7996102 : CollatzResearch.WordTrace tailWord_7996102 prefixEnd_7996102 1368614562792526482617201 := by
  unfold tailWord_7996102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113806227421736073240955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194427866184997036229140373 9113806227421736073240955)
  ·
    refine ⟨13670709341132604109861433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113806227421736073240955 13670709341132604109861433)
    ·
      refine ⟨10253032005849453082396075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13670709341132604109861433 10253032005849453082396075)
      ·
        refine ⟨15379548008774179623594113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253032005849453082396075 15379548008774179623594113)
        ·
          refine ⟨11534661006580634717695585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15379548008774179623594113 11534661006580634717695585)
          ·
            refine ⟨8650995754935476038271689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11534661006580634717695585 8650995754935476038271689)
            ·
              refine ⟨6488246816201607028703767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650995754935476038271689 6488246816201607028703767)
              ·
                refine ⟨9732370224302410543055651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488246816201607028703767 9732370224302410543055651)
                ·
                  refine ⟨14598555336453615814583477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9732370224302410543055651 14598555336453615814583477)
                  ·
                    refine ⟨1368614562792526482617201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14598555336453615814583477 1368614562792526482617201)
                    ·
                      rfl

theorem cell23_7996102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7996102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996102 prefixEnd_7996102 := by exact prefixLift 7996102
  have htrace : WordTrace (prefixWord ++ tailWord_7996102) baseStart_7996102 baseEnd_7996102 := by
    simpa [prefixWord, tailWord_7996102, baseEnd_7996102] using wordTrace_append hprefix tailTrace_7996102
  have hstable : (prefixWord ++ tailWord_7996102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996102).length < 2 ^ (prefixWord ++ tailWord_7996102).sum := by decide
  have hdescent : baseEnd_7996102 < baseStart_7996102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996104 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_7996104 : Nat := 118140960795 + 7996104 * 2 ^ 59
def prefixEnd_7996104 : Nat := 4983230072969 + 3 ^ 40 * 7996104 * 2
def baseEnd_7996104 : Nat := 4105844715338888440026593

theorem tailTrace_7996104 : CollatzResearch.WordTrace tailWord_7996104 prefixEnd_7996104 4105844715338888440026593 := by
  unfold tailWord_7996104
  simp only [CollatzResearch.WordTrace]
  refine ⟨145820936111744154342641683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194427914815658872456855577 145820936111744154342641683)
  ·
    refine ⟨218731404167616231513962525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145820936111744154342641683 218731404167616231513962525)
    ·
      refine ⟨82024276562856086817735947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218731404167616231513962525 82024276562856086817735947)
      ·
        refine ⟨123036414844284130226603921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82024276562856086817735947 123036414844284130226603921)
        ·
          refine ⟨92277311133213097669952941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123036414844284130226603921 92277311133213097669952941)
          ·
            refine ⟨34603991674954911626232353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92277311133213097669952941 34603991674954911626232353)
            ·
              refine ⟨25952993756216183719674265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34603991674954911626232353 25952993756216183719674265)
              ·
                refine ⟨19464745317162137789755699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25952993756216183719674265 19464745317162137789755699)
                ·
                  refine ⟨29197117975743206684633549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19464745317162137789755699 29197117975743206684633549)
                  ·
                    refine ⟨10948919240903702506737581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29197117975743206684633549 10948919240903702506737581)
                    ·
                      refine ⟨4105844715338888440026593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948919240903702506737581 4105844715338888440026593)
                      ·
                        rfl

theorem cell23_7996104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_7996104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996104 prefixEnd_7996104 := by exact prefixLift 7996104
  have htrace : WordTrace (prefixWord ++ tailWord_7996104) baseStart_7996104 baseEnd_7996104 := by
    simpa [prefixWord, tailWord_7996104, baseEnd_7996104] using wordTrace_append hprefix tailTrace_7996104
  have hstable : (prefixWord ++ tailWord_7996104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996104).length < 2 ^ (prefixWord ++ tailWord_7996104).sum := by decide
  have hdescent : baseEnd_7996104 < baseStart_7996104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996108 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7996108 : Nat := 118140960795 + 7996108 * 2 ^ 59
def prefixEnd_7996108 : Nat := 4983230072969 + 3 ^ 40 * 7996108 * 2
def baseEnd_7996108 : Nat := 4105846769261506424376575

theorem tailTrace_7996108 : CollatzResearch.WordTrace tailWord_7996108 prefixEnd_7996108 4105846769261506424376575 := by
  unfold tailWord_7996108
  simp only [CollatzResearch.WordTrace]
  refine ⟨145821009057736908684214489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194428012076982544912285985 145821009057736908684214489)
  ·
    refine ⟨109365756793302681513160867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145821009057736908684214489 109365756793302681513160867)
    ·
      refine ⟨164048635189954022269741301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109365756793302681513160867 164048635189954022269741301)
      ·
        refine ⟨15379559549058189587788247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164048635189954022269741301 15379559549058189587788247)
        ·
          refine ⟨23069339323587284381682371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15379559549058189587788247 23069339323587284381682371)
          ·
            refine ⟨34604008985380926572523557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23069339323587284381682371 34604008985380926572523557)
            ·
              refine ⟨6488251684758923732348167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34604008985380926572523557 6488251684758923732348167)
              ·
                refine ⟨9732377527138385598522251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488251684758923732348167 9732377527138385598522251)
                ·
                  refine ⟨14598566290707578397783377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9732377527138385598522251 14598566290707578397783377)
                  ·
                    refine ⟨10948924718030683798337533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14598566290707578397783377 10948924718030683798337533)
                    ·
                      refine ⟨4105846769261506424376575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10948924718030683798337533 4105846769261506424376575)
                      ·
                        rfl

theorem cell23_7996108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7996108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996108 prefixEnd_7996108 := by exact prefixLift 7996108
  have htrace : WordTrace (prefixWord ++ tailWord_7996108) baseStart_7996108 baseEnd_7996108 := by
    simpa [prefixWord, tailWord_7996108, baseEnd_7996108] using wordTrace_append hprefix tailTrace_7996108
  have hstable : (prefixWord ++ tailWord_7996108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996108).length < 2 ^ (prefixWord ++ tailWord_7996108).sum := by decide
  have hdescent : baseEnd_7996108 < baseStart_7996108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996137 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_7996137 : Nat := 118140960795 + 7996137 * 2 ^ 59
def prefixEnd_7996137 : Nat := 4983230072969 + 3 ^ 40 * 7996137 * 2
def baseEnd_7996137 : Nat := 1368620553400162270304647

theorem tailTrace_7996137 : CollatzResearch.WordTrace tailWord_7996137 prefixEnd_7996137 1368620553400162270304647 := by
  unfold tailWord_7996137
  simp only [CollatzResearch.WordTrace]
  refine ⟨291643075832368755321234665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194428717221579170214156443 291643075832368755321234665)
  ·
    refine ⟨218732306874276566490925999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291643075832368755321234665 218732306874276566490925999)
    ·
      refine ⟨328098460311414849736388999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218732306874276566490925999 328098460311414849736388999)
      ·
        refine ⟨492147690467122274604583499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328098460311414849736388999 492147690467122274604583499)
        ·
          refine ⟨738221535700683411906875249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492147690467122274604583499 738221535700683411906875249)
          ·
            refine ⟨553666151775512558930156437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738221535700683411906875249 553666151775512558930156437)
            ·
              refine ⟨25953100864477151199851083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553666151775512558930156437 25953100864477151199851083)
              ·
                refine ⟨38929651296715726799776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25953100864477151199851083 38929651296715726799776625)
                ·
                  refine ⟨29197238472536795099832469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38929651296715726799776625 29197238472536795099832469)
                  ·
                    refine ⟨1368620553400162270304647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29197238472536795099832469 1368620553400162270304647)
                    ·
                      rfl

theorem cell23_7996137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_7996137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996137 prefixEnd_7996137 := by exact prefixLift 7996137
  have htrace : WordTrace (prefixWord ++ tailWord_7996137) baseStart_7996137 baseEnd_7996137 := by
    simpa [prefixWord, tailWord_7996137, baseEnd_7996137] using wordTrace_append hprefix tailTrace_7996137
  have hstable : (prefixWord ++ tailWord_7996137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996137).length < 2 ^ (prefixWord ++ tailWord_7996137).sum := by decide
  have hdescent : baseEnd_7996137 < baseStart_7996137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996147 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_7996147 : Nat := 118140960795 + 7996147 * 2 ^ 59
def prefixEnd_7996147 : Nat := 4983230072969 + 3 ^ 40 * 7996147 * 2
def baseEnd_7996147 : Nat := 4105866795007031771788895

theorem tailTrace_7996147 : CollatzResearch.WordTrace tailWord_7996147 prefixEnd_7996147 4105866795007031771788895 := by
  unfold tailWord_7996147
  simp only [CollatzResearch.WordTrace]
  refine ⟨291643440562332527029098695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194428960374888351352732463 291643440562332527029098695)
  ·
    refine ⟨437465160843498790543648043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291643440562332527029098695 437465160843498790543648043)
    ·
      refine ⟨656197741265248185815472065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437465160843498790543648043 656197741265248185815472065)
      ·
        refine ⟨492148305948936139361604049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656197741265248185815472065 492148305948936139361604049)
        ·
          refine ⟨369111229461702104521203037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492148305948936139361604049 369111229461702104521203037)
          ·
            refine ⟨138416711048138289195451139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369111229461702104521203037 138416711048138289195451139)
            ·
              refine ⟨207625066572207433793176709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138416711048138289195451139 207625066572207433793176709)
              ·
                refine ⟨38929699982288893836220633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207625066572207433793176709 38929699982288893836220633)
                ·
                  refine ⟨29197274986716670377165475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38929699982288893836220633 29197274986716670377165475)
                  ·
                    refine ⟨43795912480075005565748213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29197274986716670377165475 43795912480075005565748213)
                    ·
                      refine ⟨4105866795007031771788895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43795912480075005565748213 4105866795007031771788895)
                      ·
                        rfl

theorem cell23_7996147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_7996147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996147 prefixEnd_7996147 := by exact prefixLift 7996147
  have htrace : WordTrace (prefixWord ++ tailWord_7996147) baseStart_7996147 baseEnd_7996147 := by
    simpa [prefixWord, tailWord_7996147, baseEnd_7996147] using wordTrace_append hprefix tailTrace_7996147
  have hstable : (prefixWord ++ tailWord_7996147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996147).length < 2 ^ (prefixWord ++ tailWord_7996147).sum := by decide
  have hdescent : baseEnd_7996147 < baseStart_7996147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996164 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7996164 : Nat := 118140960795 + 7996164 * 2 ^ 59
def prefixEnd_7996164 : Nat := 4983230072969 + 3 ^ 40 * 7996164 * 2
def baseEnd_7996164 : Nat := 4105875524178158205276317

theorem tailTrace_7996164 : CollatzResearch.WordTrace tailWord_7996164 prefixEnd_7996164 4105875524178158205276317 := by
  unfold tailWord_7996164
  simp only [CollatzResearch.WordTrace]
  refine ⟨145822030301635469466233773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194429373735513959288311697 145822030301635469466233773)
  ·
    refine ⟨54683261363113301049837665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145822030301635469466233773 54683261363113301049837665)
    ·
      refine ⟨41012446022334975787378249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54683261363113301049837665 41012446022334975787378249)
      ·
        refine ⟨30759334516751231840533687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41012446022334975787378249 30759334516751231840533687)
        ·
          refine ⟨46139001775126847760800531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30759334516751231840533687 46139001775126847760800531)
          ·
            refine ⟨69208502662690271641200797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46139001775126847760800531 69208502662690271641200797)
            ·
              refine ⟨25953188498508851865450299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69208502662690271641200797 25953188498508851865450299)
              ·
                refine ⟨38929782747763277798175449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25953188498508851865450299 38929782747763277798175449)
                ·
                  refine ⟨29197337060822458348631587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38929782747763277798175449 29197337060822458348631587)
                  ·
                    refine ⟨43796005591233687522947381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29197337060822458348631587 43796005591233687522947381)
                    ·
                      refine ⟨4105875524178158205276317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43796005591233687522947381 4105875524178158205276317)
                      ·
                        rfl

theorem cell23_7996164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7996164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996164 prefixEnd_7996164 := by exact prefixLift 7996164
  have htrace : WordTrace (prefixWord ++ tailWord_7996164) baseStart_7996164 baseEnd_7996164 := by
    simpa [prefixWord, tailWord_7996164, baseEnd_7996164] using wordTrace_append hprefix tailTrace_7996164
  have hstable : (prefixWord ++ tailWord_7996164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996164).length < 2 ^ (prefixWord ++ tailWord_7996164).sum := by decide
  have hdescent : baseEnd_7996164 < baseStart_7996164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996189 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7996189 : Nat := 118140960795 + 7996189 * 2 ^ 59
def prefixEnd_7996189 : Nat := 4983230072969 + 3 ^ 40 * 7996189 * 2
def baseEnd_7996189 : Nat := 4105888361194520607463703

theorem tailTrace_7996189 : CollatzResearch.WordTrace tailWord_7996189 prefixEnd_7996189 4105888361194520607463703 := by
  unfold tailWord_7996189
  simp only [CollatzResearch.WordTrace]
  refine ⟨291644972428180368202127621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194429981618786912134751747 291644972428180368202127621)
  ·
    refine ⟨54683432330283819037898929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291644972428180368202127621 54683432330283819037898929)
    ·
      refine ⟨41012574247712864278424197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54683432330283819037898929 41012574247712864278424197)
      ·
        refine ⟨7689857671446162052204537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41012574247712864278424197 7689857671446162052204537)
        ·
          refine ⟨5767393253584621539153403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7689857671446162052204537 5767393253584621539153403)
          ·
            refine ⟨8651089880376932308730105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767393253584621539153403 8651089880376932308730105)
            ·
              refine ⟨6488317410282699231547579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651089880376932308730105 6488317410282699231547579)
              ·
                refine ⟨9732476115424048847321369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488317410282699231547579 9732476115424048847321369)
                ·
                  refine ⟨7299357086568036635491027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9732476115424048847321369 7299357086568036635491027)
                  ·
                    refine ⟨10949035629852054953236541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7299357086568036635491027 10949035629852054953236541)
                    ·
                      refine ⟨4105888361194520607463703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949035629852054953236541 4105888361194520607463703)
                      ·
                        rfl

theorem cell23_7996189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7996189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996189 prefixEnd_7996189 := by exact prefixLift 7996189
  have htrace : WordTrace (prefixWord ++ tailWord_7996189) baseStart_7996189 baseEnd_7996189 := by
    simpa [prefixWord, tailWord_7996189, baseEnd_7996189] using wordTrace_append hprefix tailTrace_7996189
  have hstable : (prefixWord ++ tailWord_7996189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996189).length < 2 ^ (prefixWord ++ tailWord_7996189).sum := by decide
  have hdescent : baseEnd_7996189 < baseStart_7996189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996207 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_7996207 : Nat := 118140960795 + 7996207 * 2 ^ 59
def prefixEnd_7996207 : Nat := 4983230072969 + 3 ^ 40 * 7996207 * 2
def baseEnd_7996207 : Nat := 4105897603846301537038619

theorem tailTrace_7996207 : CollatzResearch.WordTrace tailWord_7996207 prefixEnd_7996207 4105897603846301537038619 := by
  unfold tailWord_7996207
  simp only [CollatzResearch.WordTrace]
  refine ⟨291645628942115157276282875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194430419294743438184188583 291645628942115157276282875)
  ·
    refine ⟨437468443413172735914424313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291645628942115157276282875 437468443413172735914424313)
    ·
      refine ⟨328101332559879551935818235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437468443413172735914424313 328101332559879551935818235)
      ·
        refine ⟨492151998839819327903727353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328101332559879551935818235 492151998839819327903727353)
        ·
          refine ⟨369113999129864495927795515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492151998839819327903727353 369113999129864495927795515)
          ·
            refine ⟨553670998694796743891693273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369113999129864495927795515 553670998694796743891693273)
            ·
              refine ⟨415253249021097557918769955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553670998694796743891693273 415253249021097557918769955)
              ·
                refine ⟨622879873531646336878154933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415253249021097557918769955 622879873531646336878154933)
                ·
                  refine ⟨58394988143591844082327025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622879873531646336878154933 58394988143591844082327025)
                  ·
                    refine ⟨43796241107693883061745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58394988143591844082327025 43796241107693883061745269)
                    ·
                      refine ⟨4105897603846301537038619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43796241107693883061745269 4105897603846301537038619)
                      ·
                        rfl

theorem cell23_7996207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_7996207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996207 prefixEnd_7996207 := by exact prefixLift 7996207
  have htrace : WordTrace (prefixWord ++ tailWord_7996207) baseStart_7996207 baseEnd_7996207 := by
    simpa [prefixWord, tailWord_7996207, baseEnd_7996207] using wordTrace_append hprefix tailTrace_7996207
  have hstable : (prefixWord ++ tailWord_7996207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996207).length < 2 ^ (prefixWord ++ tailWord_7996207).sum := by decide
  have hdescent : baseEnd_7996207 < baseStart_7996207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996234 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_7996234 : Nat := 118140960795 + 7996234 * 2 ^ 59
def prefixEnd_7996234 : Nat := 4983230072969 + 3 ^ 40 * 7996234 * 2
def baseEnd_7996234 : Nat := 4105911467823972931400995

theorem tailTrace_7996234 : CollatzResearch.WordTrace tailWord_7996234 prefixEnd_7996234 4105911467823972931400995 := by
  unfold tailWord_7996234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72911653428254335221878939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194431075808678227258343837 72911653428254335221878939)
  ·
    refine ⟨109367480142381502832818409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72911653428254335221878939 109367480142381502832818409)
    ·
      refine ⟨82025610106786127124613807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109367480142381502832818409 82025610106786127124613807)
      ·
        refine ⟨123038415160179190686920711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82025610106786127124613807 123038415160179190686920711)
        ·
          refine ⟨184557622740268786030381067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123038415160179190686920711 184557622740268786030381067)
          ·
            refine ⟨276836434110403179045571601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184557622740268786030381067 276836434110403179045571601)
            ·
              refine ⟨207627325582802384284178701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276836434110403179045571601 207627325582802384284178701)
              ·
                refine ⟨77860247093550894106567013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207627325582802384284178701 77860247093550894106567013)
                ·
                  refine ⟨14598796330040792644981315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77860247093550894106567013 14598796330040792644981315)
                  ·
                    refine ⟨21898194495061188967471973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14598796330040792644981315 21898194495061188967471973)
                    ·
                      refine ⟨4105911467823972931400995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21898194495061188967471973 4105911467823972931400995)
                      ·
                        rfl

theorem cell23_7996234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_7996234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996234 prefixEnd_7996234 := by exact prefixLift 7996234
  have htrace : WordTrace (prefixWord ++ tailWord_7996234) baseStart_7996234 baseEnd_7996234 := by
    simpa [prefixWord, tailWord_7996234, baseEnd_7996234] using wordTrace_append hprefix tailTrace_7996234
  have hstable : (prefixWord ++ tailWord_7996234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996234).length < 2 ^ (prefixWord ++ tailWord_7996234).sum := by decide
  have hdescent : baseEnd_7996234 < baseStart_7996234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996284 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_7996284 : Nat := 118140960795 + 7996284 * 2 ^ 59
def prefixEnd_7996284 : Nat := 4983230072969 + 3 ^ 40 * 7996284 * 2
def baseEnd_7996284 : Nat := 4105937141856697735775765

theorem tailTrace_7996284 : CollatzResearch.WordTrace tailWord_7996284 prefixEnd_7996284 4105937141856697735775765 := by
  unfold tailWord_7996284
  simp only [CollatzResearch.WordTrace]
  refine ⟨145824218681418099713417953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194432291575224132951223937 145824218681418099713417953)
  ·
    refine ⟨109368164011063574785063465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145824218681418099713417953 109368164011063574785063465)
    ·
      refine ⟨82026123008297681088797599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109368164011063574785063465 82026123008297681088797599)
      ·
        refine ⟨123039184512446521633196399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82026123008297681088797599 123039184512446521633196399)
        ·
          refine ⟨184558776768669782449794599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123039184512446521633196399 184558776768669782449794599)
          ·
            refine ⟨276838165153004673674691899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184558776768669782449794599 276838165153004673674691899)
            ·
              refine ⟨415257247729507010512037849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276838165153004673674691899 415257247729507010512037849)
              ·
                refine ⟨311442935797130257884028387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415257247729507010512037849 311442935797130257884028387)
                ·
                  refine ⟨467164403695695386826042581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311442935797130257884028387 467164403695695386826042581)
                  ·
                    refine ⟨10949165711617860628735373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 467164403695695386826042581 10949165711617860628735373)
                    ·
                      refine ⟨4105937141856697735775765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949165711617860628735373 4105937141856697735775765)
                      ·
                        rfl

theorem cell23_7996284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_7996284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996284 prefixEnd_7996284 := by exact prefixLift 7996284
  have htrace : WordTrace (prefixWord ++ tailWord_7996284) baseStart_7996284 baseEnd_7996284 := by
    simpa [prefixWord, tailWord_7996284, baseEnd_7996284] using wordTrace_append hprefix tailTrace_7996284
  have hstable : (prefixWord ++ tailWord_7996284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996284).length < 2 ^ (prefixWord ++ tailWord_7996284).sum := by decide
  have hdescent : baseEnd_7996284 < baseStart_7996284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996308 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 6]
def baseStart_7996308 : Nat := 118140960795 + 7996308 * 2 ^ 59
def prefixEnd_7996308 : Nat := 4983230072969 + 3 ^ 40 * 7996308 * 2
def baseEnd_7996308 : Nat := 456216607265822849097295

theorem tailTrace_7996308 : CollatzResearch.WordTrace tailWord_7996308 prefixEnd_7996308 456216607265822849097295 := by
  unfold tailWord_7996308
  simp only [CollatzResearch.WordTrace]
  refine ⟨145824656357374625762854789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194432875143166167683806385 145824656357374625762854789)
  ·
    refine ⟨27342123067007742330535273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145824656357374625762854789 27342123067007742330535273)
    ·
      refine ⟨20506592300255806747901455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27342123067007742330535273 20506592300255806747901455)
      ·
        refine ⟨30759888450383710121852183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506592300255806747901455 30759888450383710121852183)
        ·
          refine ⟨46139832675575565182778275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30759888450383710121852183 46139832675575565182778275)
          ·
            refine ⟨69209749013363347774167413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46139832675575565182778275 69209749013363347774167413)
            ·
              refine ⟨6488413970002813853828195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69209749013363347774167413 6488413970002813853828195)
              ·
                refine ⟨9732620955004220780742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488413970002813853828195 9732620955004220780742293)
                ·
                  refine ⟨456216607265822849097295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9732620955004220780742293 456216607265822849097295)
                  ·
                    rfl

theorem cell23_7996308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_7996308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996308 prefixEnd_7996308 := by exact prefixLift 7996308
  have htrace : WordTrace (prefixWord ++ tailWord_7996308) baseStart_7996308 baseEnd_7996308 := by
    simpa [prefixWord, tailWord_7996308, baseEnd_7996308] using wordTrace_append hprefix tailTrace_7996308
  have hstable : (prefixWord ++ tailWord_7996308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996308).length < 2 ^ (prefixWord ++ tailWord_7996308).sum := by decide
  have hdescent : baseEnd_7996308 < baseStart_7996308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996311 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7996311 : Nat := 118140960795 + 7996311 * 2 ^ 59
def prefixEnd_7996311 : Nat := 4983230072969 + 3 ^ 40 * 7996311 * 2
def baseEnd_7996311 : Nat := 4105951005834369130138141

theorem tailTrace_7996311 : CollatzResearch.WordTrace tailWord_7996311 prefixEnd_7996311 4105951005834369130138141 := by
  unfold tailWord_7996311
  simp only [CollatzResearch.WordTrace]
  refine ⟨291649422133738383038068787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194432948089158922025379191 291649422133738383038068787)
  ·
    refine ⟨437474133200607574557103181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291649422133738383038068787 437474133200607574557103181)
    ·
      refine ⟨164052799950227840458913693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437474133200607574557103181 164052799950227840458913693)
      ·
        refine ⟨61519799981335440172092635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164052799950227840458913693 61519799981335440172092635)
        ·
          refine ⟨92279699972003160258138953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61519799981335440172092635 92279699972003160258138953)
          ·
            refine ⟨69209774979002370193604215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92279699972003160258138953 69209774979002370193604215)
            ·
              refine ⟨103814662468503555290406323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69209774979002370193604215 103814662468503555290406323)
              ·
                refine ⟨155721993702755332935609485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103814662468503555290406323 155721993702755332935609485)
                ·
                  refine ⟨58395747638533249850853557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155721993702755332935609485 58395747638533249850853557)
                  ·
                    refine ⟨5474601341112492173517521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58395747638533249850853557 5474601341112492173517521)
                    ·
                      refine ⟨4105951005834369130138141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474601341112492173517521 4105951005834369130138141)
                      ·
                        rfl

theorem cell23_7996311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7996311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996311 prefixEnd_7996311 := by exact prefixLift 7996311
  have htrace : WordTrace (prefixWord ++ tailWord_7996311) baseStart_7996311 baseEnd_7996311 := by
    simpa [prefixWord, tailWord_7996311, baseEnd_7996311] using wordTrace_append hprefix tailTrace_7996311
  have hstable : (prefixWord ++ tailWord_7996311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996311).length < 2 ^ (prefixWord ++ tailWord_7996311).sum := by decide
  have hdescent : baseEnd_7996311 < baseStart_7996311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996352 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 1, 1, 3]
def baseStart_7996352 : Nat := 118140960795 + 7996352 * 2 ^ 59
def prefixEnd_7996352 : Nat := 4983230072969 + 3 ^ 40 * 7996352 * 2
def baseEnd_7996352 : Nat := 4105972058541203469725453

theorem tailTrace_7996352 : CollatzResearch.WordTrace tailWord_7996352 prefixEnd_7996352 4105972058541203469725453 := by
  unfold tailWord_7996352
  simp only [CollatzResearch.WordTrace]
  refine ⟨145825458763294923520155655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194433945017726564693540873 145825458763294923520155655)
  ·
    refine ⟨218738188144942385280233483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145825458763294923520155655 218738188144942385280233483)
    ·
      refine ⟨328107282217413577920350225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218738188144942385280233483 328107282217413577920350225)
      ·
        refine ⟨246080461663060183440262669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328107282217413577920350225 246080461663060183440262669)
        ·
          refine ⟨92280173123647568790098501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246080461663060183440262669 92280173123647568790098501)
          ·
            refine ⟨17302532460683919148143469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92280173123647568790098501 17302532460683919148143469)
            ·
              refine ⟨6488449672756469680553801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17302532460683919148143469 6488449672756469680553801)
              ·
                refine ⟨4866337254567352260415351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488449672756469680553801 4866337254567352260415351)
                ·
                  refine ⟨7299505881851028390623027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866337254567352260415351 7299505881851028390623027)
                  ·
                    refine ⟨10949258822776542585934541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7299505881851028390623027 10949258822776542585934541)
                    ·
                      refine ⟨4105972058541203469725453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949258822776542585934541 4105972058541203469725453)
                      ·
                        rfl

theorem cell23_7996352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_7996352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996352 prefixEnd_7996352 := by exact prefixLift 7996352
  have htrace : WordTrace (prefixWord ++ tailWord_7996352) baseStart_7996352 baseEnd_7996352 := by
    simpa [prefixWord, tailWord_7996352, baseEnd_7996352] using wordTrace_append hprefix tailTrace_7996352
  have hstable : (prefixWord ++ tailWord_7996352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996352).length < 2 ^ (prefixWord ++ tailWord_7996352).sum := by decide
  have hdescent : baseEnd_7996352 < baseStart_7996352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996378 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_7996378 : Nat := 118140960795 + 7996378 * 2 ^ 59
def prefixEnd_7996378 : Nat := 4983230072969 + 3 ^ 40 * 7996378 * 2
def baseEnd_7996378 : Nat := 4105985409038220368000333

theorem tailTrace_7996378 : CollatzResearch.WordTrace tailWord_7996378 prefixEnd_7996378 4105985409038220368000333 := by
  unfold tailWord_7996378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72912966456123913370189447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194434577216330435653838525 72912966456123913370189447)
  ·
    refine ⟨109369449684185870055284171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72912966456123913370189447 109369449684185870055284171)
    ·
      refine ⟨164054174526278805082926257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109369449684185870055284171 164054174526278805082926257)
      ·
        refine ⟨123040630894709103812194693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164054174526278805082926257 123040630894709103812194693)
        ·
          refine ⟨23070118292757956964786505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123040630894709103812194693 23070118292757956964786505)
          ·
            refine ⟨17302588719568467723589879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23070118292757956964786505 17302588719568467723589879)
            ·
              refine ⟨25953883079352701585384819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17302588719568467723589879 25953883079352701585384819)
              ·
                refine ⟨38930824619029052378077229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25953883079352701585384819 38930824619029052378077229)
                ·
                  refine ⟨14599059232135894641778961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38930824619029052378077229 14599059232135894641778961)
                  ·
                    refine ⟨10949294424101920981334221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14599059232135894641778961 10949294424101920981334221)
                    ·
                      refine ⟨4105985409038220368000333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949294424101920981334221 4105985409038220368000333)
                      ·
                        rfl

theorem cell23_7996378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_7996378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996378 prefixEnd_7996378 := by exact prefixLift 7996378
  have htrace : WordTrace (prefixWord ++ tailWord_7996378) baseStart_7996378 baseEnd_7996378 := by
    simpa [prefixWord, tailWord_7996378, baseEnd_7996378] using wordTrace_append hprefix tailTrace_7996378
  have hstable : (prefixWord ++ tailWord_7996378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996378).length < 2 ^ (prefixWord ++ tailWord_7996378).sum := by decide
  have hdescent : baseEnd_7996378 < baseStart_7996378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996381 : List Nat := [1, 4, 3, 1, 2, 1, 2, 9]
def baseStart_7996381 : Nat := 118140960795 + 7996381 * 2 ^ 59
def prefixEnd_7996381 : Nat := 4983230072969 + 3 ^ 40 * 7996381 * 2
def baseEnd_7996381 : Nat := 152073590721488290972697

theorem tailTrace_7996381 : CollatzResearch.WordTrace tailWord_7996381 prefixEnd_7996381 152073590721488290972697 := by
  unfold tailWord_7996381
  simp only [CollatzResearch.WordTrace]
  refine ⟨291651975243484784993116997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194434650162323189995411331 291651975243484784993116997)
  ·
    refine ⟨54684745358153397186209437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291651975243484784993116997 54684745358153397186209437)
    ·
      refine ⟨20506779509307523944828539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54684745358153397186209437 20506779509307523944828539)
      ·
        refine ⟨30760169263961285917242809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506779509307523944828539 30760169263961285917242809)
        ·
          refine ⟨23070126947970964437932107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30760169263961285917242809 23070126947970964437932107)
          ·
            refine ⟨34605190421956446656898161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23070126947970964437932107 34605190421956446656898161)
            ·
              refine ⟨25953892816467334992673621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34605190421956446656898161 25953892816467334992673621)
              ·
                refine ⟨152073590721488290972697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25953892816467334992673621 152073590721488290972697)
                ·
                  rfl

theorem cell23_7996381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 9].length) (baseStart_7996381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996381 prefixEnd_7996381 := by exact prefixLift 7996381
  have htrace : WordTrace (prefixWord ++ tailWord_7996381) baseStart_7996381 baseEnd_7996381 := by
    simpa [prefixWord, tailWord_7996381, baseEnd_7996381] using wordTrace_append hprefix tailTrace_7996381
  have hstable : (prefixWord ++ tailWord_7996381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996381).length < 2 ^ (prefixWord ++ tailWord_7996381).sum := by decide
  have hdescent : baseEnd_7996381 < baseStart_7996381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996402 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_7996402 : Nat := 118140960795 + 7996402 * 2 ^ 59
def prefixEnd_7996402 : Nat := 4983230072969 + 3 ^ 40 * 7996402 * 2
def baseEnd_7996402 : Nat := 1368665910857976091366741

theorem tailTrace_7996402 : CollatzResearch.WordTrace tailWord_7996402 prefixEnd_7996402 1368665910857976091366741 := by
  unfold tailWord_7996402
  simp only [CollatzResearch.WordTrace]
  refine ⟨72913185294102176394907865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194435160784272470386420973 72913185294102176394907865)
  ·
    refine ⟨54684888970576632296180899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72913185294102176394907865 54684888970576632296180899)
    ·
      refine ⟨82027333455864948444271349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54684888970576632296180899 82027333455864948444271349)
      ·
        refine ⟨7690062511487338916650439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82027333455864948444271349 7690062511487338916650439)
        ·
          refine ⟨11535093767231008374975659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690062511487338916650439 11535093767231008374975659)
          ·
            refine ⟨17302640650846512562463489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535093767231008374975659 17302640650846512562463489)
            ·
              refine ⟨12976980488134884421847617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17302640650846512562463489 12976980488134884421847617)
              ·
                refine ⟨9732735366101163316385713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12976980488134884421847617 9732735366101163316385713)
                ·
                  refine ⟨7299551524575872487289285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9732735366101163316385713 7299551524575872487289285)
                  ·
                    refine ⟨1368665910857976091366741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299551524575872487289285 1368665910857976091366741)
                    ·
                      rfl

theorem cell23_7996402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_7996402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996402 prefixEnd_7996402 := by exact prefixLift 7996402
  have htrace : WordTrace (prefixWord ++ tailWord_7996402) baseStart_7996402 baseEnd_7996402 := by
    simpa [prefixWord, tailWord_7996402, baseEnd_7996402] using wordTrace_append hprefix tailTrace_7996402
  have hstable : (prefixWord ++ tailWord_7996402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996402).length < 2 ^ (prefixWord ++ tailWord_7996402).sum := by decide
  have hdescent : baseEnd_7996402 < baseStart_7996402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996452 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7996452 : Nat := 118140960795 + 7996452 * 2 ^ 59
def prefixEnd_7996452 : Nat := 4983230072969 + 3 ^ 40 * 7996452 * 2
def baseEnd_7996452 : Nat := 4106023406606653078474993

theorem tailTrace_7996452 : CollatzResearch.WordTrace tailWord_7996452 prefixEnd_7996452 4106023406606653078474993 := by
  unfold tailWord_7996452
  simp only [CollatzResearch.WordTrace]
  refine ⟨145827282413113782059475805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194436376550818376079301073 145827282413113782059475805)
  ·
    refine ⟨54685230904917668272303427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145827282413113782059475805 54685230904917668272303427)
    ·
      refine ⟨82027846357376502408455141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54685230904917668272303427 82027846357376502408455141)
      ·
        refine ⟨15380221192008094201585339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82027846357376502408455141 15380221192008094201585339)
        ·
          refine ⟨23070331788012141302378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380221192008094201585339 23070331788012141302378009)
          ·
            refine ⟨17302748841009105976783507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23070331788012141302378009 17302748841009105976783507)
            ·
              refine ⟨25954123261513658965175261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17302748841009105976783507 25954123261513658965175261)
              ·
                refine ⟨9732796223067622111940723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25954123261513658965175261 9732796223067622111940723)
                ·
                  refine ⟨14599194334601433167911085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9732796223067622111940723 14599194334601433167911085)
                  ·
                    refine ⟨5474697875475537437966657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14599194334601433167911085 5474697875475537437966657)
                    ·
                      refine ⟨4106023406606653078474993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474697875475537437966657 4106023406606653078474993)
                      ·
                        rfl

theorem cell23_7996452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7996452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996452 prefixEnd_7996452 := by exact prefixLift 7996452
  have htrace : WordTrace (prefixWord ++ tailWord_7996452) baseStart_7996452 baseEnd_7996452 := by
    simpa [prefixWord, tailWord_7996452, baseEnd_7996452] using wordTrace_append hprefix tailTrace_7996452
  have hstable : (prefixWord ++ tailWord_7996452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996452).length < 2 ^ (prefixWord ++ tailWord_7996452).sum := by decide
  have hdescent : baseEnd_7996452 < baseStart_7996452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996465 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_7996465 : Nat := 118140960795 + 7996465 * 2 ^ 59
def prefixEnd_7996465 : Nat := 4983230072969 + 3 ^ 40 * 7996465 * 2
def baseEnd_7996465 : Nat := 4106030081855161527612433

theorem tailTrace_7996465 : CollatzResearch.WordTrace tailWord_7996465 prefixEnd_7996465 4106030081855161527612433 := by
  unfold tailWord_7996465
  simp only [CollatzResearch.WordTrace]
  refine ⟨291655038975180467339174849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194436692650120311559449899 291655038975180467339174849)
  ·
    refine ⟨218741279231385350504381137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291655038975180467339174849 218741279231385350504381137)
    ·
      refine ⟨164055959423539012878285853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218741279231385350504381137 164055959423539012878285853)
      ·
        refine ⟨61520984783827129829357195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164055959423539012878285853 61520984783827129829357195)
        ·
          refine ⟨92281477175740694744035793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61520984783827129829357195 92281477175740694744035793)
          ·
            refine ⟨69211107881805521058026845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92281477175740694744035793 69211107881805521058026845)
            ·
              refine ⟨25954165455677070396760067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69211107881805521058026845 25954165455677070396760067)
              ·
                refine ⟨38931248183515605595140101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25954165455677070396760067 38931248183515605595140101)
                ·
                  refine ⟨7299609034409176049088769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38931248183515605595140101 7299609034409176049088769)
                  ·
                    refine ⟨5474706775806882036816577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299609034409176049088769 5474706775806882036816577)
                    ·
                      refine ⟨4106030081855161527612433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474706775806882036816577 4106030081855161527612433)
                      ·
                        rfl

theorem cell23_7996465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_7996465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996465 prefixEnd_7996465 := by exact prefixLift 7996465
  have htrace : WordTrace (prefixWord ++ tailWord_7996465) baseStart_7996465 baseEnd_7996465 := by
    simpa [prefixWord, tailWord_7996465, baseEnd_7996465] using wordTrace_append hprefix tailTrace_7996465
  have hstable : (prefixWord ++ tailWord_7996465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996465).length < 2 ^ (prefixWord ++ tailWord_7996465).sum := by decide
  have hdescent : baseEnd_7996465 < baseStart_7996465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996501 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7996501 : Nat := 118140960795 + 7996501 * 2 ^ 59
def prefixEnd_7996501 : Nat := 4983230072969 + 3 ^ 40 * 7996501 * 2
def baseEnd_7996501 : Nat := 1368682855719574462254089

theorem tailTrace_7996501 : CollatzResearch.WordTrace tailWord_7996501 prefixEnd_7996501 1368682855719574462254089 := by
  unfold tailWord_7996501
  simp only [CollatzResearch.WordTrace]
  refine ⟨291656352003050045487485357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194437568002033363658323571 291656352003050045487485357)
  ·
    refine ⟨109371132001143767057807009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291656352003050045487485357 109371132001143767057807009)
    ·
      refine ⟨82028349000857825293355257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109371132001143767057807009 82028349000857825293355257)
      ·
        refine ⟨61521261750643368970016443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82028349000857825293355257 61521261750643368970016443)
        ·
          refine ⟨92281892625965053455024665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61521261750643368970016443 92281892625965053455024665)
          ·
            refine ⟨69211419469473790091268499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92281892625965053455024665 69211419469473790091268499)
            ·
              refine ⟨103817129204210685136902749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69211419469473790091268499 103817129204210685136902749)
              ·
                refine ⟨38931423451579006926338531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103817129204210685136902749 38931423451579006926338531)
                ·
                  refine ⟨58397135177368510389507797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38931423451579006926338531 58397135177368510389507797)
                  ·
                    refine ⟨1368682855719574462254089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58397135177368510389507797 1368682855719574462254089)
                    ·
                      rfl

theorem cell23_7996501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7996501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996501 prefixEnd_7996501 := by exact prefixLift 7996501
  have htrace : WordTrace (prefixWord ++ tailWord_7996501) baseStart_7996501 baseEnd_7996501 := by
    simpa [prefixWord, tailWord_7996501, baseEnd_7996501] using wordTrace_append hprefix tailTrace_7996501
  have hstable : (prefixWord ++ tailWord_7996501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996501).length < 2 ^ (prefixWord ++ tailWord_7996501).sum := by decide
  have hdescent : baseEnd_7996501 < baseStart_7996501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996502 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7996502 : Nat := 118140960795 + 7996502 * 2 ^ 59
def prefixEnd_7996502 : Nat := 4983230072969 + 3 ^ 40 * 7996502 * 2
def baseEnd_7996502 : Nat := 4106049080639377882849763

theorem tailTrace_7996502 : CollatzResearch.WordTrace tailWord_7996502 prefixEnd_7996502 4106049080639377882849763 := by
  unfold tailWord_7996502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228524279752901416141985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194437592317364281772181173 18228524279752901416141985)
  ·
    refine ⟨13671393209814676062106489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18228524279752901416141985 13671393209814676062106489)
    ·
      refine ⟨10253544907361007046579867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13671393209814676062106489 10253544907361007046579867)
      ·
        refine ⟨15380317361041510569869801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253544907361007046579867 15380317361041510569869801)
        ·
          refine ⟨11535238020781132927402351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15380317361041510569869801 11535238020781132927402351)
          ·
            refine ⟨17302857031171699391103527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535238020781132927402351 17302857031171699391103527)
            ·
              refine ⟨25954285546757549086655291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17302857031171699391103527 25954285546757549086655291)
              ·
                refine ⟨38931428320136323629982937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25954285546757549086655291 38931428320136323629982937)
                ·
                  refine ⟨29198571240102242722487203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38931428320136323629982937 29198571240102242722487203)
                  ·
                    refine ⟨43797856860153364083730805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29198571240102242722487203 43797856860153364083730805)
                    ·
                      refine ⟨4106049080639377882849763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43797856860153364083730805 4106049080639377882849763)
                      ·
                        rfl

theorem cell23_7996502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7996502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996502 prefixEnd_7996502 := by exact prefixLift 7996502
  have htrace : WordTrace (prefixWord ++ tailWord_7996502) baseStart_7996502 baseEnd_7996502 := by
    simpa [prefixWord, tailWord_7996502, baseEnd_7996502] using wordTrace_append hprefix tailTrace_7996502
  have hstable : (prefixWord ++ tailWord_7996502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996502).length < 2 ^ (prefixWord ++ tailWord_7996502).sum := by decide
  have hdescent : baseEnd_7996502 < baseStart_7996502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996511 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_7996511 : Nat := 118140960795 + 7996511 * 2 ^ 59
def prefixEnd_7996511 : Nat := 4983230072969 + 3 ^ 40 * 7996511 * 2
def baseEnd_7996511 : Nat := 4106053701965268347637221

theorem tailTrace_7996511 : CollatzResearch.WordTrace tailWord_7996511 prefixEnd_7996511 4106053701965268347637221 := by
  unfold tailWord_7996511
  simp only [CollatzResearch.WordTrace]
  refine ⟨291656716733013817195349387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194437811155342544796899591 291656716733013817195349387)
  ·
    refine ⟨437485075099520725793024081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291656716733013817195349387 437485075099520725793024081)
    ·
      refine ⟨328113806324640544344768061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437485075099520725793024081 328113806324640544344768061)
      ·
        refine ⟨123042677371740204129288023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328113806324640544344768061 123042677371740204129288023)
        ·
          refine ⟨184564016057610306193932035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123042677371740204129288023 184564016057610306193932035)
          ·
            refine ⟨276846024086415459290898053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184564016057610306193932035 276846024086415459290898053)
            ·
              refine ⟨51908629516202898617043385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276846024086415459290898053 51908629516202898617043385)
              ·
                refine ⟨38931472137152173962782539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51908629516202898617043385 38931472137152173962782539)
                ·
                  refine ⟨58397208205728260944173809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38931472137152173962782539 58397208205728260944173809)
                  ·
                    refine ⟨43797906154296195708130357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58397208205728260944173809 43797906154296195708130357)
                    ·
                      refine ⟨4106053701965268347637221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43797906154296195708130357 4106053701965268347637221)
                      ·
                        rfl

theorem cell23_7996511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_7996511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996511 prefixEnd_7996511 := by exact prefixLift 7996511
  have htrace : WordTrace (prefixWord ++ tailWord_7996511) baseStart_7996511 baseEnd_7996511 := by
    simpa [prefixWord, tailWord_7996511, baseEnd_7996511] using wordTrace_append hprefix tailTrace_7996511
  have hstable : (prefixWord ++ tailWord_7996511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996511).length < 2 ^ (prefixWord ++ tailWord_7996511).sum := by decide
  have hdescent : baseEnd_7996511 < baseStart_7996511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996522 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_7996522 : Nat := 118140960795 + 7996522 * 2 ^ 59
def prefixEnd_7996522 : Nat := 4983230072969 + 3 ^ 40 * 7996522 * 2
def baseEnd_7996522 : Nat := 456228816694718644955519

theorem tailTrace_7996522 : CollatzResearch.WordTrace tailWord_7996522 prefixEnd_7996522 456228816694718644955519 := by
  unfold tailWord_7996522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72914279483993491518499955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194438078623982644049333213 72914279483993491518499955)
  ·
    refine ⟨109371419225990237277749933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72914279483993491518499955 109371419225990237277749933)
    ·
      refine ⟨41014282209746338979156225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109371419225990237277749933 41014282209746338979156225)
      ·
        refine ⟨30760711657309754234367169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41014282209746338979156225 30760711657309754234367169)
        ·
          refine ⟨23070533742982315675775377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30760711657309754234367169 23070533742982315675775377)
          ·
            refine ⟨17302900307236736756831533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23070533742982315675775377 17302900307236736756831533)
            ·
              refine ⟨6488587615213776283811825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17302900307236736756831533 6488587615213776283811825)
              ·
                refine ⟨4866440711410332212858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488587615213776283811825 4866440711410332212858869)
                ·
                  refine ⟨456228816694718644955519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4866440711410332212858869 456228816694718644955519)
                  ·
                    rfl

theorem cell23_7996522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_7996522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996522 prefixEnd_7996522 := by exact prefixLift 7996522
  have htrace : WordTrace (prefixWord ++ tailWord_7996522) baseStart_7996522 baseEnd_7996522 := by
    simpa [prefixWord, tailWord_7996522, baseEnd_7996522] using wordTrace_append hprefix tailTrace_7996522
  have hstable : (prefixWord ++ tailWord_7996522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996522).length < 2 ^ (prefixWord ++ tailWord_7996522).sum := by decide
  have hdescent : baseEnd_7996522 < baseStart_7996522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996533 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7996533 : Nat := 118140960795 + 7996533 * 2 ^ 59
def prefixEnd_7996533 : Nat := 4983230072969 + 3 ^ 40 * 7996533 * 2
def baseEnd_7996533 : Nat := 4106064998539667261562121

theorem tailTrace_7996533 : CollatzResearch.WordTrace tailWord_7996533 prefixEnd_7996533 4106064998539667261562121 := by
  unfold tailWord_7996533
  simp only [CollatzResearch.WordTrace]
  refine ⟨291657519138934114952650253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194438346092622743301766835 291657519138934114952650253)
  ·
    refine ⟨109371569677100293107243845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291657519138934114952650253 109371569677100293107243845)
    ·
      refine ⟨20507169314456304957608221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109371569677100293107243845 20507169314456304957608221)
      ·
        refine ⟨7690188492921114359103083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20507169314456304957608221 7690188492921114359103083)
        ·
          refine ⟨11535282739381671538654625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690188492921114359103083 11535282739381671538654625)
          ·
            refine ⟨8651462054536253653990969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11535282739381671538654625 8651462054536253653990969)
            ·
              refine ⟨6488596540902190240493227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651462054536253653990969 6488596540902190240493227)
              ·
                refine ⟨9732894811353285360739841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488596540902190240493227 9732894811353285360739841)
                ·
                  refine ⟨7299671108514964020554881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9732894811353285360739841 7299671108514964020554881)
                  ·
                    refine ⟨5474753331386223015416161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299671108514964020554881 5474753331386223015416161)
                    ·
                      refine ⟨4106064998539667261562121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474753331386223015416161 4106064998539667261562121)
                      ·
                        rfl

theorem cell23_7996533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7996533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996533 prefixEnd_7996533 := by exact prefixLift 7996533
  have htrace : WordTrace (prefixWord ++ tailWord_7996533) baseStart_7996533 baseEnd_7996533 := by
    simpa [prefixWord, tailWord_7996533, baseEnd_7996533] using wordTrace_append hprefix tailTrace_7996533
  have hstable : (prefixWord ++ tailWord_7996533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996533).length < 2 ^ (prefixWord ++ tailWord_7996533).sum := by decide
  have hdescent : baseEnd_7996533 < baseStart_7996533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996551 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7996551 : Nat := 118140960795 + 7996551 * 2 ^ 59
def prefixEnd_7996551 : Nat := 4983230072969 + 3 ^ 40 * 7996551 * 2
def baseEnd_7996551 : Nat := 4106074241191448191137037

theorem tailTrace_7996551 : CollatzResearch.WordTrace tailWord_7996551 prefixEnd_7996551 4106074241191448191137037 := by
  unfold tailWord_7996551
  simp only [CollatzResearch.WordTrace]
  refine ⟨291658175652868904026805507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194438783768579269351203671 291658175652868904026805507)
  ·
    refine ⟨437487263479303356040208261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291658175652868904026805507 437487263479303356040208261)
    ·
      refine ⟨82028861902369379257539049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437487263479303356040208261 82028861902369379257539049)
      ·
        refine ⟨61521646426777034443154287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82028861902369379257539049 61521646426777034443154287)
        ·
          refine ⟨92282469640165551664731431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61521646426777034443154287 92282469640165551664731431)
          ·
            refine ⟨138423704460248327497097147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92282469640165551664731431 138423704460248327497097147)
            ·
              refine ⟨207635556690372491245645721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138423704460248327497097147 207635556690372491245645721)
              ·
                refine ⟨155726667517779368434234291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207635556690372491245645721 155726667517779368434234291)
                ·
                  refine ⟨233590001276669052651351437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155726667517779368434234291 233590001276669052651351437)
                  ·
                    refine ⟨87596250478750894744256789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233590001276669052651351437 87596250478750894744256789)
                    ·
                      refine ⟨4106074241191448191137037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87596250478750894744256789 4106074241191448191137037)
                      ·
                        rfl

theorem cell23_7996551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7996551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996551 prefixEnd_7996551 := by exact prefixLift 7996551
  have htrace : WordTrace (prefixWord ++ tailWord_7996551) baseStart_7996551 baseEnd_7996551 := by
    simpa [prefixWord, tailWord_7996551, baseEnd_7996551] using wordTrace_append hprefix tailTrace_7996551
  have hstable : (prefixWord ++ tailWord_7996551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996551).length < 2 ^ (prefixWord ++ tailWord_7996551).sum := by decide
  have hdescent : baseEnd_7996551 < baseStart_7996551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996605 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7996605 : Nat := 118140960795 + 7996605 * 2 ^ 59
def prefixEnd_7996605 : Nat := 4983230072969 + 3 ^ 40 * 7996605 * 2
def baseEnd_7996605 : Nat := 4106101969146790979861789

theorem tailTrace_7996605 : CollatzResearch.WordTrace tailWord_7996605 prefixEnd_7996605 4106101969146790979861789 := by
  unfold tailWord_7996605
  simp only [CollatzResearch.WordTrace]
  refine ⟨291660145194673271249271269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194440096796448847499514179 291660145194673271249271269)
  ·
    refine ⟨54686277224001238359238363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291660145194673271249271269 54686277224001238359238363)
    ·
      refine ⟨82029415836001857538857545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54686277224001238359238363 82029415836001857538857545)
      ·
        refine ⟨61522061877001393154143159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82029415836001857538857545 61522061877001393154143159)
        ·
          refine ⟨92283092815502089731214739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61522061877001393154143159 92283092815502089731214739)
          ·
            refine ⟨138424639223253134596822109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92283092815502089731214739 138424639223253134596822109)
            ·
              refine ⟨51909239708719925473808291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138424639223253134596822109 51909239708719925473808291)
              ·
                refine ⟨77863859563079888210712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51909239708719925473808291 77863859563079888210712437)
                ·
                  refine ⟨7299736834038739519754291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77863859563079888210712437 7299736834038739519754291)
                  ·
                    refine ⟨10949605251058109279631437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7299736834038739519754291 10949605251058109279631437)
                    ·
                      refine ⟨4106101969146790979861789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949605251058109279631437 4106101969146790979861789)
                      ·
                        rfl

theorem cell23_7996605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7996605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996605 prefixEnd_7996605 := by exact prefixLift 7996605
  have htrace : WordTrace (prefixWord ++ tailWord_7996605) baseStart_7996605 baseEnd_7996605 := by
    simpa [prefixWord, tailWord_7996605, baseEnd_7996605] using wordTrace_append hprefix tailTrace_7996605
  have hstable : (prefixWord ++ tailWord_7996605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996605).length < 2 ^ (prefixWord ++ tailWord_7996605).sum := by decide
  have hdescent : baseEnd_7996605 < baseStart_7996605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996609 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7996609 : Nat := 118140960795 + 7996609 * 2 ^ 59
def prefixEnd_7996609 : Nat := 4983230072969 + 3 ^ 40 * 7996609 * 2
def baseEnd_7996609 : Nat := 4106104023069408964211771

theorem tailTrace_7996609 : CollatzResearch.WordTrace tailWord_7996609 prefixEnd_7996609 4106104023069408964211771 := by
  unfold tailWord_7996609
  simp only [CollatzResearch.WordTrace]
  refine ⟨291660291086658779932416881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194440194057772519954944587 291660291086658779932416881)
  ·
    refine ⟨218745218314994084949312661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291660291086658779932416881 218745218314994084949312661)
    ·
      refine ⟨10253682108515347731999031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218745218314994084949312661 10253682108515347731999031)
      ·
        refine ⟨15380523162773021597998547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253682108515347731999031 15380523162773021597998547)
        ·
          refine ⟨23070784744159532396997821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380523162773021597998547 23070784744159532396997821)
          ·
            refine ⟨8651544279059824648874183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23070784744159532396997821 8651544279059824648874183)
            ·
              refine ⟨12977316418589736973311275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8651544279059824648874183 12977316418589736973311275)
              ·
                refine ⟨19465974627884605459966913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12977316418589736973311275 19465974627884605459966913)
                ·
                  refine ⟨14599480970913454094975185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19465974627884605459966913 14599480970913454094975185)
                  ·
                    refine ⟨10949610728185090571231389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14599480970913454094975185 10949610728185090571231389)
                    ·
                      refine ⟨4106104023069408964211771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949610728185090571231389 4106104023069408964211771)
                      ·
                        rfl

theorem cell23_7996609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7996609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996609 prefixEnd_7996609 := by exact prefixLift 7996609
  have htrace : WordTrace (prefixWord ++ tailWord_7996609) baseStart_7996609 baseEnd_7996609 := by
    simpa [prefixWord, tailWord_7996609, baseEnd_7996609] using wordTrace_append hprefix tailTrace_7996609
  have hstable : (prefixWord ++ tailWord_7996609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996609).length < 2 ^ (prefixWord ++ tailWord_7996609).sum := by decide
  have hdescent : baseEnd_7996609 < baseStart_7996609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996690 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7996690 : Nat := 118140960795 + 7996690 * 2 ^ 59
def prefixEnd_7996690 : Nat := 4983230072969 + 3 ^ 40 * 7996690 * 2
def baseEnd_7996690 : Nat := 4106145615002423147298899

theorem tailTrace_7996690 : CollatzResearch.WordTrace tailWord_7996690 prefixEnd_7996690 4106145615002423147298899 := by
  unfold tailWord_7996690
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915811349841332691528881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194442163599576887177410349 72915811349841332691528881)
  ·
    refine ⟨54686858512380999518646661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72915811349841332691528881 54686858512380999518646661)
    ·
      refine ⟨10253785971071437409746249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54686858512380999518646661 10253785971071437409746249)
      ·
        refine ⟨7690339478303578057309687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10253785971071437409746249 7690339478303578057309687)
        ·
          refine ⟨11535509217455367085964531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690339478303578057309687 11535509217455367085964531)
          ·
            refine ⟨17303263826183050628946797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535509217455367085964531 17303263826183050628946797)
            ·
              refine ⟨6488723934818643985855049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17303263826183050628946797 6488723934818643985855049)
              ·
                refine ⟨4866542951113982989391287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488723934818643985855049 4866542951113982989391287)
                ·
                  refine ⟨7299814426670974484086931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866542951113982989391287 7299814426670974484086931)
                  ·
                    refine ⟨10949721640006461726130397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7299814426670974484086931 10949721640006461726130397)
                    ·
                      refine ⟨4106145615002423147298899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10949721640006461726130397 4106145615002423147298899)
                      ·
                        rfl

theorem cell23_7996690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7996690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996690 prefixEnd_7996690 := by exact prefixLift 7996690
  have htrace : WordTrace (prefixWord ++ tailWord_7996690) baseStart_7996690 baseEnd_7996690 := by
    simpa [prefixWord, tailWord_7996690, baseEnd_7996690] using wordTrace_append hprefix tailTrace_7996690
  have hstable : (prefixWord ++ tailWord_7996690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996690).length < 2 ^ (prefixWord ++ tailWord_7996690).sum := by decide
  have hdescent : baseEnd_7996690 < baseStart_7996690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996705 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7996705 : Nat := 118140960795 + 7996705 * 2 ^ 59
def prefixEnd_7996705 : Nat := 4983230072969 + 3 ^ 40 * 7996705 * 2
def baseEnd_7996705 : Nat := 4106153317212240588611329

theorem tailTrace_7996705 : CollatzResearch.WordTrace tailWord_7996705 prefixEnd_7996705 4106153317212240588611329 := by
  unfold tailWord_7996705
  simp only [CollatzResearch.WordTrace]
  refine ⟨291663792494310988327911569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194442528329540658885274379 291663792494310988327911569)
  ·
    refine ⟨218747844370733241245933677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291663792494310988327911569 218747844370733241245933677)
    ·
      refine ⟨82030441639024965467225129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218747844370733241245933677 82030441639024965467225129)
      ·
        refine ⟨61522831229268724100418847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82030441639024965467225129 61522831229268724100418847)
        ·
          refine ⟨92284246843903086150628271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61522831229268724100418847 92284246843903086150628271)
          ·
            refine ⟨138426370265854629225942407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92284246843903086150628271 138426370265854629225942407)
            ·
              refine ⟨207639555398781943838913611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138426370265854629225942407 207639555398781943838913611)
              ·
                refine ⟨311459333098172915758370417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207639555398781943838913611 311459333098172915758370417)
                ·
                  refine ⟨233594499823629686818777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311459333098172915758370417 233594499823629686818777813)
                  ·
                    refine ⟨5474871089616320784815105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233594499823629686818777813 5474871089616320784815105)
                    ·
                      refine ⟨4106153317212240588611329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5474871089616320784815105 4106153317212240588611329)
                      ·
                        rfl

theorem cell23_7996705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7996705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996705 prefixEnd_7996705 := by exact prefixLift 7996705
  have htrace : WordTrace (prefixWord ++ tailWord_7996705) baseStart_7996705 baseEnd_7996705 := by
    simpa [prefixWord, tailWord_7996705, baseEnd_7996705] using wordTrace_append hprefix tailTrace_7996705
  have hstable : (prefixWord ++ tailWord_7996705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996705).length < 2 ^ (prefixWord ++ tailWord_7996705).sum := by decide
  have hdescent : baseEnd_7996705 < baseStart_7996705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996706 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7996706 : Nat := 118140960795 + 7996706 * 2 ^ 59
def prefixEnd_7996706 : Nat := 4983230072969 + 3 ^ 40 * 7996706 * 2
def baseEnd_7996706 : Nat := 1368717943564298361566275

theorem tailTrace_7996706 : CollatzResearch.WordTrace tailWord_7996706 prefixEnd_7996706 1368717943564298361566275 := by
  unfold tailWord_7996706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915957241826841374674493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194442552644871576999131981 72915957241826841374674493)
  ·
    refine ⟨27343483965685065515502935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72915957241826841374674493 27343483965685065515502935)
    ·
      refine ⟨41015225948527598273254403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27343483965685065515502935 41015225948527598273254403)
      ·
        refine ⟨61522838922791397409881605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41015225948527598273254403 61522838922791397409881605)
        ·
          refine ⟨11535532298023387014352801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61522838922791397409881605 11535532298023387014352801)
          ·
            refine ⟨8651649223517540260764601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11535532298023387014352801 8651649223517540260764601)
            ·
              refine ⟨6488736917638155195573451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651649223517540260764601 6488736917638155195573451)
              ·
                refine ⟨9733105376457232793360177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488736917638155195573451 9733105376457232793360177)
                ·
                  refine ⟨7299829032342924595020133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9733105376457232793360177 7299829032342924595020133)
                  ·
                    refine ⟨1368717943564298361566275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7299829032342924595020133 1368717943564298361566275)
                    ·
                      rfl

theorem cell23_7996706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7996706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996706 prefixEnd_7996706 := by exact prefixLift 7996706
  have htrace : WordTrace (prefixWord ++ tailWord_7996706) baseStart_7996706 baseEnd_7996706 := by
    simpa [prefixWord, tailWord_7996706, baseEnd_7996706] using wordTrace_append hprefix tailTrace_7996706
  have hstable : (prefixWord ++ tailWord_7996706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996706).length < 2 ^ (prefixWord ++ tailWord_7996706).sum := by decide
  have hdescent : baseEnd_7996706 < baseStart_7996706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996728 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_7996728 : Nat := 118140960795 + 7996728 * 2 ^ 59
def prefixEnd_7996728 : Nat := 4983230072969 + 3 ^ 40 * 7996728 * 2
def baseEnd_7996728 : Nat := 1368721709089097999541241

theorem tailTrace_7996728 : CollatzResearch.WordTrace tailWord_7996728 prefixEnd_7996728 1368721709089097999541241 := by
  unfold tailWord_7996728
  simp only [CollatzResearch.WordTrace]
  refine ⟨145832315686613831627999419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194443087582151775503999225 145832315686613831627999419)
  ·
    refine ⟨218748473529920747441999129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145832315686613831627999419 218748473529920747441999129)
    ·
      refine ⟨164061355147440560581499347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218748473529920747441999129 164061355147440560581499347)
      ·
        refine ⟨246092032721160840872249021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164061355147440560581499347 246092032721160840872249021)
        ·
          refine ⟨92284512270435315327093383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246092032721160840872249021 92284512270435315327093383)
          ·
            refine ⟨138426768405652972990640075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92284512270435315327093383 138426768405652972990640075)
            ·
              refine ⟨207640152608479459485960113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138426768405652972990640075 207640152608479459485960113)
              ·
                refine ⟨155730114456359594614470085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207640152608479459485960113 155730114456359594614470085)
                ·
                  refine ⟨29199396460567423990213141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155730114456359594614470085 29199396460567423990213141)
                  ·
                    refine ⟨1368721709089097999541241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29199396460567423990213141 1368721709089097999541241)
                    ·
                      rfl

theorem cell23_7996728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_7996728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996728 prefixEnd_7996728 := by exact prefixLift 7996728
  have htrace : WordTrace (prefixWord ++ tailWord_7996728) baseStart_7996728 baseEnd_7996728 := by
    simpa [prefixWord, tailWord_7996728, baseEnd_7996728] using wordTrace_append hprefix tailTrace_7996728
  have hstable : (prefixWord ++ tailWord_7996728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996728).length < 2 ^ (prefixWord ++ tailWord_7996728).sum := by decide
  have hdescent : baseEnd_7996728 < baseStart_7996728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996805 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_7996805 : Nat := 118140960795 + 7996805 * 2 ^ 59
def prefixEnd_7996805 : Nat := 4983230072969 + 3 ^ 40 * 7996805 * 2
def baseEnd_7996805 : Nat := 1368734888425896732453623

theorem tailTrace_7996805 : CollatzResearch.WordTrace tailWord_7996805 prefixEnd_7996805 1368734888425896732453623 := by
  unfold tailWord_7996805
  simp only [CollatzResearch.WordTrace]
  refine ⟨291667439793948705406551869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194444959862632470271034579 291667439793948705406551869)
  ·
    refine ⟨109375289922730764527456951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291667439793948705406551869 109375289922730764527456951)
    ·
      refine ⟨164062934884096146791185427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109375289922730764527456951 164062934884096146791185427)
      ·
        refine ⟨246094402326144220186778141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164062934884096146791185427 246094402326144220186778141)
        ·
          refine ⟨92285400872304082570041803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246094402326144220186778141 92285400872304082570041803)
          ·
            refine ⟨138428101308456123855062705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92285400872304082570041803 138428101308456123855062705)
            ·
              refine ⟨103821075981342092891297029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138428101308456123855062705 103821075981342092891297029)
              ·
                refine ⟨19466451746501642417118193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103821075981342092891297029 19466451746501642417118193)
                ·
                  refine ⟨14599838809876231812838645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19466451746501642417118193 14599838809876231812838645)
                  ·
                    refine ⟨1368734888425896732453623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14599838809876231812838645 1368734888425896732453623)
                    ·
                      rfl

theorem cell23_7996805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_7996805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996805 prefixEnd_7996805 := by exact prefixLift 7996805
  have htrace : WordTrace (prefixWord ++ tailWord_7996805) baseStart_7996805 baseEnd_7996805 := by
    simpa [prefixWord, tailWord_7996805, baseEnd_7996805] using wordTrace_append hprefix tailTrace_7996805
  have hstable : (prefixWord ++ tailWord_7996805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996805).length < 2 ^ (prefixWord ++ tailWord_7996805).sum := by decide
  have hdescent : baseEnd_7996805 < baseStart_7996805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996825 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_7996825 : Nat := 118140960795 + 7996825 * 2 ^ 59
def prefixEnd_7996825 : Nat := 4983230072969 + 3 ^ 40 * 7996825 * 2
def baseEnd_7996825 : Nat := 4106214934890780119110777

theorem tailTrace_7996825 : CollatzResearch.WordTrace tailWord_7996825 prefixEnd_7996825 4106214934890780119110777 := by
  unfold tailWord_7996825
  simp only [CollatzResearch.WordTrace]
  refine ⟨291668169253876248822279929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194445446169250832548186619 291668169253876248822279929)
  ·
    refine ⟨218751126940407186616709947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291668169253876248822279929 218751126940407186616709947)
    ·
      refine ⟨328126690410610779925064921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218751126940407186616709947 328126690410610779925064921)
      ·
        refine ⟨246095017807958084943798691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328126690410610779925064921 246095017807958084943798691)
        ·
          refine ⟨369142526711937127415698037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246095017807958084943798691 369142526711937127415698037)
          ·
            refine ⟨34607111879244105695221691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369142526711937127415698037 34607111879244105695221691)
            ·
              refine ⟨51910667818866158542832537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34607111879244105695221691 51910667818866158542832537)
              ·
                refine ⟨38933000864149618907124403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51910667818866158542832537 38933000864149618907124403)
                ·
                  refine ⟨58399501296224428360686605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38933000864149618907124403 58399501296224428360686605)
                  ·
                    refine ⟨21899812986084160635257477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58399501296224428360686605 21899812986084160635257477)
                    ·
                      refine ⟨4106214934890780119110777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21899812986084160635257477 4106214934890780119110777)
                      ·
                        rfl

theorem cell23_7996825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_7996825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996825 prefixEnd_7996825 := by exact prefixLift 7996825
  have htrace : WordTrace (prefixWord ++ tailWord_7996825) baseStart_7996825 baseEnd_7996825 := by
    simpa [prefixWord, tailWord_7996825, baseEnd_7996825] using wordTrace_append hprefix tailTrace_7996825
  have hstable : (prefixWord ++ tailWord_7996825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996825).length < 2 ^ (prefixWord ++ tailWord_7996825).sum := by decide
  have hdescent : baseEnd_7996825 < baseStart_7996825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996963 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 1, 5]
def baseStart_7996963 : Nat := 118140960795 + 7996963 * 2 ^ 59
def prefixEnd_7996963 : Nat := 4983230072969 + 3 ^ 40 * 7996963 * 2
def baseEnd_7996963 : Nat := 1368761931740366859728381

theorem tailTrace_7996963 : CollatzResearch.WordTrace tailWord_7996963 prefixEnd_7996963 1368761931740366859728381 := by
  unfold tailWord_7996963
  simp only [CollatzResearch.WordTrace]
  refine ⟨291673202527376298390803543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194448801684917532260535695 291673202527376298390803543)
  ·
    refine ⟨437509803791064447586205315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291673202527376298390803543 437509803791064447586205315)
    ·
      refine ⟨656264705686596671379307973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437509803791064447586205315 656264705686596671379307973)
      ·
        refine ⟨123049632316236875883620245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 656264705686596671379307973 123049632316236875883620245)
        ·
          refine ⟨5767951514823603557044699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123049632316236875883620245 5767951514823603557044699)
          ·
            refine ⟨8651927272235405335567049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767951514823603557044699 8651927272235405335567049)
            ·
              refine ⟨6488945454176554001675287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651927272235405335567049 6488945454176554001675287)
              ·
                refine ⟨9733418181264831002512931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488945454176554001675287 9733418181264831002512931)
                ·
                  refine ⟨14600127271897246503769397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733418181264831002512931 14600127271897246503769397)
                  ·
                    refine ⟨1368761931740366859728381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14600127271897246503769397 1368761931740366859728381)
                    ·
                      rfl

theorem cell23_7996963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 5].length) (baseStart_7996963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996963 prefixEnd_7996963 := by exact prefixLift 7996963
  have htrace : WordTrace (prefixWord ++ tailWord_7996963) baseStart_7996963 baseEnd_7996963 := by
    simpa [prefixWord, tailWord_7996963, baseEnd_7996963] using wordTrace_append hprefix tailTrace_7996963
  have hstable : (prefixWord ++ tailWord_7996963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996963).length < 2 ^ (prefixWord ++ tailWord_7996963).sum := by decide
  have hdescent : baseEnd_7996963 < baseStart_7996963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7996983 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_7996983 : Nat := 118140960795 + 7996983 * 2 ^ 59
def prefixEnd_7996983 : Nat := 4983230072969 + 3 ^ 40 * 7996983 * 2
def baseEnd_7996983 : Nat := 4106296064834190500935051

theorem tailTrace_7996983 : CollatzResearch.WordTrace tailWord_7996983 prefixEnd_7996983 4106296064834190500935051 := by
  unfold tailWord_7996983
  simp only [CollatzResearch.WordTrace]
  refine ⟨291673931987303841806531603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194449287991535894537687735 291673931987303841806531603)
  ·
    refine ⟨437510897980955762709797405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291673931987303841806531603 437510897980955762709797405)
    ·
      refine ⟨164066586742858411016174027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437510897980955762709797405 164066586742858411016174027)
      ·
        refine ⟨246099880114287616524261041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164066586742858411016174027 246099880114287616524261041)
        ·
          refine ⟨184574910085715712393195781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246099880114287616524261041 184574910085715712393195781)
          ·
            refine ⟨34607795641071696073724209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184574910085715712393195781 34607795641071696073724209)
            ·
              refine ⟨25955846730803772055293157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34607795641071696073724209 25955846730803772055293157)
              ·
                refine ⟨4866721262025707260367467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25955846730803772055293157 4866721262025707260367467)
                ·
                  refine ⟨7300081893038560890551201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866721262025707260367467 7300081893038560890551201)
                  ·
                    refine ⟨5475061419778920667913401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300081893038560890551201 5475061419778920667913401)
                    ·
                      refine ⟨4106296064834190500935051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475061419778920667913401 4106296064834190500935051)
                      ·
                        rfl

theorem cell23_7996983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_7996983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7996983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7996983 prefixEnd_7996983 := by exact prefixLift 7996983
  have htrace : WordTrace (prefixWord ++ tailWord_7996983) baseStart_7996983 baseEnd_7996983 := by
    simpa [prefixWord, tailWord_7996983, baseEnd_7996983] using wordTrace_append hprefix tailTrace_7996983
  have hstable : (prefixWord ++ tailWord_7996983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7996983).length < 2 ^ (prefixWord ++ tailWord_7996983).sum := by decide
  have hdescent : baseEnd_7996983 < baseStart_7996983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7996983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997012 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7997012 : Nat := 118140960795 + 7997012 * 2 ^ 59
def prefixEnd_7997012 : Nat := 4983230072969 + 3 ^ 40 * 7997012 * 2
def baseEnd_7997012 : Nat := 4106310955773170887472417

theorem tailTrace_7997012 : CollatzResearch.WordTrace tailWord_7997012 prefixEnd_7997012 4106310955773170887472417 := by
  unfold tailWord_7997012
  simp only [CollatzResearch.WordTrace]
  refine ⟨145837494852099389879668645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194449993136132519839558193 145837494852099389879668645)
  ·
    refine ⟨27344530284768635602437871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145837494852099389879668645 27344530284768635602437871)
    ·
      refine ⟨41016795427152953403656807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27344530284768635602437871 41016795427152953403656807)
      ·
        refine ⟨61525193140729430105485211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41016795427152953403656807 61525193140729430105485211)
        ·
          refine ⟨92287789711094145158227817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61525193140729430105485211 92287789711094145158227817)
          ·
            refine ⟨69215842283320608868670863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92287789711094145158227817 69215842283320608868670863)
            ·
              refine ⟨103823763424980913303006295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69215842283320608868670863 103823763424980913303006295)
              ·
                refine ⟨155735645137471369954509443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103823763424980913303006295 155735645137471369954509443)
                ·
                  refine ⟨233603467706207054931764165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155735645137471369954509443 233603467706207054931764165)
                  ·
                    refine ⟨43800650194913822799705781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233603467706207054931764165 43800650194913822799705781)
                    ·
                      refine ⟨4106310955773170887472417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43800650194913822799705781 4106310955773170887472417)
                      ·
                        rfl

theorem cell23_7997012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7997012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997012 prefixEnd_7997012 := by exact prefixLift 7997012
  have htrace : WordTrace (prefixWord ++ tailWord_7997012) baseStart_7997012 baseEnd_7997012 := by
    simpa [prefixWord, tailWord_7997012, baseEnd_7997012] using wordTrace_append hprefix tailTrace_7997012
  have hstable : (prefixWord ++ tailWord_7997012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997012).length < 2 ^ (prefixWord ++ tailWord_7997012).sum := by decide
  have hdescent : baseEnd_7997012 < baseStart_7997012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997052 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_7997052 : Nat := 118140960795 + 7997052 * 2 ^ 59
def prefixEnd_7997052 : Nat := 4983230072969 + 3 ^ 40 * 7997052 * 2
def baseEnd_7997052 : Nat := 4106331494999350730972233

theorem tailTrace_7997052 : CollatzResearch.WordTrace tailWord_7997052 prefixEnd_7997052 4106331494999350730972233 := by
  unfold tailWord_7997052
  simp only [CollatzResearch.WordTrace]
  refine ⟨145838224312026933295396705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194450965749369244393862273 145838224312026933295396705)
  ·
    refine ⟨109378668234020199971547529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145838224312026933295396705 109378668234020199971547529)
    ·
      refine ⟨82034001175515149978660647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109378668234020199971547529 82034001175515149978660647)
      ·
        refine ⟨123051001763272724967990971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82034001175515149978660647 123051001763272724967990971)
        ·
          refine ⟨184576502644909087451986457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123051001763272724967990971 184576502644909087451986457)
          ·
            refine ⟨138432376983681815588989843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184576502644909087451986457 138432376983681815588989843)
            ·
              refine ⟨207648565475522723383484765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138432376983681815588989843 207648565475522723383484765)
              ·
                refine ⟨77868212053321021268806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207648565475522723383484765 77868212053321021268806787)
                ·
                  refine ⟨116802318079981531903210181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77868212053321021268806787 116802318079981531903210181)
                  ·
                    refine ⟨21900434639996537231851909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116802318079981531903210181 21900434639996537231851909)
                    ·
                      refine ⟨4106331494999350730972233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21900434639996537231851909 4106331494999350730972233)
                      ·
                        rfl

theorem cell23_7997052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_7997052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997052 prefixEnd_7997052 := by exact prefixLift 7997052
  have htrace : WordTrace (prefixWord ++ tailWord_7997052) baseStart_7997052 baseEnd_7997052 := by
    simpa [prefixWord, tailWord_7997052, baseEnd_7997052] using wordTrace_append hprefix tailTrace_7997052
  have hstable : (prefixWord ++ tailWord_7997052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997052).length < 2 ^ (prefixWord ++ tailWord_7997052).sum := by decide
  have hdescent : baseEnd_7997052 < baseStart_7997052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997060 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7997060 : Nat := 118140960795 + 7997060 * 2 ^ 59
def prefixEnd_7997060 : Nat := 4983230072969 + 3 ^ 40 * 7997060 * 2
def baseEnd_7997060 : Nat := 4106335602844586699672197

theorem tailTrace_7997060 : CollatzResearch.WordTrace tailWord_7997060 prefixEnd_7997060 4106335602844586699672197 := by
  unfold tailWord_7997060
  simp only [CollatzResearch.WordTrace]
  refine ⟨145838370204012441978542317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194451160272016589304723089 145838370204012441978542317)
  ·
    refine ⟨54689388826504665741953369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145838370204012441978542317 54689388826504665741953369)
    ·
      refine ⟨41017041619878499306465027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54689388826504665741953369 41017041619878499306465027)
      ·
        refine ⟨61525562429817748959697541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41017041619878499306465027 61525562429817748959697541)
        ·
          refine ⟨11536042955590827929943289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61525562429817748959697541 11536042955590827929943289)
          ·
            refine ⟨8652032216693120947457467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11536042955590827929943289 8652032216693120947457467)
            ·
              refine ⟨12978048325039681421186201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652032216693120947457467 12978048325039681421186201)
              ·
                refine ⟨9733536243779761065889651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978048325039681421186201 9733536243779761065889651)
                ·
                  refine ⟨14600304365669641598834477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733536243779761065889651 14600304365669641598834477)
                  ·
                    refine ⟨5475114137126115599562929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14600304365669641598834477 5475114137126115599562929)
                    ·
                      refine ⟨4106335602844586699672197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475114137126115599562929 4106335602844586699672197)
                      ·
                        rfl

theorem cell23_7997060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7997060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997060 prefixEnd_7997060 := by exact prefixLift 7997060
  have htrace : WordTrace (prefixWord ++ tailWord_7997060) baseStart_7997060 baseEnd_7997060 := by
    simpa [prefixWord, tailWord_7997060, baseEnd_7997060] using wordTrace_append hprefix tailTrace_7997060
  have hstable : (prefixWord ++ tailWord_7997060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997060).length < 2 ^ (prefixWord ++ tailWord_7997060).sum := by decide
  have hdescent : baseEnd_7997060 < baseStart_7997060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997146 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_7997146 : Nat := 118140960795 + 7997146 * 2 ^ 59
def prefixEnd_7997146 : Nat := 4983230072969 + 3 ^ 40 * 7997146 * 2
def baseEnd_7997146 : Nat := 4106379762180873363196801

theorem tailTrace_7997146 : CollatzResearch.WordTrace tailWord_7997146 prefixEnd_7997146 4106379762180873363196801 := by
  unfold tailWord_7997146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72919969271428330161178823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194453251390475547096476861 72919969271428330161178823)
  ·
    refine ⟨109379953907142495241768235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72919969271428330161178823 109379953907142495241768235)
    ·
      refine ⟨164069930860713742862652353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109379953907142495241768235 164069930860713742862652353)
      ·
        refine ⟨123052448145535307146989265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164069930860713742862652353 123052448145535307146989265)
        ·
          refine ⟨92289336109151480360241949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123052448145535307146989265 92289336109151480360241949)
          ·
            refine ⟨34608501040931805135090731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92289336109151480360241949 34608501040931805135090731)
            ·
              refine ⟨51912751561397707702636097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34608501040931805135090731 51912751561397707702636097)
              ·
                refine ⟨38934563671048280776977073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51912751561397707702636097 38934563671048280776977073)
                ·
                  refine ⟨29200922753286210582732805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38934563671048280776977073 29200922753286210582732805)
                  ·
                    refine ⟨5475173016241164484262401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29200922753286210582732805 5475173016241164484262401)
                    ·
                      refine ⟨4106379762180873363196801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475173016241164484262401 4106379762180873363196801)
                      ·
                        rfl

theorem cell23_7997146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_7997146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997146 prefixEnd_7997146 := by exact prefixLift 7997146
  have htrace : WordTrace (prefixWord ++ tailWord_7997146) baseStart_7997146 baseEnd_7997146 := by
    simpa [prefixWord, tailWord_7997146, baseEnd_7997146] using wordTrace_append hprefix tailTrace_7997146
  have hstable : (prefixWord ++ tailWord_7997146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997146).length < 2 ^ (prefixWord ++ tailWord_7997146).sum := by decide
  have hdescent : baseEnd_7997146 < baseStart_7997146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997156 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_7997156 : Nat := 118140960795 + 7997156 * 2 ^ 59
def prefixEnd_7997156 : Nat := 4983230072969 + 3 ^ 40 * 7997156 * 2
def baseEnd_7997156 : Nat := 1368794965662472774690585

theorem tailTrace_7997156 : CollatzResearch.WordTrace tailWord_7997156 prefixEnd_7997156 1368794965662472774690585 := by
  unfold tailWord_7997156
  simp only [CollatzResearch.WordTrace]
  refine ⟨145840120907838546176289661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194453494543784728235052881 145840120907838546176289661)
  ·
    refine ⟨54690045340439454816108623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145840120907838546176289661 54690045340439454816108623)
    ·
      refine ⟨82035068010659182224162935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54690045340439454816108623 82035068010659182224162935)
      ·
        refine ⟨123052602015988773336244403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82035068010659182224162935 123052602015988773336244403)
        ·
          refine ⟨184578903023983160004366605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123052602015988773336244403 184578903023983160004366605)
          ·
            refine ⟨69217088633993685001637477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184578903023983160004366605 69217088633993685001637477)
            ·
              refine ⟨12978204118873815937807027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69217088633993685001637477 12978204118873815937807027)
              ·
                refine ⟨19467306178310723906710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978204118873815937807027 19467306178310723906710541)
                ·
                  refine ⟨7300239816866521465016453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19467306178310723906710541 7300239816866521465016453)
                  ·
                    refine ⟨1368794965662472774690585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300239816866521465016453 1368794965662472774690585)
                    ·
                      rfl

theorem cell23_7997156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_7997156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997156 prefixEnd_7997156 := by exact prefixLift 7997156
  have htrace : WordTrace (prefixWord ++ tailWord_7997156) baseStart_7997156 baseEnd_7997156 := by
    simpa [prefixWord, tailWord_7997156, baseEnd_7997156] using wordTrace_append hprefix tailTrace_7997156
  have hstable : (prefixWord ++ tailWord_7997156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997156).length < 2 ^ (prefixWord ++ tailWord_7997156).sum := by decide
  have hdescent : baseEnd_7997156 < baseStart_7997156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997196 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_7997196 : Nat := 118140960795 + 7997196 * 2 ^ 59
def prefixEnd_7997196 : Nat := 4983230072969 + 3 ^ 40 * 7997196 * 2
def baseEnd_7997196 : Nat := 4106405436213598167571571

theorem tailTrace_7997196 : CollatzResearch.WordTrace tailWord_7997196 prefixEnd_7997196 4106405436213598167571571 := by
  unfold tailWord_7997196
  simp only [CollatzResearch.WordTrace]
  refine ⟨145840850367766089592017721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194454467157021452789356961 145840850367766089592017721)
  ·
    refine ⟨109380637775824567194013291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145840850367766089592017721 109380637775824567194013291)
    ·
      refine ⟨164070956663736850791019937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109380637775824567194013291 164070956663736850791019937)
      ·
        refine ⟨123053217497802638093264953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164070956663736850791019937 123053217497802638093264953)
        ·
          refine ⟨92289913123351978569948715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123053217497802638093264953 92289913123351978569948715)
          ·
            refine ⟨138434869685027967854923073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92289913123351978569948715 138434869685027967854923073)
            ·
              refine ⟨103826152263770975891192305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138434869685027967854923073 103826152263770975891192305)
              ·
                refine ⟨77869614197828231918394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103826152263770975891192305 77869614197828231918394229)
                ·
                  refine ⟨7300276331046396742349459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77869614197828231918394229 7300276331046396742349459)
                  ·
                    refine ⟨10950414496569595113524189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300276331046396742349459 10950414496569595113524189)
                    ·
                      refine ⟨4106405436213598167571571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10950414496569595113524189 4106405436213598167571571)
                      ·
                        rfl

theorem cell23_7997196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_7997196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997196 prefixEnd_7997196 := by exact prefixLift 7997196
  have htrace : WordTrace (prefixWord ++ tailWord_7997196) baseStart_7997196 baseEnd_7997196 := by
    simpa [prefixWord, tailWord_7997196, baseEnd_7997196] using wordTrace_append hprefix tailTrace_7997196
  have hstable : (prefixWord ++ tailWord_7997196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997196).length < 2 ^ (prefixWord ++ tailWord_7997196).sum := by decide
  have hdescent : baseEnd_7997196 < baseStart_7997196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997233 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_7997233 : Nat := 118140960795 + 7997233 * 2 ^ 59
def prefixEnd_7997233 : Nat := 4983230072969 + 3 ^ 40 * 7997233 * 2
def baseEnd_7997233 : Nat := 1368808144999271507602967

theorem tailTrace_7997233 : CollatzResearch.WordTrace tailWord_7997233 prefixEnd_7997233 1368808144999271507602967 := by
  unfold tailWord_7997233
  simp only [CollatzResearch.WordTrace]
  refine ⟨291683050236398134503132353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194455366824265423002088235 291683050236398134503132353)
  ·
    refine ⟨218762287677298600877349265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291683050236398134503132353 218762287677298600877349265)
    ·
      refine ⟨164071715757973950658011949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218762287677298600877349265 164071715757973950658011949)
      ·
        refine ⟨61526893409240231496754481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164071715757973950658011949 61526893409240231496754481)
        ·
          refine ⟨46145170056930173622565861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61526893409240231496754481 46145170056930173622565861)
          ·
            refine ⟨8652219385674407554231099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46145170056930173622565861 8652219385674407554231099)
            ·
              refine ⟨12978329078511611331346649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652219385674407554231099 12978329078511611331346649)
              ·
                refine ⟨9733746808883708498509987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978329078511611331346649 9733746808883708498509987)
                ·
                  refine ⟨14600620213325562747764981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733746808883708498509987 14600620213325562747764981)
                  ·
                    refine ⟨1368808144999271507602967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14600620213325562747764981 1368808144999271507602967)
                    ·
                      rfl

theorem cell23_7997233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_7997233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997233 prefixEnd_7997233 := by exact prefixLift 7997233
  have htrace : WordTrace (prefixWord ++ tailWord_7997233) baseStart_7997233 baseEnd_7997233 := by
    simpa [prefixWord, tailWord_7997233, baseEnd_7997233] using wordTrace_append hprefix tailTrace_7997233
  have hstable : (prefixWord ++ tailWord_7997233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997233).length < 2 ^ (prefixWord ++ tailWord_7997233).sum := by decide
  have hdescent : baseEnd_7997233 < baseStart_7997233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997246 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7997246 : Nat := 118140960795 + 7997246 * 2 ^ 59
def prefixEnd_7997246 : Nat := 4983230072969 + 3 ^ 40 * 7997246 * 2
def baseEnd_7997246 : Nat := 1368810370082107657315447

theorem tailTrace_7997246 : CollatzResearch.WordTrace tailWord_7997246 prefixEnd_7997246 1368810370082107657315447 := by
  unfold tailWord_7997246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36460440548168879715419449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194455682923567358482237061 36460440548168879715419449)
  ·
    refine ⟨27345330411126659786564587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36460440548168879715419449 27345330411126659786564587)
    ·
      refine ⟨41017995616689989679846881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27345330411126659786564587 41017995616689989679846881)
      ·
        refine ⟨30763496712517492259885161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41017995616689989679846881 30763496712517492259885161)
        ·
          refine ⟨23072622534388119194913871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30763496712517492259885161 23072622534388119194913871)
          ·
            refine ⟨34608933801582178792370807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23072622534388119194913871 34608933801582178792370807)
            ·
              refine ⟨51913400702373268188556211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34608933801582178792370807 51913400702373268188556211)
              ·
                refine ⟨77870101053559902282834317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51913400702373268188556211 77870101053559902282834317)
                ·
                  refine ⟨29201287895084963356062869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77870101053559902282834317 29201287895084963356062869)
                  ·
                    refine ⟨1368810370082107657315447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29201287895084963356062869 1368810370082107657315447)
                    ·
                      rfl

theorem cell23_7997246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7997246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997246 prefixEnd_7997246 := by exact prefixLift 7997246
  have htrace : WordTrace (prefixWord ++ tailWord_7997246) baseStart_7997246 baseEnd_7997246 := by
    simpa [prefixWord, tailWord_7997246, baseEnd_7997246] using wordTrace_append hprefix tailTrace_7997246
  have hstable : (prefixWord ++ tailWord_7997246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997246).length < 2 ^ (prefixWord ++ tailWord_7997246).sum := by decide
  have hdescent : baseEnd_7997246 < baseStart_7997246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997253 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_7997253 : Nat := 118140960795 + 7997253 * 2 ^ 59
def prefixEnd_7997253 : Nat := 4983230072969 + 3 ^ 40 * 7997253 * 2
def baseEnd_7997253 : Nat := 4106434704610904444558809

theorem tailTrace_7997253 : CollatzResearch.WordTrace tailWord_7997253 prefixEnd_7997253 4106434704610904444558809 := by
  unfold tailWord_7997253
  simp only [CollatzResearch.WordTrace]
  refine ⟨291683779696325677918860413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194455853130883785279240275 291683779696325677918860413)
  ·
    refine ⟨109381417386122129219572655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291683779696325677918860413 109381417386122129219572655)
    ·
      refine ⟨164072126079183193829358983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109381417386122129219572655 164072126079183193829358983)
      ·
        refine ⟨246108189118774790744038475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164072126079183193829358983 246108189118774790744038475)
        ·
          refine ⟨369162283678162186116057713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246108189118774790744038475 369162283678162186116057713)
          ·
            refine ⟨276871712758621639587043285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369162283678162186116057713 276871712758621639587043285)
            ·
              refine ⟨6489180767780194677821327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276871712758621639587043285 6489180767780194677821327)
              ·
                refine ⟨9733771151670292016731991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489180767780194677821327 9733771151670292016731991)
                ·
                  refine ⟨14600656727505438025097987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9733771151670292016731991 14600656727505438025097987)
                  ·
                    refine ⟨21900985091258157037646981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14600656727505438025097987 21900985091258157037646981)
                    ·
                      refine ⟨4106434704610904444558809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21900985091258157037646981 4106434704610904444558809)
                      ·
                        rfl

theorem cell23_7997253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_7997253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997253 prefixEnd_7997253 := by exact prefixLift 7997253
  have htrace : WordTrace (prefixWord ++ tailWord_7997253) baseStart_7997253 baseEnd_7997253 := by
    simpa [prefixWord, tailWord_7997253, baseEnd_7997253] using wordTrace_append hprefix tailTrace_7997253
  have hstable : (prefixWord ++ tailWord_7997253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997253).length < 2 ^ (prefixWord ++ tailWord_7997253).sum := by decide
  have hdescent : baseEnd_7997253 < baseStart_7997253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997256 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_7997256 : Nat := 118140960795 + 7997256 * 2 ^ 59
def prefixEnd_7997256 : Nat := 4983230072969 + 3 ^ 40 * 7997256 * 2
def baseEnd_7997256 : Nat := 4106436245052867932821295

theorem tailTrace_7997256 : CollatzResearch.WordTrace tailWord_7997256 prefixEnd_7997256 4106436245052867932821295 := by
  unfold tailWord_7997256
  simp only [CollatzResearch.WordTrace]
  refine ⟨145841944557657404715609811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194455926076876539620813081 145841944557657404715609811)
  ·
    refine ⟨218762916836486107073414717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145841944557657404715609811 218762916836486107073414717)
    ·
      refine ⟨82036093813682290152530519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218762916836486107073414717 82036093813682290152530519)
      ·
        refine ⟨123054140720523435228795779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82036093813682290152530519 123054140720523435228795779)
        ·
          refine ⟨184581211080785152843193669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123054140720523435228795779 184581211080785152843193669)
          ·
            refine ⟨34608977077647216158098813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184581211080785152843193669 34608977077647216158098813)
            ·
              refine ⟨12978366404117706059287055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34608977077647216158098813 12978366404117706059287055)
              ·
                refine ⟨19467549606176559088930583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978366404117706059287055 19467549606176559088930583)
                ·
                  refine ⟨29201324409264838633395875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19467549606176559088930583 29201324409264838633395875)
                  ·
                    refine ⟨43801986613897257950093813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29201324409264838633395875 43801986613897257950093813)
                    ·
                      refine ⟨4106436245052867932821295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43801986613897257950093813 4106436245052867932821295)
                      ·
                        rfl

theorem cell23_7997256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_7997256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997256 prefixEnd_7997256 := by exact prefixLift 7997256
  have htrace : WordTrace (prefixWord ++ tailWord_7997256) baseStart_7997256 baseEnd_7997256 := by
    simpa [prefixWord, tailWord_7997256, baseEnd_7997256] using wordTrace_append hprefix tailTrace_7997256
  have hstable : (prefixWord ++ tailWord_7997256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997256).length < 2 ^ (prefixWord ++ tailWord_7997256).sum := by decide
  have hdescent : baseEnd_7997256 < baseStart_7997256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997283 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7997283 : Nat := 118140960795 + 7997283 * 2 ^ 59
def prefixEnd_7997283 : Nat := 4983230072969 + 3 ^ 40 * 7997283 * 2
def baseEnd_7997283 : Nat := 4106450109030539327183671

theorem tailTrace_7997283 : CollatzResearch.WordTrace tailWord_7997283 prefixEnd_7997283 4106450109030539327183671 := by
  unfold tailWord_7997283
  simp only [CollatzResearch.WordTrace]
  refine ⟨291684873886216993042452503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194456582590811328694968335 291684873886216993042452503)
  ·
    refine ⟨437527310829325489563678755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291684873886216993042452503 437527310829325489563678755)
    ·
      refine ⟨656290966243988234345518133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437527310829325489563678755 656290966243988234345518133)
      ·
        refine ⟨61527278085373896969892325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656290966243988234345518133 61527278085373896969892325)
        ·
          refine ⟨11536364641007605681854811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61527278085373896969892325 11536364641007605681854811)
          ·
            refine ⟨17304546961511408522782217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536364641007605681854811 17304546961511408522782217)
            ·
              refine ⟨12978410221133556392086663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304546961511408522782217 12978410221133556392086663)
              ·
                refine ⟨19467615331700334588129995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978410221133556392086663 19467615331700334588129995)
                ·
                  refine ⟨29201422997550501882194993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19467615331700334588129995 29201422997550501882194993)
                  ·
                    refine ⟨21901067248162876411646245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29201422997550501882194993 21901067248162876411646245)
                    ·
                      refine ⟨4106450109030539327183671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21901067248162876411646245 4106450109030539327183671)
                      ·
                        rfl

theorem cell23_7997283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7997283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997283 prefixEnd_7997283 := by exact prefixLift 7997283
  have htrace : WordTrace (prefixWord ++ tailWord_7997283) baseStart_7997283 baseEnd_7997283 := by
    simpa [prefixWord, tailWord_7997283, baseEnd_7997283] using wordTrace_append hprefix tailTrace_7997283
  have hstable : (prefixWord ++ tailWord_7997283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997283).length < 2 ^ (prefixWord ++ tailWord_7997283).sum := by decide
  have hdescent : baseEnd_7997283 < baseStart_7997283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997299 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_7997299 : Nat := 118140960795 + 7997299 * 2 ^ 59
def prefixEnd_7997299 : Nat := 4983230072969 + 3 ^ 40 * 7997299 * 2
def baseEnd_7997299 : Nat := 4106458324721011264583597

theorem tailTrace_7997299 : CollatzResearch.WordTrace tailWord_7997299 prefixEnd_7997299 4106458324721011264583597 := by
  unfold tailWord_7997299
  simp only [CollatzResearch.WordTrace]
  refine ⟨291685457454159027775034951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194456971636106018516689967 291685457454159027775034951)
  ·
    refine ⟨437528186181238541662552427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291685457454159027775034951 437528186181238541662552427)
    ·
      refine ⟨656292279271857812493828641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437528186181238541662552427 656292279271857812493828641)
      ·
        refine ⟨492219209453893359370371481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656292279271857812493828641 492219209453893359370371481)
        ·
          refine ⟨369164407090420019527778611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492219209453893359370371481 369164407090420019527778611)
          ·
            refine ⟨553746610635630029291667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369164407090420019527778611 553746610635630029291667917)
            ·
              refine ⟨207654978988361260984375469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553746610635630029291667917 207654978988361260984375469)
              ·
                refine ⟨77870617120635472869140801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207654978988361260984375469 77870617120635472869140801)
                ·
                  refine ⟨58402962840476604651855601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77870617120635472869140801 58402962840476604651855601)
                  ·
                    refine ⟨43802222130357453488891701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58402962840476604651855601 43802222130357453488891701)
                    ·
                      refine ⟨4106458324721011264583597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43802222130357453488891701 4106458324721011264583597)
                      ·
                        rfl

theorem cell23_7997299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_7997299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997299 prefixEnd_7997299 := by exact prefixLift 7997299
  have htrace : WordTrace (prefixWord ++ tailWord_7997299) baseStart_7997299 baseEnd_7997299 := by
    simpa [prefixWord, tailWord_7997299, baseEnd_7997299] using wordTrace_append hprefix tailTrace_7997299
  have hstable : (prefixWord ++ tailWord_7997299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997299).length < 2 ^ (prefixWord ++ tailWord_7997299).sum := by decide
  have hdescent : baseEnd_7997299 < baseStart_7997299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997320 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7997320 : Nat := 118140960795 + 7997320 * 2 ^ 59
def prefixEnd_7997320 : Nat := 4983230072969 + 3 ^ 40 * 7997320 * 2
def baseEnd_7997320 : Nat := 4106469107814755682421001

theorem tailTrace_7997320 : CollatzResearch.WordTrace tailWord_7997320 prefixEnd_7997320 4106469107814755682421001 := by
  unfold tailWord_7997320
  simp only [CollatzResearch.WordTrace]
  refine ⟨145843111693541474180774707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194457482258055298907699609 145843111693541474180774707)
  ·
    refine ⟨218764667540312211271162061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145843111693541474180774707 218764667540312211271162061)
    ·
      refine ⟨82036750327617079226685773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218764667540312211271162061 82036750327617079226685773)
      ·
        refine ⟨30763781372856404710007165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82036750327617079226685773 30763781372856404710007165)
        ·
          refine ⟨11536418014821151766252687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30763781372856404710007165 11536418014821151766252687)
          ·
            refine ⟨17304627022231727649379031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536418014821151766252687 17304627022231727649379031)
            ·
              refine ⟨25956940533347591474068547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17304627022231727649379031 25956940533347591474068547)
              ·
                refine ⟨38935410800021387211102821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25956940533347591474068547 38935410800021387211102821)
                ·
                  refine ⟨7300389525004010102081779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38935410800021387211102821 7300389525004010102081779)
                  ·
                    refine ⟨10950584287506015153122669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300389525004010102081779 10950584287506015153122669)
                    ·
                      refine ⟨4106469107814755682421001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10950584287506015153122669 4106469107814755682421001)
                      ·
                        rfl

theorem cell23_7997320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7997320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997320 prefixEnd_7997320 := by exact prefixLift 7997320
  have htrace : WordTrace (prefixWord ++ tailWord_7997320) baseStart_7997320 baseEnd_7997320 := by
    simpa [prefixWord, tailWord_7997320, baseEnd_7997320] using wordTrace_append hprefix tailTrace_7997320
  have hstable : (prefixWord ++ tailWord_7997320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997320).length < 2 ^ (prefixWord ++ tailWord_7997320).sum := by decide
  have hdescent : baseEnd_7997320 < baseStart_7997320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997334 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7997334 : Nat := 118140960795 + 7997334 * 2 ^ 59
def prefixEnd_7997334 : Nat := 4983230072969 + 3 ^ 40 * 7997334 * 2
def baseEnd_7997334 : Nat := 4106476296543918627645937

theorem tailTrace_7997334 : CollatzResearch.WordTrace tailWord_7997334 prefixEnd_7997334 4106476296543918627645937 := by
  unfold tailWord_7997334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18230420875564514297034941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194457822672688152501706037 18230420875564514297034941)
  ·
    refine ⟨6836407828336692861388103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18230420875564514297034941 6836407828336692861388103)
    ·
      refine ⟨10254611742505039292082155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836407828336692861388103 10254611742505039292082155)
      ·
        refine ⟨15381917613757558938123233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10254611742505039292082155 15381917613757558938123233)
        ·
          refine ⟨11536438210318169203592425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15381917613757558938123233 11536438210318169203592425)
          ·
            refine ⟨8652328657738626902694319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11536438210318169203592425 8652328657738626902694319)
            ·
              refine ⟨12978492986607940354041479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652328657738626902694319 12978492986607940354041479)
              ·
                refine ⟨19467739479911910531062219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978492986607940354041479 19467739479911910531062219)
                ·
                  refine ⟨29201609219867865796593329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19467739479911910531062219 29201609219867865796593329)
                  ·
                    refine ⟨21901206914900899347444997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29201609219867865796593329 21901206914900899347444997)
                    ·
                      refine ⟨4106476296543918627645937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21901206914900899347444997 4106476296543918627645937)
                      ·
                        rfl

theorem cell23_7997334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7997334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997334 prefixEnd_7997334 := by exact prefixLift 7997334
  have htrace : WordTrace (prefixWord ++ tailWord_7997334) baseStart_7997334 baseEnd_7997334 := by
    simpa [prefixWord, tailWord_7997334, baseEnd_7997334] using wordTrace_append hprefix tailTrace_7997334
  have hstable : (prefixWord ++ tailWord_7997334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997334).length < 2 ^ (prefixWord ++ tailWord_7997334).sum := by decide
  have hdescent : baseEnd_7997334 < baseStart_7997334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997394 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7997394 : Nat := 118140960795 + 7997394 * 2 ^ 59
def prefixEnd_7997394 : Nat := 4983230072969 + 3 ^ 40 * 7997394 * 2
def baseEnd_7997394 : Nat := 4106507105383188392895661

theorem tailTrace_7997394 : CollatzResearch.WordTrace tailWord_7997394 prefixEnd_7997394 4106507105383188392895661 := by
  unfold tailWord_7997394
  simp only [CollatzResearch.WordTrace]
  refine ⟨72922230597203714749935809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194459281592543239333162157 72922230597203714749935809)
  ·
    refine ⟨54691672947902786062451857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72922230597203714749935809 54691672947902786062451857)
    ·
      refine ⟨41018754710927089546838893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54691672947902786062451857 41018754710927089546838893)
      ·
        refine ⟨15382033016597658580064585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41018754710927089546838893 15382033016597658580064585)
        ·
          refine ⟨11536524762448243935048439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15382033016597658580064585 11536524762448243935048439)
          ·
            refine ⟨17304787143672365902572659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536524762448243935048439 17304787143672365902572659)
            ·
              refine ⟨25957180715508548853858989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17304787143672365902572659 25957180715508548853858989)
              ·
                refine ⟨9733942768315705820197121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25957180715508548853858989 9733942768315705820197121)
                ·
                  refine ⟨7300457076236779365147841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9733942768315705820197121 7300457076236779365147841)
                  ·
                    refine ⟨5475342807177584523860881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300457076236779365147841 5475342807177584523860881)
                    ·
                      refine ⟨4106507105383188392895661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475342807177584523860881 4106507105383188392895661)
                      ·
                        rfl

theorem cell23_7997394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7997394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997394 prefixEnd_7997394 := by exact prefixLift 7997394
  have htrace : WordTrace (prefixWord ++ tailWord_7997394) baseStart_7997394 baseEnd_7997394 := by
    simpa [prefixWord, tailWord_7997394, baseEnd_7997394] using wordTrace_append hprefix tailTrace_7997394
  have hstable : (prefixWord ++ tailWord_7997394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997394).length < 2 ^ (prefixWord ++ tailWord_7997394).sum := by decide
  have hdescent : baseEnd_7997394 < baseStart_7997394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997433 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_7997433 : Nat := 118140960795 + 7997433 * 2 ^ 59
def prefixEnd_7997433 : Nat := 4983230072969 + 3 ^ 40 * 7997433 * 2
def baseEnd_7997433 : Nat := 4106527131128713740307981

theorem tailTrace_7997433 : CollatzResearch.WordTrace tailWord_7997433 prefixEnd_7997433 4106527131128713740307981 := by
  unfold tailWord_7997433
  simp only [CollatzResearch.WordTrace]
  refine ⟨291690344835673568660412953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194460229890449045773608635 291690344835673568660412953)
  ·
    refine ⟨218767758626755176495309715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291690344835673568660412953 218767758626755176495309715)
    ·
      refine ⟨328151637940132764742964573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218767758626755176495309715 328151637940132764742964573)
      ·
        refine ⟨123056864227549786778611715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328151637940132764742964573 123056864227549786778611715)
        ·
          refine ⟨184585296341324680167917573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123056864227549786778611715 184585296341324680167917573)
          ·
            refine ⟨34609743063998377531484545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184585296341324680167917573 34609743063998377531484545)
            ·
              refine ⟨25957307297998783148613409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34609743063998377531484545 25957307297998783148613409)
              ·
                refine ⟨19467980473499087361460057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25957307297998783148613409 19467980473499087361460057)
                ·
                  refine ⟨14600985355124315521095043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19467980473499087361460057 14600985355124315521095043)
                  ·
                    refine ⟨21901478032686473281642565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14600985355124315521095043 21901478032686473281642565)
                    ·
                      refine ⟨4106527131128713740307981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21901478032686473281642565 4106527131128713740307981)
                      ·
                        rfl

theorem cell23_7997433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_7997433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997433 prefixEnd_7997433 := by exact prefixLift 7997433
  have htrace : WordTrace (prefixWord ++ tailWord_7997433) baseStart_7997433 baseEnd_7997433 := by
    simpa [prefixWord, tailWord_7997433, baseEnd_7997433] using wordTrace_append hprefix tailTrace_7997433
  have hstable : (prefixWord ++ tailWord_7997433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997433).length < 2 ^ (prefixWord ++ tailWord_7997433).sum := by decide
  have hdescent : baseEnd_7997433 < baseStart_7997433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997436 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_7997436 : Nat := 118140960795 + 7997436 * 2 ^ 59
def prefixEnd_7997436 : Nat := 4983230072969 + 3 ^ 40 * 7997436 * 2
def baseEnd_7997436 : Nat := 4106528671570677228570467

theorem tailTrace_7997436 : CollatzResearch.WordTrace tailWord_7997436 prefixEnd_7997436 4106528671570677228570467 := by
  unfold tailWord_7997436
  simp only [CollatzResearch.WordTrace]
  refine ⟨145845227127331350086386081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194460302836441800115181441 145845227127331350086386081)
  ·
    refine ⟨109383920345498512564789561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145845227127331350086386081 109383920345498512564789561)
    ·
      refine ⟨82037940259123884423592171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109383920345498512564789561 82037940259123884423592171)
      ·
        refine ⟨123056910388685826635388257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82037940259123884423592171 123056910388685826635388257)
        ·
          refine ⟨92292682791514369976541193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123056910388685826635388257 92292682791514369976541193)
          ·
            refine ⟨69219512093635777482405895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92292682791514369976541193 69219512093635777482405895)
            ·
              refine ⟨103829268140453666223608843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69219512093635777482405895 103829268140453666223608843)
              ·
                refine ⟨155743902210680499335413265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103829268140453666223608843 155743902210680499335413265)
                ·
                  refine ⟨116807926658010374501559949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155743902210680499335413265 116807926658010374501559949)
                  ·
                    refine ⟨43802972496753890438084981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116807926658010374501559949 43802972496753890438084981)
                    ·
                      refine ⟨4106528671570677228570467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43802972496753890438084981 4106528671570677228570467)
                      ·
                        rfl

theorem cell23_7997436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_7997436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997436 prefixEnd_7997436 := by exact prefixLift 7997436
  have htrace : WordTrace (prefixWord ++ tailWord_7997436) baseStart_7997436 baseEnd_7997436 := by
    simpa [prefixWord, tailWord_7997436, baseEnd_7997436] using wordTrace_append hprefix tailTrace_7997436
  have hstable : (prefixWord ++ tailWord_7997436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997436).length < 2 ^ (prefixWord ++ tailWord_7997436).sum := by decide
  have hdescent : baseEnd_7997436 < baseStart_7997436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997477 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_7997477 : Nat := 118140960795 + 7997477 * 2 ^ 59
def prefixEnd_7997477 : Nat := 4983230072969 + 3 ^ 40 * 7997477 * 2
def baseEnd_7997477 : Nat := 1368849908092503856052593

theorem tailTrace_7997477 : CollatzResearch.WordTrace tailWord_7997477 prefixEnd_7997477 1368849908092503856052593 := by
  unfold tailWord_7997477
  simp only [CollatzResearch.WordTrace]
  refine ⟨291691949647514164175014685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194461299765009442783343123 291691949647514164175014685)
  ·
    refine ⟨109384481117817811565630507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291691949647514164175014685 109384481117817811565630507)
    ·
      refine ⟨164076721676726717348445761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109384481117817811565630507 164076721676726717348445761)
      ·
        refine ⟨123057541257545038011334321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164076721676726717348445761 123057541257545038011334321)
        ·
          refine ⟨92293155943158778508500741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123057541257545038011334321 92293155943158778508500741)
          ·
            refine ⟨17304966739342270970343889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92293155943158778508500741 17304966739342270970343889)
            ·
              refine ⟨12978725054506703227757917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304966739342270970343889 12978725054506703227757917)
              ·
                refine ⟨4867021895440013710409219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12978725054506703227757917 4867021895440013710409219)
                ·
                  refine ⟨7300532843160020565613829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867021895440013710409219 7300532843160020565613829)
                  ·
                    refine ⟨1368849908092503856052593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300532843160020565613829 1368849908092503856052593)
                    ·
                      rfl

theorem cell23_7997477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_7997477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997477 prefixEnd_7997477 := by exact prefixLift 7997477
  have htrace : WordTrace (prefixWord ++ tailWord_7997477) baseStart_7997477 baseEnd_7997477 := by
    simpa [prefixWord, tailWord_7997477, baseEnd_7997477] using wordTrace_append hprefix tailTrace_7997477
  have hstable : (prefixWord ++ tailWord_7997477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997477).length < 2 ^ (prefixWord ++ tailWord_7997477).sum := by decide
  have hdescent : baseEnd_7997477 < baseStart_7997477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997490 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_7997490 : Nat := 118140960795 + 7997490 * 2 ^ 59
def prefixEnd_7997490 : Nat := 4983230072969 + 3 ^ 40 * 7997490 * 2
def baseEnd_7997490 : Nat := 456284044391780001921691

theorem tailTrace_7997490 : CollatzResearch.WordTrace tailWord_7997490 prefixEnd_7997490 456284044391780001921691 := by
  unfold tailWord_7997490
  simp only [CollatzResearch.WordTrace]
  refine ⟨72923105949116766848809481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194461615864311378263491949 72923105949116766848809481)
  ·
    refine ⟨54692329461837575136607111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72923105949116766848809481 54692329461837575136607111)
    ·
      refine ⟨82038494192756362704910667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54692329461837575136607111 82038494192756362704910667)
      ·
        refine ⟨123057741289134544057366001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82038494192756362704910667 123057741289134544057366001)
        ·
          refine ⟨92293305966850908043024501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123057741289134544057366001 92293305966850908043024501)
          ·
            refine ⟨8652497434392272629033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92293305966850908043024501 8652497434392272629033547)
            ·
              refine ⟨12978746151588408943550321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652497434392272629033547 12978746151588408943550321)
              ·
                refine ⟨9734059613691306707662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978746151588408943550321 9734059613691306707662741)
                ·
                  refine ⟨456284044391780001921691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9734059613691306707662741 456284044391780001921691)
                  ·
                    rfl

theorem cell23_7997490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_7997490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997490 prefixEnd_7997490 := by exact prefixLift 7997490
  have htrace : WordTrace (prefixWord ++ tailWord_7997490) baseStart_7997490 baseEnd_7997490 := by
    simpa [prefixWord, tailWord_7997490, baseEnd_7997490] using wordTrace_append hprefix tailTrace_7997490
  have hstable : (prefixWord ++ tailWord_7997490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997490).length < 2 ^ (prefixWord ++ tailWord_7997490).sum := by decide
  have hdescent : baseEnd_7997490 < baseStart_7997490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997510 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7997510 : Nat := 118140960795 + 7997510 * 2 ^ 59
def prefixEnd_7997510 : Nat := 4983230072969 + 3 ^ 40 * 7997510 * 2
def baseEnd_7997510 : Nat := 4106566669139109939045127

theorem tailTrace_7997510 : CollatzResearch.WordTrace tailWord_7997510 prefixEnd_7997510 4106566669139109939045127 := by
  unfold tailWord_7997510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115411039262331587842687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194462102170929740540643989 9115411039262331587842687)
  ·
    refine ⟨13673116558893497381764031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9115411039262331587842687 13673116558893497381764031)
    ·
      refine ⟨20509674838340246072646047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673116558893497381764031 20509674838340246072646047)
      ·
        refine ⟨30764512257510369108969071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20509674838340246072646047 30764512257510369108969071)
        ·
          refine ⟨46146768386265553663453607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30764512257510369108969071 46146768386265553663453607)
          ·
            refine ⟨69220152579398330495180411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46146768386265553663453607 69220152579398330495180411)
            ·
              refine ⟨103830228869097495742770617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69220152579398330495180411 103830228869097495742770617)
              ·
                refine ⟨77872671651823121807077963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103830228869097495742770617 77872671651823121807077963)
                ·
                  refine ⟨116809007477734682710616945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77872671651823121807077963 116809007477734682710616945)
                  ·
                    refine ⟨87606755608301012032962709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116809007477734682710616945 87606755608301012032962709)
                    ·
                      refine ⟨4106566669139109939045127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87606755608301012032962709 4106566669139109939045127)
                      ·
                        rfl

theorem cell23_7997510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7997510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997510 prefixEnd_7997510 := by exact prefixLift 7997510
  have htrace : WordTrace (prefixWord ++ tailWord_7997510) baseStart_7997510 baseEnd_7997510 := by
    simpa [prefixWord, tailWord_7997510, baseEnd_7997510] using wordTrace_append hprefix tailTrace_7997510
  have hstable : (prefixWord ++ tailWord_7997510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997510).length < 2 ^ (prefixWord ++ tailWord_7997510).sum := by decide
  have hdescent : baseEnd_7997510 < baseStart_7997510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997517 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7997517 : Nat := 118140960795 + 7997517 * 2 ^ 59
def prefixEnd_7997517 : Nat := 4983230072969 + 3 ^ 40 * 7997517 * 2
def baseEnd_7997517 : Nat := 4106570263503691411657595

theorem tailTrace_7997517 : CollatzResearch.WordTrace tailWord_7997517 prefixEnd_7997517 4106570263503691411657595 := by
  unfold tailWord_7997517
  simp only [CollatzResearch.WordTrace]
  refine ⟨291693408567369251006470805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194462272378246167337647203 291693408567369251006470805)
  ·
    refine ⟨13673128526595433640928319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291693408567369251006470805 13673128526595433640928319)
    ·
      refine ⟨20509692789893150461392479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673128526595433640928319 20509692789893150461392479)
      ·
        refine ⟨30764539184839725692088719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20509692789893150461392479 30764539184839725692088719)
        ·
          refine ⟨46146808777259588538133079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30764539184839725692088719 46146808777259588538133079)
          ·
            refine ⟨69220213165889382807199619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46146808777259588538133079 69220213165889382807199619)
            ·
              refine ⟨103830319748834074210799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69220213165889382807199619 103830319748834074210799429)
              ·
                refine ⟨19468184952906388914524893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103830319748834074210799429 19468184952906388914524893)
                ·
                  refine ⟨7300569357339895842946835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19468184952906388914524893 7300569357339895842946835)
                  ·
                    refine ⟨10950854036009843764420253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300569357339895842946835 10950854036009843764420253)
                    ·
                      refine ⟨4106570263503691411657595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10950854036009843764420253 4106570263503691411657595)
                      ·
                        rfl

theorem cell23_7997517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7997517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997517 prefixEnd_7997517 := by exact prefixLift 7997517
  have htrace : WordTrace (prefixWord ++ tailWord_7997517) baseStart_7997517 baseEnd_7997517 := by
    simpa [prefixWord, tailWord_7997517, baseEnd_7997517] using wordTrace_append hprefix tailTrace_7997517
  have hstable : (prefixWord ++ tailWord_7997517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997517).length < 2 ^ (prefixWord ++ tailWord_7997517).sum := by decide
  have hdescent : baseEnd_7997517 < baseStart_7997517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997540 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_7997540 : Nat := 118140960795 + 7997540 * 2 ^ 59
def prefixEnd_7997540 : Nat := 4983230072969 + 3 ^ 40 * 7997540 * 2
def baseEnd_7997540 : Nat := 4106582073558744821669989

theorem tailTrace_7997540 : CollatzResearch.WordTrace tailWord_7997540 prefixEnd_7997540 4106582073558744821669989 := by
  unfold tailWord_7997540
  simp only [CollatzResearch.WordTrace]
  refine ⟨145847123723142962967279037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194462831630857283956372049 145847123723142962967279037)
  ·
    refine ⟨54692671396178611112729639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145847123723142962967279037 54692671396178611112729639)
    ·
      refine ⟨82039007094267916669094459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54692671396178611112729639 82039007094267916669094459)
      ·
        refine ⟨123058510641401875003641689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82039007094267916669094459 123058510641401875003641689)
        ·
          refine ⟨92293882981051406252731267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123058510641401875003641689 92293882981051406252731267)
          ·
            refine ⟨138440824471577109379096901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92293882981051406252731267 138440824471577109379096901)
            ·
              refine ⟨25957654588420708008580669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138440824471577109379096901 25957654588420708008580669)
              ·
                refine ⟨9734120470657765503217751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25957654588420708008580669 9734120470657765503217751)
                ·
                  refine ⟨14601180705986648254826627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734120470657765503217751 14601180705986648254826627)
                  ·
                    refine ⟨21901771058979972382239941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14601180705986648254826627 21901771058979972382239941)
                    ·
                      refine ⟨4106582073558744821669989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21901771058979972382239941 4106582073558744821669989)
                      ·
                        rfl

theorem cell23_7997540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_7997540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997540 prefixEnd_7997540 := by exact prefixLift 7997540
  have htrace : WordTrace (prefixWord ++ tailWord_7997540) baseStart_7997540 baseEnd_7997540 := by
    simpa [prefixWord, tailWord_7997540, baseEnd_7997540] using wordTrace_append hprefix tailTrace_7997540
  have hstable : (prefixWord ++ tailWord_7997540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997540).length < 2 ^ (prefixWord ++ tailWord_7997540).sum := by decide
  have hdescent : baseEnd_7997540 < baseStart_7997540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997550 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_7997550 : Nat := 118140960795 + 7997550 * 2 ^ 59
def prefixEnd_7997550 : Nat := 4983230072969 + 3 ^ 40 * 7997550 * 2
def baseEnd_7997550 : Nat := 1368862402788429927514981

theorem tailTrace_7997550 : CollatzResearch.WordTrace tailWord_7997550 prefixEnd_7997550 1368862402788429927514981 := by
  unfold tailWord_7997550
  simp only [CollatzResearch.WordTrace]
  refine ⟨36461826522031212205302763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194463074784166465094948069 36461826522031212205302763)
  ·
    refine ⟨54692739783046818307954145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36461826522031212205302763 54692739783046818307954145)
    ·
      refine ⟨41019554837285113730965609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54692739783046818307954145 41019554837285113730965609)
      ·
        refine ⟨30764666127963835298224207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41019554837285113730965609 30764666127963835298224207)
        ·
          refine ⟨46146999191945752947336311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30764666127963835298224207 46146999191945752947336311)
          ·
            refine ⟨69220498787918629421004467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46146999191945752947336311 69220498787918629421004467)
            ·
              refine ⟨103830748181877944131506701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69220498787918629421004467 103830748181877944131506701)
              ·
                refine ⟨38936530568204229049315013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103830748181877944131506701 38936530568204229049315013)
                ·
                  refine ⟨7300599481538292946746565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38936530568204229049315013 7300599481538292946746565)
                  ·
                    refine ⟨1368862402788429927514981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300599481538292946746565 1368862402788429927514981)
                    ·
                      rfl

theorem cell23_7997550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_7997550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997550 prefixEnd_7997550 := by exact prefixLift 7997550
  have htrace : WordTrace (prefixWord ++ tailWord_7997550) baseStart_7997550 baseEnd_7997550 := by
    simpa [prefixWord, tailWord_7997550, baseEnd_7997550] using wordTrace_append hprefix tailTrace_7997550
  have hstable : (prefixWord ++ tailWord_7997550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997550).length < 2 ^ (prefixWord ++ tailWord_7997550).sum := by decide
  have hdescent : baseEnd_7997550 < baseStart_7997550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997594 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7997594 : Nat := 118140960795 + 7997594 * 2 ^ 59
def prefixEnd_7997594 : Nat := 4983230072969 + 3 ^ 40 * 7997594 * 2
def baseEnd_7997594 : Nat := 4106609801514087610394741

theorem tailTrace_7997594 : CollatzResearch.WordTrace tailWord_7997594 prefixEnd_7997594 4106609801514087610394741 := by
  unfold tailWord_7997594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72924054247022573289255959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194464144658726862104682557 72924054247022573289255959)
  ·
    refine ⟨109386081370533859933883939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72924054247022573289255959 109386081370533859933883939)
    ·
      refine ⟨164079122055800789900825909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109386081370533859933883939 164079122055800789900825909)
      ·
        refine ⟨15382417692731324053202429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164079122055800789900825909 15382417692731324053202429)
        ·
          refine ⟨5768406634774246519950911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15382417692731324053202429 5768406634774246519950911)
          ·
            refine ⟨8652609952161369779926367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768406634774246519950911 8652609952161369779926367)
            ·
              refine ⟨12978914928242054669889551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652609952161369779926367 12978914928242054669889551)
              ·
                refine ⟨19468372392363082004834327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978914928242054669889551 19468372392363082004834327)
                ·
                  refine ⟨29202558588544623007251491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19468372392363082004834327 29202558588544623007251491)
                  ·
                    refine ⟨43803837882816934510877237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29202558588544623007251491 43803837882816934510877237)
                    ·
                      refine ⟨4106609801514087610394741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43803837882816934510877237 4106609801514087610394741)
                      ·
                        rfl

theorem cell23_7997594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7997594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997594 prefixEnd_7997594 := by exact prefixLift 7997594
  have htrace : WordTrace (prefixWord ++ tailWord_7997594) baseStart_7997594 baseEnd_7997594 := by
    simpa [prefixWord, tailWord_7997594, baseEnd_7997594] using wordTrace_append hprefix tailTrace_7997594
  have hstable : (prefixWord ++ tailWord_7997594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997594).length < 2 ^ (prefixWord ++ tailWord_7997594).sum := by decide
  have hdescent : baseEnd_7997594 < baseStart_7997594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997614 : List Nat := [4, 1, 4, 2, 1, 2, 1, 8]
def baseStart_7997614 : Nat := 118140960795 + 7997614 * 2 ^ 59
def prefixEnd_7997614 : Nat := 4983230072969 + 3 ^ 40 * 7997614 * 2
def baseEnd_7997614 : Nat := 152097039671376945634987

theorem tailTrace_7997614 : CollatzResearch.WordTrace tailWord_7997614 prefixEnd_7997614 152097039671376945634987 := by
  unfold tailWord_7997614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462118306002229571593987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194464630965345224381834597 36462118306002229571593987)
  ·
    refine ⟨54693177459003344357390981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36462118306002229571593987 54693177459003344357390981)
    ·
      refine ⟨10254970773563127067010809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54693177459003344357390981 10254970773563127067010809)
      ·
        refine ⟨7691228080172345300258107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10254970773563127067010809 7691228080172345300258107)
        ·
          refine ⟨11536842120258517950387161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691228080172345300258107 11536842120258517950387161)
          ·
            refine ⟨8652631590193888462790371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11536842120258517950387161 8652631590193888462790371)
            ·
              refine ⟨12978947385290832694185557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652631590193888462790371 12978947385290832694185557)
              ·
                refine ⟨152097039671376945634987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12978947385290832694185557 152097039671376945634987)
                ·
                  rfl

theorem cell23_7997614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_7997614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997614 prefixEnd_7997614 := by exact prefixLift 7997614
  have htrace : WordTrace (prefixWord ++ tailWord_7997614) baseStart_7997614 baseEnd_7997614 := by
    simpa [prefixWord, tailWord_7997614, baseEnd_7997614] using wordTrace_append hprefix tailTrace_7997614
  have hstable : (prefixWord ++ tailWord_7997614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997614).length < 2 ^ (prefixWord ++ tailWord_7997614).sum := by decide
  have hdescent : baseEnd_7997614 < baseStart_7997614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997623 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 8]
def baseStart_7997623 : Nat := 118140960795 + 7997623 * 2 ^ 59
def prefixEnd_7997623 : Nat := 4983230072969 + 3 ^ 40 * 7997623 * 2
def baseEnd_7997623 : Nat := 1368874897484355998977369

theorem tailTrace_7997623 : CollatzResearch.WordTrace tailWord_7997623 prefixEnd_7997623 1368874897484355998977369 := by
  unfold tailWord_7997623
  simp only [CollatzResearch.WordTrace]
  refine ⟨291697274704985231109829523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194464849803323487406553015 291697274704985231109829523)
  ·
    refine ⟨437545912057477846664744285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291697274704985231109829523 437545912057477846664744285)
    ·
      refine ⟨164079717021554192499279107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437545912057477846664744285 164079717021554192499279107)
      ·
        refine ⟨246119575532331288748918661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164079717021554192499279107 246119575532331288748918661)
        ·
          refine ⟨46147420412312116640422249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246119575532331288748918661 46147420412312116640422249)
          ·
            refine ⟨34610565309234087480316687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46147420412312116640422249 34610565309234087480316687)
            ·
              refine ⟨51915847963851131220475031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34610565309234087480316687 51915847963851131220475031)
              ·
                refine ⟨77873771945776696830712547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51915847963851131220475031 77873771945776696830712547)
                ·
                  refine ⟨116810657918665045246068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77873771945776696830712547 116810657918665045246068821)
                  ·
                    refine ⟨1368874897484355998977369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116810657918665045246068821 1368874897484355998977369)
                    ·
                      rfl

theorem cell23_7997623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_7997623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997623 prefixEnd_7997623 := by exact prefixLift 7997623
  have htrace : WordTrace (prefixWord ++ tailWord_7997623) baseStart_7997623 baseEnd_7997623 := by
    simpa [prefixWord, tailWord_7997623, baseEnd_7997623] using wordTrace_append hprefix tailTrace_7997623
  have hstable : (prefixWord ++ tailWord_7997623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997623).length < 2 ^ (prefixWord ++ tailWord_7997623).sum := by decide
  have hdescent : baseEnd_7997623 < baseStart_7997623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997643 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_7997643 : Nat := 118140960795 + 7997643 * 2 ^ 59
def prefixEnd_7997643 : Nat := 4983230072969 + 3 ^ 40 * 7997643 * 2
def baseEnd_7997643 : Nat := 4106634962066157918682015

theorem tailTrace_7997643 : CollatzResearch.WordTrace tailWord_7997643 prefixEnd_7997643 4106634962066157918682015 := by
  unfold tailWord_7997643
  simp only [CollatzResearch.WordTrace]
  refine ⟨291698004164912774525557583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194465336109941849683705055 291698004164912774525557583)
  ·
    refine ⟨437547006247369161788336375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291698004164912774525557583 437547006247369161788336375)
    ·
      refine ⟨656320509371053742682504563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437547006247369161788336375 656320509371053742682504563)
      ·
        refine ⟨984480764056580614023756845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656320509371053742682504563 984480764056580614023756845)
        ·
          refine ⟨369180286521217730258908817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984480764056580614023756845 369180286521217730258908817)
          ·
            refine ⟨276885214890913297694181613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369180286521217730258908817 276885214890913297694181613)
            ·
              refine ⟨103831955584092486635318105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276885214890913297694181613 103831955584092486635318105)
              ·
                refine ⟨77873966688069364976488579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103831955584092486635318105 77873966688069364976488579)
                ·
                  refine ⟨116810950032104047464732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77873966688069364976488579 116810950032104047464732869)
                  ·
                    refine ⟨21902053131019508899637413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116810950032104047464732869 21902053131019508899637413)
                    ·
                      refine ⟨4106634962066157918682015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21902053131019508899637413 4106634962066157918682015)
                      ·
                        rfl

theorem cell23_7997643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_7997643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997643 prefixEnd_7997643 := by exact prefixLift 7997643
  have htrace : WordTrace (prefixWord ++ tailWord_7997643) baseStart_7997643 baseEnd_7997643 := by
    simpa [prefixWord, tailWord_7997643, baseEnd_7997643] using wordTrace_append hprefix tailTrace_7997643
  have hstable : (prefixWord ++ tailWord_7997643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997643).length < 2 ^ (prefixWord ++ tailWord_7997643).sum := by decide
  have hdescent : baseEnd_7997643 < baseStart_7997643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997647 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 4, 2, 2]
def baseStart_7997647 : Nat := 118140960795 + 7997647 * 2 ^ 59
def prefixEnd_7997647 : Nat := 4983230072969 + 3 ^ 40 * 7997647 * 2
def baseEnd_7997647 : Nat := 4106637015988775903031997

theorem tailTrace_7997647 : CollatzResearch.WordTrace tailWord_7997647 prefixEnd_7997647 4106637015988775903031997 := by
  unfold tailWord_7997647
  simp only [CollatzResearch.WordTrace]
  refine ⟨291698150056898283208703195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194465433371265522139135463 291698150056898283208703195)
  ·
    refine ⟨437547225085347424813054793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291698150056898283208703195 437547225085347424813054793)
    ·
      refine ⟨328160418814010568609791095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437547225085347424813054793 328160418814010568609791095)
      ·
        refine ⟨492240628221015852914686643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328160418814010568609791095 492240628221015852914686643)
        ·
          refine ⟨738360942331523779372029965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492240628221015852914686643 738360942331523779372029965)
          ·
            refine ⟨276885353374321417264511237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 738360942331523779372029965 276885353374321417264511237)
            ·
              refine ⟨51916003757685265737095857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276885353374321417264511237 51916003757685265737095857)
              ·
                refine ⟨38937002818263949302821893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51916003757685265737095857 38937002818263949302821893)
                ·
                  refine ⟨7300688028424490494279105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38937002818263949302821893 7300688028424490494279105)
                  ·
                    refine ⟨5475516021318367870709329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300688028424490494279105 5475516021318367870709329)
                    ·
                      refine ⟨4106637015988775903031997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475516021318367870709329 4106637015988775903031997)
                      ·
                        rfl

theorem cell23_7997647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2, 2].length) (baseStart_7997647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997647 prefixEnd_7997647 := by exact prefixLift 7997647
  have htrace : WordTrace (prefixWord ++ tailWord_7997647) baseStart_7997647 baseEnd_7997647 := by
    simpa [prefixWord, tailWord_7997647, baseEnd_7997647] using wordTrace_append hprefix tailTrace_7997647
  have hstable : (prefixWord ++ tailWord_7997647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997647).length < 2 ^ (prefixWord ++ tailWord_7997647).sum := by decide
  have hdescent : baseEnd_7997647 < baseStart_7997647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997683 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 7]
def baseStart_7997683 : Nat := 118140960795 + 7997683 * 2 ^ 59
def prefixEnd_7997683 : Nat := 4983230072969 + 3 ^ 40 * 7997683 * 2
def baseEnd_7997683 : Nat := 1368885167097445920727277

theorem tailTrace_7997683 : CollatzResearch.WordTrace tailWord_7997683 prefixEnd_7997683 1368885167097445920727277 := by
  unfold tailWord_7997683
  simp only [CollatzResearch.WordTrace]
  refine ⟨291699463084767861357013703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194466308723178574238009135 291699463084767861357013703)
  ·
    refine ⟨437549194627151792035520555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291699463084767861357013703 437549194627151792035520555)
    ·
      refine ⟨656323791940727688053280833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437549194627151792035520555 656323791940727688053280833)
      ·
        refine ⟨492242843955545766039960625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656323791940727688053280833 492242843955545766039960625)
        ·
          refine ⟨369182132966659324529970469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492242843955545766039960625 369182132966659324529970469)
          ·
            refine ⟨69221649931248623349369463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369182132966659324529970469 69221649931248623349369463)
            ·
              refine ⟨103832474896872935024054195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69221649931248623349369463 103832474896872935024054195)
              ·
                refine ⟨155748712345309402536081293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103832474896872935024054195 155748712345309402536081293)
                ·
                  refine ⟨58405767129491025951030485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155748712345309402536081293 58405767129491025951030485)
                  ·
                    refine ⟨1368885167097445920727277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58405767129491025951030485 1368885167097445920727277)
                    ·
                      rfl

theorem cell23_7997683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_7997683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997683 prefixEnd_7997683 := by exact prefixLift 7997683
  have htrace : WordTrace (prefixWord ++ tailWord_7997683) baseStart_7997683 baseEnd_7997683 := by
    simpa [prefixWord, tailWord_7997683, baseEnd_7997683] using wordTrace_append hprefix tailTrace_7997683
  have hstable : (prefixWord ++ tailWord_7997683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997683).length < 2 ^ (prefixWord ++ tailWord_7997683).sum := by decide
  have hdescent : baseEnd_7997683 < baseStart_7997683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997704 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 5]
def baseStart_7997704 : Nat := 118140960795 + 7997704 * 2 ^ 59
def prefixEnd_7997704 : Nat := 4983230072969 + 3 ^ 40 * 7997704 * 2
def baseEnd_7997704 : Nat := 456296253820675797779915

theorem tailTrace_7997704 : CollatzResearch.WordTrace tailWord_7997704 prefixEnd_7997704 456296253820675797779915 := by
  unfold tailWord_7997704
  simp only [CollatzResearch.WordTrace]
  refine ⟨145850114508845890971764083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194466819345127854629018777 145850114508845890971764083)
  ·
    refine ⟨218775171763268836457646125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145850114508845890971764083 218775171763268836457646125)
    ·
      refine ⟨82040689411225813671617297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218775171763268836457646125 82040689411225813671617297)
      ·
        refine ⟨61530517058419360253712973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82040689411225813671617297 61530517058419360253712973)
        ·
          refine ⟨23073943896907260095142365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61530517058419360253712973 23073943896907260095142365)
          ·
            refine ⟨8652728961340222535678387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23073943896907260095142365 8652728961340222535678387)
            ·
              refine ⟨12979093442010333803517581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652728961340222535678387 12979093442010333803517581)
              ·
                refine ⟨4867160040753875176319093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12979093442010333803517581 4867160040753875176319093)
                ·
                  refine ⟨456296253820675797779915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867160040753875176319093 456296253820675797779915)
                  ·
                    rfl

theorem cell23_7997704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 5].length) (baseStart_7997704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997704 prefixEnd_7997704 := by exact prefixLift 7997704
  have htrace : WordTrace (prefixWord ++ tailWord_7997704) baseStart_7997704 baseEnd_7997704 := by
    simpa [prefixWord, tailWord_7997704, baseEnd_7997704] using wordTrace_append hprefix tailTrace_7997704
  have hstable : (prefixWord ++ tailWord_7997704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997704).length < 2 ^ (prefixWord ++ tailWord_7997704).sum := by decide
  have hdescent : baseEnd_7997704 < baseStart_7997704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997710 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7997710 : Nat := 118140960795 + 7997710 * 2 ^ 59
def prefixEnd_7997710 : Nat := 4983230072969 + 3 ^ 40 * 7997710 * 2
def baseEnd_7997710 : Nat := 4106669365270009156544207

theorem tailTrace_7997710 : CollatzResearch.WordTrace tailWord_7997710 prefixEnd_7997710 4106669365270009156544207 := by
  unfold tailWord_7997710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462555981958755621030823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194466965237113363312164389 36462555981958755621030823)
  ·
    refine ⟨54693833972938133431546235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36462555981958755621030823 54693833972938133431546235)
    ·
      refine ⟨82040750959407200147319353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54693833972938133431546235 82040750959407200147319353)
      ·
        refine ⟨61530563219555400110489515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82040750959407200147319353 61530563219555400110489515)
        ·
          refine ⟨92295844829333100165734273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61530563219555400110489515 92295844829333100165734273)
          ·
            refine ⟨69221883621999825124300705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92295844829333100165734273 69221883621999825124300705)
            ·
              refine ⟨51916412716499868843225529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69221883621999825124300705 51916412716499868843225529)
              ·
                refine ⟨38937309537374901632419147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51916412716499868843225529 38937309537374901632419147)
                ·
                  refine ⟨58405964306062352448628721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38937309537374901632419147 58405964306062352448628721)
                  ·
                    refine ⟨43804473229546764336471541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58405964306062352448628721 43804473229546764336471541)
                    ·
                      refine ⟨4106669365270009156544207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43804473229546764336471541 4106669365270009156544207)
                      ·
                        rfl

theorem cell23_7997710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7997710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997710 prefixEnd_7997710 := by exact prefixLift 7997710
  have htrace : WordTrace (prefixWord ++ tailWord_7997710) baseStart_7997710 baseEnd_7997710 := by
    simpa [prefixWord, tailWord_7997710, baseEnd_7997710] using wordTrace_append hprefix tailTrace_7997710
  have hstable : (prefixWord ++ tailWord_7997710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997710).length < 2 ^ (prefixWord ++ tailWord_7997710).sum := by decide
  have hdescent : baseEnd_7997710 < baseStart_7997710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997740 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_7997740 : Nat := 118140960795 + 7997740 * 2 ^ 59
def prefixEnd_7997740 : Nat := 4983230072969 + 3 ^ 40 * 7997740 * 2
def baseEnd_7997740 : Nat := 4106684769689644039169069

theorem tailTrace_7997740 : CollatzResearch.WordTrace tailWord_7997740 prefixEnd_7997740 4106684769689644039169069 := by
  unfold tailWord_7997740
  simp only [CollatzResearch.WordTrace]
  refine ⟨145850771022780680045919337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194467694697040906727892449 145850771022780680045919337)
  ·
    refine ⟨109388078267085510034439503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145850771022780680045919337 109388078267085510034439503)
    ·
      refine ⟨164082117400628265051659255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109388078267085510034439503 164082117400628265051659255)
      ·
        refine ⟨246123176100942397577488883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164082117400628265051659255 246123176100942397577488883)
        ·
          refine ⟨369184764151413596366233325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246123176100942397577488883 369184764151413596366233325)
          ·
            refine ⟨138444286556780098637337497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369184764151413596366233325 138444286556780098637337497)
            ·
              refine ⟨103833214917585073978003123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138444286556780098637337497 103833214917585073978003123)
              ·
                refine ⟨155749822376377610967004685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103833214917585073978003123 155749822376377610967004685)
                ·
                  refine ⟨58406183391141604112626757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155749822376377610967004685 58406183391141604112626757)
                  ·
                    refine ⟨10951159385839050771117517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58406183391141604112626757 10951159385839050771117517)
                    ·
                      refine ⟨4106684769689644039169069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951159385839050771117517 4106684769689644039169069)
                      ·
                        rfl

theorem cell23_7997740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_7997740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997740 prefixEnd_7997740 := by exact prefixLift 7997740
  have htrace : WordTrace (prefixWord ++ tailWord_7997740) baseStart_7997740 baseEnd_7997740 := by
    simpa [prefixWord, tailWord_7997740, baseEnd_7997740] using wordTrace_append hprefix tailTrace_7997740
  have hstable : (prefixWord ++ tailWord_7997740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997740).length < 2 ^ (prefixWord ++ tailWord_7997740).sum := by decide
  have hdescent : baseEnd_7997740 < baseStart_7997740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997777 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 6]
def baseStart_7997777 : Nat := 118140960795 + 7997777 * 2 ^ 59
def prefixEnd_7997777 : Nat := 4983230072969 + 3 ^ 40 * 7997777 * 2
def baseEnd_7997777 : Nat := 456300418719317821600711

theorem tailTrace_7997777 : CollatzResearch.WordTrace tailWord_7997777 prefixEnd_7997777 456300418719317821600711 := by
  unfold tailWord_7997777
  simp only [CollatzResearch.WordTrace]
  refine ⟨291702891546427315410935585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194468594364284876940623723 291702891546427315410935585)
  ·
    refine ⟨218777168659820486558201689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291702891546427315410935585 218777168659820486558201689)
    ·
      refine ⟨164082876494865364918651267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218777168659820486558201689 164082876494865364918651267)
      ·
        refine ⟨246124314742298047377976901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164082876494865364918651267 246124314742298047377976901)
        ·
          refine ⟨46148309014180883883370669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246124314742298047377976901 46148309014180883883370669)
          ·
            refine ⟨17305615880317831456264001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46148309014180883883370669 17305615880317831456264001)
            ·
              refine ⟨12979211910238373592198001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17305615880317831456264001 12979211910238373592198001)
              ·
                refine ⟨9734408932678780194148501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12979211910238373592198001 9734408932678780194148501)
                ·
                  refine ⟨456300418719317821600711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9734408932678780194148501 456300418719317821600711)
                  ·
                    rfl

theorem cell23_7997777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_7997777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997777 prefixEnd_7997777 := by exact prefixLift 7997777
  have htrace : WordTrace (prefixWord ++ tailWord_7997777) baseStart_7997777 baseEnd_7997777 := by
    simpa [prefixWord, tailWord_7997777, baseEnd_7997777] using wordTrace_append hprefix tailTrace_7997777
  have hstable : (prefixWord ++ tailWord_7997777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997777).length < 2 ^ (prefixWord ++ tailWord_7997777).sum := by decide
  have hdescent : baseEnd_7997777 < baseStart_7997777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997781 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_7997781 : Nat := 118140960795 + 7997781 * 2 ^ 59
def prefixEnd_7997781 : Nat := 4983230072969 + 3 ^ 40 * 7997781 * 2
def baseEnd_7997781 : Nat := 1368901940798826126252127

theorem tailTrace_7997781 : CollatzResearch.WordTrace tailWord_7997781 prefixEnd_7997781 1368901940798826126252127 := by
  unfold tailWord_7997781
  simp only [CollatzResearch.WordTrace]
  refine ⟨291703037438412824094081197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194468691625608549396054131 291703037438412824094081197)
  ·
    refine ⟨109388639039404809035280449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291703037438412824094081197 109388639039404809035280449)
    ·
      refine ⟨82041479279553606776460337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109388639039404809035280449 82041479279553606776460337)
      ·
        refine ⟨61531109459665205082345253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82041479279553606776460337 61531109459665205082345253)
        ·
          refine ⟨11537083023687225952939735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61531109459665205082345253 11537083023687225952939735)
          ·
            refine ⟨17305624535530838929409603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537083023687225952939735 17305624535530838929409603)
            ·
              refine ⟨25958436803296258394114405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17305624535530838929409603 25958436803296258394114405)
              ·
                refine ⟨4867206900618048448896451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25958436803296258394114405 4867206900618048448896451)
                ·
                  refine ⟨7300810350927072673344677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867206900618048448896451 7300810350927072673344677)
                  ·
                    refine ⟨1368901940798826126252127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300810350927072673344677 1368901940798826126252127)
                    ·
                      rfl

theorem cell23_7997781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_7997781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997781 prefixEnd_7997781 := by exact prefixLift 7997781
  have htrace : WordTrace (prefixWord ++ tailWord_7997781) baseStart_7997781 baseEnd_7997781 := by
    simpa [prefixWord, tailWord_7997781, baseEnd_7997781] using wordTrace_append hprefix tailTrace_7997781
  have hstable : (prefixWord ++ tailWord_7997781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997781).length < 2 ^ (prefixWord ++ tailWord_7997781).sum := by decide
  have hdescent : baseEnd_7997781 < baseStart_7997781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997820 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_7997820 : Nat := 118140960795 + 7997820 * 2 ^ 59
def prefixEnd_7997820 : Nat := 4983230072969 + 3 ^ 40 * 7997820 * 2
def baseEnd_7997820 : Nat := 1368908616047334575389567

theorem tailTrace_7997820 : CollatzResearch.WordTrace tailWord_7997820 prefixEnd_7997820 1368908616047334575389567 := by
  unfold tailWord_7997820
  simp only [CollatzResearch.WordTrace]
  refine ⟨145852229942635766877375457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194469639923514355836500609 145852229942635766877375457)
  ·
    refine ⟨109389172456976825158031593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145852229942635766877375457 109389172456976825158031593)
    ·
      refine ⟨82041879342732618868523695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109389172456976825158031593 82041879342732618868523695)
      ·
        refine ⟨123062819014098928302785543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82041879342732618868523695 123062819014098928302785543)
        ·
          refine ⟨184594228521148392454178315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123062819014098928302785543 184594228521148392454178315)
          ·
            refine ⟨276891342781722588681267473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184594228521148392454178315 276891342781722588681267473)
            ·
              refine ⟨207668507086291941510950605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276891342781722588681267473 207668507086291941510950605)
              ·
                refine ⟨77875690157359478066606477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207668507086291941510950605 77875690157359478066606477)
                ·
                  refine ⟨29203383809009804274977429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77875690157359478066606477 29203383809009804274977429)
                  ·
                    refine ⟨1368908616047334575389567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29203383809009804274977429 1368908616047334575389567)
                    ·
                      rfl

theorem cell23_7997820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_7997820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997820 prefixEnd_7997820 := by exact prefixLift 7997820
  have htrace : WordTrace (prefixWord ++ tailWord_7997820) baseStart_7997820 baseEnd_7997820 := by
    simpa [prefixWord, tailWord_7997820, baseEnd_7997820] using wordTrace_append hprefix tailTrace_7997820
  have hstable : (prefixWord ++ tailWord_7997820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997820).length < 2 ^ (prefixWord ++ tailWord_7997820).sum := by decide
  have hdescent : baseEnd_7997820 < baseStart_7997820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997821 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_7997821 : Nat := 118140960795 + 7997821 * 2 ^ 59
def prefixEnd_7997821 : Nat := 4983230072969 + 3 ^ 40 * 7997821 * 2
def baseEnd_7997821 : Nat := 4106726361622658222256197

theorem tailTrace_7997821 : CollatzResearch.WordTrace tailWord_7997821 prefixEnd_7997821 4106726361622658222256197 := by
  unfold tailWord_7997821
  simp only [CollatzResearch.WordTrace]
  refine ⟨291704496358267910925537317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194469664238845273950358211 291704496358267910925537317)
  ·
    refine ⟨54694593067175233298538247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291704496358267910925537317 54694593067175233298538247)
    ·
      refine ⟨82041889600762849947807371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54694593067175233298538247 82041889600762849947807371)
      ·
        refine ⟨123062834401144274921711057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82041889600762849947807371 123062834401144274921711057)
        ·
          refine ⟨92297125800858206191283293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123062834401144274921711057 92297125800858206191283293)
          ·
            refine ⟨34611422175321827321731235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92297125800858206191283293 34611422175321827321731235)
            ·
              refine ⟨51917133262982740982596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34611422175321827321731235 51917133262982740982596853)
              ·
                refine ⟨4867231243404631967118455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51917133262982740982596853 4867231243404631967118455)
                ·
                  refine ⟨7300846865106947950677683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867231243404631967118455 7300846865106947950677683)
                  ·
                    refine ⟨10951270297660421926016525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300846865106947950677683 10951270297660421926016525)
                    ·
                      refine ⟨4106726361622658222256197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951270297660421926016525 4106726361622658222256197)
                      ·
                        rfl

theorem cell23_7997821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_7997821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997821 prefixEnd_7997821 := by exact prefixLift 7997821
  have htrace : WordTrace (prefixWord ++ tailWord_7997821) baseStart_7997821 baseEnd_7997821 := by
    simpa [prefixWord, tailWord_7997821, baseEnd_7997821] using wordTrace_append hprefix tailTrace_7997821
  have hstable : (prefixWord ++ tailWord_7997821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997821).length < 2 ^ (prefixWord ++ tailWord_7997821).sum := by decide
  have hdescent : baseEnd_7997821 < baseStart_7997821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997838 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7997838 : Nat := 118140960795 + 7997838 * 2 ^ 59
def prefixEnd_7997838 : Nat := 4983230072969 + 3 ^ 40 * 7997838 * 2
def baseEnd_7997838 : Nat := 4106735090793784655743619

theorem tailTrace_7997838 : CollatzResearch.WordTrace tailWord_7997838 prefixEnd_7997838 4106735090793784655743619 := by
  unfold tailWord_7997838
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463139549900790353613271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194470077599470881885937445 36463139549900790353613271)
  ·
    refine ⟨54694709324851185530419907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36463139549900790353613271 54694709324851185530419907)
    ·
      refine ⟨82042063987276778295629861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54694709324851185530419907 82042063987276778295629861)
      ·
        refine ⟨15382886997614395930430599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82042063987276778295629861 15382886997614395930430599)
        ·
          refine ⟨23074330496421593895645899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15382886997614395930430599 23074330496421593895645899)
          ·
            refine ⟨34611495744632390843468849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23074330496421593895645899 34611495744632390843468849)
            ·
              refine ⟨25958621808474293132601637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34611495744632390843468849 25958621808474293132601637)
              ·
                refine ⟨4867241589088929962362807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25958621808474293132601637 4867241589088929962362807)
                ·
                  refine ⟨7300862383633394943544211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867241589088929962362807 7300862383633394943544211)
                  ·
                    refine ⟨10951293575450092415316317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300862383633394943544211 10951293575450092415316317)
                    ·
                      refine ⟨4106735090793784655743619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951293575450092415316317 4106735090793784655743619)
                      ·
                        rfl

theorem cell23_7997838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7997838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997838 prefixEnd_7997838 := by exact prefixLift 7997838
  have htrace : WordTrace (prefixWord ++ tailWord_7997838) baseStart_7997838 baseEnd_7997838 := by
    simpa [prefixWord, tailWord_7997838, baseEnd_7997838] using wordTrace_append hprefix tailTrace_7997838
  have hstable : (prefixWord ++ tailWord_7997838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997838).length < 2 ^ (prefixWord ++ tailWord_7997838).sum := by decide
  have hdescent : baseEnd_7997838 < baseStart_7997838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997847 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7997847 : Nat := 118140960795 + 7997847 * 2 ^ 59
def prefixEnd_7997847 : Nat := 4983230072969 + 3 ^ 40 * 7997847 * 2
def baseEnd_7997847 : Nat := 4106739712119675120531077

theorem tailTrace_7997847 : CollatzResearch.WordTrace tailWord_7997847 prefixEnd_7997847 4106739712119675120531077 := by
  unfold tailWord_7997847
  simp only [CollatzResearch.WordTrace]
  refine ⟨291705444656173717365983795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194470296437449144910655863 291705444656173717365983795)
  ·
    refine ⟨437558166984260576048975693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291705444656173717365983795 437558166984260576048975693)
    ·
      refine ⟨164084312619097716018365885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437558166984260576048975693 164084312619097716018365885)
      ·
        refine ⟨61531617232161643506887207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164084312619097716018365885 61531617232161643506887207)
        ·
          refine ⟨92297425848242465260330811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61531617232161643506887207 92297425848242465260330811)
          ·
            refine ⟨138446138772363697890496217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92297425848242465260330811 138446138772363697890496217)
            ·
              refine ⟨103834604079272773417872163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138446138772363697890496217 103834604079272773417872163)
              ·
                refine ⟨155751906118909160126808245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103834604079272773417872163 155751906118909160126808245)
                ·
                  refine ⟨14601741198647733761888273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155751906118909160126808245 14601741198647733761888273)
                  ·
                    refine ⟨10951305898985800321416205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14601741198647733761888273 10951305898985800321416205)
                    ·
                      refine ⟨4106739712119675120531077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951305898985800321416205 4106739712119675120531077)
                      ·
                        rfl

theorem cell23_7997847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7997847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997847 prefixEnd_7997847 := by exact prefixLift 7997847
  have htrace : WordTrace (prefixWord ++ tailWord_7997847) baseStart_7997847 baseEnd_7997847 := by
    simpa [prefixWord, tailWord_7997847, baseEnd_7997847] using wordTrace_append hprefix tailTrace_7997847
  have hstable : (prefixWord ++ tailWord_7997847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997847).length < 2 ^ (prefixWord ++ tailWord_7997847).sum := by decide
  have hdescent : baseEnd_7997847 < baseStart_7997847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997880 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_7997880 : Nat := 118140960795 + 7997880 * 2 ^ 59
def prefixEnd_7997880 : Nat := 4983230072969 + 3 ^ 40 * 7997880 * 2
def baseEnd_7997880 : Nat := 1368918885660424497139475

theorem tailTrace_7997880 : CollatzResearch.WordTrace tailWord_7997880 prefixEnd_7997880 1368918885660424497139475 := by
  unfold tailWord_7997880
  simp only [CollatzResearch.WordTrace]
  refine ⟨145853324132527082000967547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194471098843369442667956729 145853324132527082000967547)
  ·
    refine ⟨218779986198790623001451321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145853324132527082000967547 218779986198790623001451321)
    ·
      refine ⟨164084989649092967251088491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218779986198790623001451321 164084989649092967251088491)
      ·
        refine ⟨246127484473639450876632737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164084989649092967251088491 246127484473639450876632737)
        ·
          refine ⟨184595613355229588157474553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246127484473639450876632737 184595613355229588157474553)
          ·
            refine ⟨138446710016422191118105915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184595613355229588157474553 138446710016422191118105915)
            ·
              refine ⟨207670065024633286677158873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138446710016422191118105915 207670065024633286677158873)
              ·
                refine ⟨155752548768474965007869155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207670065024633286677158873 155752548768474965007869155)
                ·
                  refine ⟨233628823152712447511803733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155752548768474965007869155 233628823152712447511803733)
                  ·
                    refine ⟨1368918885660424497139475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 233628823152712447511803733 1368918885660424497139475)
                    ·
                      rfl

theorem cell23_7997880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_7997880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997880 prefixEnd_7997880 := by exact prefixLift 7997880
  have htrace : WordTrace (prefixWord ++ tailWord_7997880) baseStart_7997880 baseEnd_7997880 := by
    simpa [prefixWord, tailWord_7997880, baseEnd_7997880] using wordTrace_append hprefix tailTrace_7997880
  have hstable : (prefixWord ++ tailWord_7997880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997880).length < 2 ^ (prefixWord ++ tailWord_7997880).sum := by decide
  have hdescent : baseEnd_7997880 < baseStart_7997880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997889 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7997889 : Nat := 118140960795 + 7997889 * 2 ^ 59
def prefixEnd_7997889 : Nat := 4983230072969 + 3 ^ 40 * 7997889 * 2
def baseEnd_7997889 : Nat := 4106761278307163956205885

theorem tailTrace_7997889 : CollatzResearch.WordTrace tailWord_7997889 prefixEnd_7997889 4106761278307163956205885 := by
  unfold tailWord_7997889
  simp only [CollatzResearch.WordTrace]
  refine ⟨291706976522021558539012721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194471317681347705692675147 291706976522021558539012721)
  ·
    refine ⟨218780232391516168904259541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291706976522021558539012721 218780232391516168904259541)
    ·
      refine ⟨5127661696676160208693583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218780232391516168904259541 5127661696676160208693583)
      ·
        refine ⟨7691492545014240313040375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127661696676160208693583 7691492545014240313040375)
        ·
          refine ⟨11537238817521360469560563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691492545014240313040375 11537238817521360469560563)
          ·
            refine ⟨17305858226282040704340845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537238817521360469560563 17305858226282040704340845)
            ·
              refine ⟨6489696834855765264127817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17305858226282040704340845 6489696834855765264127817)
              ·
                refine ⟨4867272626141823948095863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489696834855765264127817 4867272626141823948095863)
                ·
                  refine ⟨7300908939212735922143795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867272626141823948095863 7300908939212735922143795)
                  ·
                    refine ⟨10951363408819103883215693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300908939212735922143795 10951363408819103883215693)
                    ·
                      refine ⟨4106761278307163956205885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951363408819103883215693 4106761278307163956205885)
                      ·
                        rfl

theorem cell23_7997889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7997889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997889 prefixEnd_7997889 := by exact prefixLift 7997889
  have htrace : WordTrace (prefixWord ++ tailWord_7997889) baseStart_7997889 baseEnd_7997889 := by
    simpa [prefixWord, tailWord_7997889, baseEnd_7997889] using wordTrace_append hprefix tailTrace_7997889
  have hstable : (prefixWord ++ tailWord_7997889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997889).length < 2 ^ (prefixWord ++ tailWord_7997889).sum := by decide
  have hdescent : baseEnd_7997889 < baseStart_7997889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997895 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_7997895 : Nat := 118140960795 + 7997895 * 2 ^ 59
def prefixEnd_7997895 : Nat := 4983230072969 + 3 ^ 40 * 7997895 * 2
def baseEnd_7997895 : Nat := 4106764359191090932730857

theorem tailTrace_7997895 : CollatzResearch.WordTrace tailWord_7997895 prefixEnd_7997895 4106764359191090932730857 := by
  unfold tailWord_7997895
  simp only [CollatzResearch.WordTrace]
  refine ⟨291707195359999821563731139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194471463573333214375820759 291707195359999821563731139)
  ·
    refine ⟨437560793039999732345596709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291707195359999821563731139 437560793039999732345596709)
    ·
      refine ⟨82042648694999949814799383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437560793039999732345596709 82042648694999949814799383)
      ·
        refine ⟨123063973042499924722199075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82042648694999949814799383 123063973042499924722199075)
        ·
          refine ⟨184595959563749887083298613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123063973042499924722199075 184595959563749887083298613)
          ·
            refine ⟨17305871209101551914059245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184595959563749887083298613 17305871209101551914059245)
            ·
              refine ⟨6489701703413081967772217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17305871209101551914059245 6489701703413081967772217)
              ·
                refine ⟨4867276277559811475829163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489701703413081967772217 4867276277559811475829163)
                ·
                  refine ⟨7300914416339717213743745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867276277559811475829163 7300914416339717213743745)
                  ·
                    refine ⟨5475685812254787910307809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300914416339717213743745 5475685812254787910307809)
                    ·
                      refine ⟨4106764359191090932730857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475685812254787910307809 4106764359191090932730857)
                      ·
                        rfl

theorem cell23_7997895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_7997895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997895 prefixEnd_7997895 := by exact prefixLift 7997895
  have htrace : WordTrace (prefixWord ++ tailWord_7997895) baseStart_7997895 baseEnd_7997895 := by
    simpa [prefixWord, tailWord_7997895, baseEnd_7997895] using wordTrace_append hprefix tailTrace_7997895
  have hstable : (prefixWord ++ tailWord_7997895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997895).length < 2 ^ (prefixWord ++ tailWord_7997895).sum := by decide
  have hdescent : baseEnd_7997895 < baseStart_7997895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997937 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_7997937 : Nat := 118140960795 + 7997937 * 2 ^ 59
def prefixEnd_7997937 : Nat := 4983230072969 + 3 ^ 40 * 7997937 * 2
def baseEnd_7997937 : Nat := 4106785925378579768405663

theorem tailTrace_7997937 : CollatzResearch.WordTrace tailWord_7997937 prefixEnd_7997937 4106785925378579768405663 := by
  unfold tailWord_7997937
  simp only [CollatzResearch.WordTrace]
  refine ⟨291708727225847662736760065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194472484817231775157840043 291708727225847662736760065)
  ·
    refine ⟨218781545419385747052570049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291708727225847662736760065 218781545419385747052570049)
    ·
      refine ⟨164086159064539310289427537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218781545419385747052570049 164086159064539310289427537)
      ·
        refine ⟨123064619298404482717070653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164086159064539310289427537 123064619298404482717070653)
        ·
          refine ⟨46149232236901681018901495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123064619298404482717070653 46149232236901681018901495)
          ·
            refine ⟨69223848355352521528352243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46149232236901681018901495 69223848355352521528352243)
            ·
              refine ⟨103835772533028782292528365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69223848355352521528352243 103835772533028782292528365)
              ·
                refine ⟨38938414699885793359698137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103835772533028782292528365 38938414699885793359698137)
                ·
                  refine ⟨29203811024914345019773603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38938414699885793359698137 29203811024914345019773603)
                  ·
                    refine ⟨43805716537371517529660405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29203811024914345019773603 43805716537371517529660405)
                    ·
                      refine ⟨4106785925378579768405663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43805716537371517529660405 4106785925378579768405663)
                      ·
                        rfl

theorem cell23_7997937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_7997937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997937 prefixEnd_7997937 := by exact prefixLift 7997937
  have htrace : WordTrace (prefixWord ++ tailWord_7997937) baseStart_7997937 baseEnd_7997937 := by
    simpa [prefixWord, tailWord_7997937, baseEnd_7997937] using wordTrace_append hprefix tailTrace_7997937
  have hstable : (prefixWord ++ tailWord_7997937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997937).length < 2 ^ (prefixWord ++ tailWord_7997937).sum := by decide
  have hdescent : baseEnd_7997937 < baseStart_7997937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997964 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_7997964 : Nat := 118140960795 + 7997964 * 2 ^ 59
def prefixEnd_7997964 : Nat := 4983230072969 + 3 ^ 40 * 7997964 * 2
def baseEnd_7997964 : Nat := 4106799789356251162768039

theorem tailTrace_7997964 : CollatzResearch.WordTrace tailWord_7997964 prefixEnd_7997964 4106799789356251162768039 := by
  unfold tailWord_7997964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145854855998374923173996473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194473141331166564231995297 145854855998374923173996473)
  ·
    refine ⟨109391141998781192380497355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145854855998374923173996473 109391141998781192380497355)
    ·
      refine ⟨164086712998171788570746033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109391141998781192380497355 164086712998171788570746033)
      ·
        refine ⟨123065034748628841428059525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164086712998171788570746033 123065034748628841428059525)
        ·
          refine ⟨23074694015367907767761161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123065034748628841428059525 23074694015367907767761161)
          ·
            refine ⟨17306020511525930825820871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23074694015367907767761161 17306020511525930825820871)
            ·
              refine ⟨25959030767288896238731307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306020511525930825820871 25959030767288896238731307)
              ·
                refine ⟨38938546150933344358096961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25959030767288896238731307 38938546150933344358096961)
                ·
                  refine ⟨29203909613200008268572721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38938546150933344358096961 29203909613200008268572721)
                  ·
                    refine ⟨21902932209900006201429541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29203909613200008268572721 21902932209900006201429541)
                    ·
                      refine ⟨4106799789356251162768039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21902932209900006201429541 4106799789356251162768039)
                      ·
                        rfl

theorem cell23_7997964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_7997964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997964 prefixEnd_7997964 := by exact prefixLift 7997964
  have htrace : WordTrace (prefixWord ++ tailWord_7997964) baseStart_7997964 baseEnd_7997964 := by
    simpa [prefixWord, tailWord_7997964, baseEnd_7997964] using wordTrace_append hprefix tailTrace_7997964
  have hstable : (prefixWord ++ tailWord_7997964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997964).length < 2 ^ (prefixWord ++ tailWord_7997964).sum := by decide
  have hdescent : baseEnd_7997964 < baseStart_7997964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7997967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_7997967 : Nat := 118140960795 + 7997967 * 2 ^ 59
def prefixEnd_7997967 : Nat := 4983230072969 + 3 ^ 40 * 7997967 * 2
def baseEnd_7997967 : Nat := 4106801329798214651030525

theorem tailTrace_7997967 : CollatzResearch.WordTrace tailWord_7997967 prefixEnd_7997967 4106801329798214651030525 := by
  unfold tailWord_7997967
  simp only [CollatzResearch.WordTrace]
  refine ⟨291709821415738977860352155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194473214277159318573568103 291709821415738977860352155)
  ·
    refine ⟨437564732123608466790528233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291709821415738977860352155 437564732123608466790528233)
    ·
      refine ⟨328173549092706350092896175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437564732123608466790528233 328173549092706350092896175)
      ·
        refine ⟨492260323639059525139344263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328173549092706350092896175 492260323639059525139344263)
        ·
          refine ⟨738390485458589287709016395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492260323639059525139344263 738390485458589287709016395)
          ·
            refine ⟨1107585728187883931563524593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738390485458589287709016395 1107585728187883931563524593)
            ·
              refine ⟨830689296140912948672643445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107585728187883931563524593 830689296140912948672643445)
              ·
                refine ⟨77877121513210588938060323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830689296140912948672643445 77877121513210588938060323)
                ·
                  refine ⟨116815682269815883407090485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77877121513210588938060323 116815682269815883407090485)
                  ·
                    refine ⟨10951470212795239069414733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116815682269815883407090485 10951470212795239069414733)
                    ·
                      refine ⟨4106801329798214651030525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951470212795239069414733 4106801329798214651030525)
                      ·
                        rfl

theorem cell23_7997967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_7997967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7997967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7997967 prefixEnd_7997967 := by exact prefixLift 7997967
  have htrace : WordTrace (prefixWord ++ tailWord_7997967) baseStart_7997967 baseEnd_7997967 := by
    simpa [prefixWord, tailWord_7997967, baseEnd_7997967] using wordTrace_append hprefix tailTrace_7997967
  have hstable : (prefixWord ++ tailWord_7997967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7997967).length < 2 ^ (prefixWord ++ tailWord_7997967).sum := by decide
  have hdescent : baseEnd_7997967 < baseStart_7997967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7997967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998061 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7998061 : Nat := 118140960795 + 7998061 * 2 ^ 59
def prefixEnd_7998061 : Nat := 4983230072969 + 3 ^ 40 * 7998061 * 2
def baseEnd_7998061 : Nat := 4106849596979737283255093

theorem tailTrace_7998061 : CollatzResearch.WordTrace tailWord_7998061 prefixEnd_7998061 4106849596979737283255093 := by
  unfold tailWord_7998061
  simp only [CollatzResearch.WordTrace]
  refine ⟨291713249877398431914274037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194475499918265621276182691 291713249877398431914274037)
  ·
    refine ⟨27348117176006102991963191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291713249877398431914274037 27348117176006102991963191)
    ·
      refine ⟨41022175764009154487944787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27348117176006102991963191 41022175764009154487944787)
      ·
        refine ⟨61533263646013731731917181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41022175764009154487944787 61533263646013731731917181)
        ·
          refine ⟨23074973867255149399468943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61533263646013731731917181 23074973867255149399468943)
          ·
            refine ⟨34612460800882724099203415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23074973867255149399468943 34612460800882724099203415)
            ·
              refine ⟨51918691201324086148805123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34612460800882724099203415 51918691201324086148805123)
              ·
                refine ⟨77878036801986129223207685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51918691201324086148805123 77878036801986129223207685)
                ·
                  refine ⟨14602131900372399229351441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77878036801986129223207685 14602131900372399229351441)
                  ·
                    refine ⟨10951598925279299422013581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14602131900372399229351441 10951598925279299422013581)
                    ·
                      refine ⟨4106849596979737283255093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951598925279299422013581 4106849596979737283255093)
                      ·
                        rfl

theorem cell23_7998061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7998061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998061 prefixEnd_7998061 := by exact prefixLift 7998061
  have htrace : WordTrace (prefixWord ++ tailWord_7998061) baseStart_7998061 baseEnd_7998061 := by
    simpa [prefixWord, tailWord_7998061, baseEnd_7998061] using wordTrace_append hprefix tailTrace_7998061
  have hstable : (prefixWord ++ tailWord_7998061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998061).length < 2 ^ (prefixWord ++ tailWord_7998061).sum := by decide
  have hdescent : baseEnd_7998061 < baseStart_7998061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998067 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_7998067 : Nat := 118140960795 + 7998067 * 2 ^ 59
def prefixEnd_7998067 : Nat := 4983230072969 + 3 ^ 40 * 7998067 * 2
def baseEnd_7998067 : Nat := 4106852677863664259780065

theorem tailTrace_7998067 : CollatzResearch.WordTrace tailWord_7998067 prefixEnd_7998067 4106852677863664259780065 := by
  unfold tailWord_7998067
  simp only [CollatzResearch.WordTrace]
  refine ⟨291713468715376694938992455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194475645810251129959328303 291713468715376694938992455)
  ·
    refine ⟨437570203073065042408488683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291713468715376694938992455 437570203073065042408488683)
    ·
      refine ⟨656355304609597563612733025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437570203073065042408488683 656355304609597563612733025)
      ·
        refine ⟨492266478457198172709549769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656355304609597563612733025 492266478457198172709549769)
        ·
          refine ⟨369199858842898629532162327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492266478457198172709549769 369199858842898629532162327)
          ·
            refine ⟨553799788264347944298243491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369199858842898629532162327 553799788264347944298243491)
            ·
              refine ⟨830699682396521916447365237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553799788264347944298243491 830699682396521916447365237)
              ·
                refine ⟨77878095224673929666940491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830699682396521916447365237 77878095224673929666940491)
                ·
                  refine ⟨116817142837010894500410737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77878095224673929666940491 116817142837010894500410737)
                  ·
                    refine ⟨87612857127758170875308053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116817142837010894500410737 87612857127758170875308053)
                    ·
                      refine ⟨4106852677863664259780065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87612857127758170875308053 4106852677863664259780065)
                      ·
                        rfl

theorem cell23_7998067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_7998067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998067 prefixEnd_7998067 := by exact prefixLift 7998067
  have htrace : WordTrace (prefixWord ++ tailWord_7998067) baseStart_7998067 baseEnd_7998067 := by
    simpa [prefixWord, tailWord_7998067, baseEnd_7998067] using wordTrace_append hprefix tailTrace_7998067
  have hstable : (prefixWord ++ tailWord_7998067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998067).length < 2 ^ (prefixWord ++ tailWord_7998067).sum := by decide
  have hdescent : baseEnd_7998067 < baseStart_7998067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998119 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7998119 : Nat := 118140960795 + 7998119 * 2 ^ 59
def prefixEnd_7998119 : Nat := 4983230072969 + 3 ^ 40 * 7998119 * 2
def baseEnd_7998119 : Nat := 1368959792952566018776609

theorem tailTrace_7998119 : CollatzResearch.WordTrace tailWord_7998119 prefixEnd_7998119 1368959792952566018776609 := by
  unfold tailWord_7998119
  simp only [CollatzResearch.WordTrace]
  refine ⟨291715365311188307819885411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194476910207458871879923607 291715365311188307819885411)
  ·
    refine ⟨437573047966782461729828117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291715365311188307819885411 437573047966782461729828117)
    ·
      refine ⟨20511236623442927893585693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 437573047966782461729828117 20511236623442927893585693)
      ·
        refine ⟨7691713733791097960094635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20511236623442927893585693 7691713733791097960094635)
        ·
          refine ⟨11537570600686646940141953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691713733791097960094635 11537570600686646940141953)
          ·
            refine ⟨8653177950514985205106465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11537570600686646940141953 8653177950514985205106465)
            ·
              refine ⟨6489883462886238903829849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653177950514985205106465 6489883462886238903829849)
              ·
                refine ⟨4867412597164679177872387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489883462886238903829849 4867412597164679177872387)
                ·
                  refine ⟨7301118895747018766808581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867412597164679177872387 7301118895747018766808581)
                  ·
                    refine ⟨1368959792952566018776609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301118895747018766808581 1368959792952566018776609)
                    ·
                      rfl

theorem cell23_7998119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7998119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998119 prefixEnd_7998119 := by exact prefixLift 7998119
  have htrace : WordTrace (prefixWord ++ tailWord_7998119) baseStart_7998119 baseEnd_7998119 := by
    simpa [prefixWord, tailWord_7998119, baseEnd_7998119] using wordTrace_append hprefix tailTrace_7998119
  have hstable : (prefixWord ++ tailWord_7998119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998119).length < 2 ^ (prefixWord ++ tailWord_7998119).sum := by decide
  have hdescent : baseEnd_7998119 < baseStart_7998119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998141 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7998141 : Nat := 118140960795 + 7998141 * 2 ^ 59
def prefixEnd_7998141 : Nat := 4983230072969 + 3 ^ 40 * 7998141 * 2
def baseEnd_7998141 : Nat := 1368963558477365656751575

theorem tailTrace_7998141 : CollatzResearch.WordTrace tailWord_7998141 prefixEnd_7998141 1368963558477365656751575 := by
  unfold tailWord_7998141
  simp only [CollatzResearch.WordTrace]
  refine ⟨291716167717108605577186277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194477445144739070384790851 291716167717108605577186277)
  ·
    refine ⟨54696781446957863545722427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291716167717108605577186277 54696781446957863545722427)
    ·
      refine ⟨82045172170436795318583641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54696781446957863545722427 82045172170436795318583641)
      ·
        refine ⟨61533879127827596488937731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82045172170436795318583641 61533879127827596488937731)
        ·
          refine ⟨92300818691741394733406597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61533879127827596488937731 92300818691741394733406597)
          ·
            refine ⟨17306403504701511512513737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92300818691741394733406597 17306403504701511512513737)
            ·
              refine ⟨12979802628526133634385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17306403504701511512513737 12979802628526133634385303)
              ·
                refine ⟨19469703942789200451577955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12979802628526133634385303 19469703942789200451577955)
                ·
                  refine ⟨29204555914183800677366933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19469703942789200451577955 29204555914183800677366933)
                  ·
                    refine ⟨1368963558477365656751575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29204555914183800677366933 1368963558477365656751575)
                    ·
                      rfl

theorem cell23_7998141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7998141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998141 prefixEnd_7998141 := by exact prefixLift 7998141
  have htrace : WordTrace (prefixWord ++ tailWord_7998141) baseStart_7998141 baseEnd_7998141 := by
    simpa [prefixWord, tailWord_7998141, baseEnd_7998141] using wordTrace_append hprefix tailTrace_7998141
  have hstable : (prefixWord ++ tailWord_7998141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998141).length < 2 ^ (prefixWord ++ tailWord_7998141).sum := by decide
  have hdescent : baseEnd_7998141 < baseStart_7998141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998162 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_7998162 : Nat := 118140960795 + 7998162 * 2 ^ 59
def prefixEnd_7998162 : Nat := 4983230072969 + 3 ^ 40 * 7998162 * 2
def baseEnd_7998162 : Nat := 1368967152841947129364043

theorem tailTrace_7998162 : CollatzResearch.WordTrace tailWord_7998162 prefixEnd_7998162 1368967152841947129364043 := by
  unfold tailWord_7998162
  simp only [CollatzResearch.WordTrace]
  refine ⟨72929233412508131540925185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194477955766688350775800493 72929233412508131540925185)
  ·
    refine ⟨54696925059381098655693889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72929233412508131540925185 54696925059381098655693889)
    ·
      refine ⟨41022693794535823991770417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54696925059381098655693889 41022693794535823991770417)
      ·
        refine ⟨30767020345901867993827813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41022693794535823991770417 30767020345901867993827813)
        ·
          refine ⟨5768816314856600248842715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30767020345901867993827813 5768816314856600248842715)
          ·
            refine ⟨8653224472284900373264073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768816314856600248842715 8653224472284900373264073)
            ·
              refine ⟨6489918354213675279948055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653224472284900373264073 6489918354213675279948055)
              ·
                refine ⟨9734877531320512919922083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489918354213675279948055 9734877531320512919922083)
                ·
                  refine ⟨14602316296980769379883125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734877531320512919922083 14602316296980769379883125)
                  ·
                    refine ⟨1368967152841947129364043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14602316296980769379883125 1368967152841947129364043)
                    ·
                      rfl

theorem cell23_7998162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_7998162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998162 prefixEnd_7998162 := by exact prefixLift 7998162
  have htrace : WordTrace (prefixWord ++ tailWord_7998162) baseStart_7998162 baseEnd_7998162 := by
    simpa [prefixWord, tailWord_7998162, baseEnd_7998162] using wordTrace_append hprefix tailTrace_7998162
  have hstable : (prefixWord ++ tailWord_7998162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998162).length < 2 ^ (prefixWord ++ tailWord_7998162).sum := by decide
  have hdescent : baseEnd_7998162 < baseStart_7998162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998165 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7998165 : Nat := 118140960795 + 7998165 * 2 ^ 59
def prefixEnd_7998165 : Nat := 4983230072969 + 3 ^ 40 * 7998165 * 2
def baseEnd_7998165 : Nat := 4106902998967804876354615

theorem tailTrace_7998165 : CollatzResearch.WordTrace tailWord_7998165 prefixEnd_7998165 4106902998967804876354615 := by
  unfold tailWord_7998165
  simp only [CollatzResearch.WordTrace]
  refine ⟨291717043069021657676059949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194478028712681105117373299 291717043069021657676059949)
  ·
    refine ⟨109393891150883121628522481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291717043069021657676059949 109393891150883121628522481)
    ·
      refine ⟨82045418363162341221391861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109393891150883121628522481 82045418363162341221391861)
      ·
        refine ⟨7691757971546469489505487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82045418363162341221391861 7691757971546469489505487)
        ·
          refine ⟨11537636957319704234258231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691757971546469489505487 11537636957319704234258231)
          ·
            refine ⟨17306455435979556351387347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537636957319704234258231 17306455435979556351387347)
            ·
              refine ⟨25959683153969334527081021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306455435979556351387347 25959683153969334527081021)
              ·
                refine ⟨9734881182738500447655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25959683153969334527081021 9734881182738500447655383)
                ·
                  refine ⟨14602321774107750671483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734881182738500447655383 14602321774107750671483075)
                  ·
                    refine ⟨21903482661161626007224613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14602321774107750671483075 21903482661161626007224613)
                    ·
                      refine ⟨4106902998967804876354615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21903482661161626007224613 4106902998967804876354615)
                      ·
                        rfl

theorem cell23_7998165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7998165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998165 prefixEnd_7998165 := by exact prefixLift 7998165
  have htrace : WordTrace (prefixWord ++ tailWord_7998165) baseStart_7998165 baseEnd_7998165 := by
    simpa [prefixWord, tailWord_7998165, baseEnd_7998165] using wordTrace_append hprefix tailTrace_7998165
  have hstable : (prefixWord ++ tailWord_7998165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998165).length < 2 ^ (prefixWord ++ tailWord_7998165).sum := by decide
  have hdescent : baseEnd_7998165 < baseStart_7998165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998168 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_7998168 : Nat := 118140960795 + 7998168 * 2 ^ 59
def prefixEnd_7998168 : Nat := 4983230072969 + 3 ^ 40 * 7998168 * 2
def baseEnd_7998168 : Nat := 4106904539409768364617101

theorem tailTrace_7998168 : CollatzResearch.WordTrace tailWord_7998168 prefixEnd_7998168 4106904539409768364617101 := by
  unfold tailWord_7998168
  simp only [CollatzResearch.WordTrace]
  refine ⟨145858576244005394594209579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194478101658673859458946105 145858576244005394594209579)
  ·
    refine ⟨218787864366008091891314369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145858576244005394594209579 218787864366008091891314369)
    ·
      refine ⟨164090898274506068918485777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218787864366008091891314369 164090898274506068918485777)
      ·
        refine ⟨123068173705879551688864333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164090898274506068918485777 123068173705879551688864333)
        ·
          refine ⟨46150565139704831883324125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123068173705879551688864333 46150565139704831883324125)
          ·
            refine ⟨17306461927389311956246547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46150565139704831883324125 17306461927389311956246547)
            ·
              refine ⟨25959692891083967934369821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306461927389311956246547 25959692891083967934369821)
              ·
                refine ⟨9734884834156487975388683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25959692891083967934369821 9734884834156487975388683)
                ·
                  refine ⟨14602327251234731963083025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734884834156487975388683 14602327251234731963083025)
                  ·
                    refine ⟨10951745438426048972312269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14602327251234731963083025 10951745438426048972312269)
                    ·
                      refine ⟨4106904539409768364617101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951745438426048972312269 4106904539409768364617101)
                      ·
                        rfl

theorem cell23_7998168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_7998168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998168 prefixEnd_7998168 := by exact prefixLift 7998168
  have htrace : WordTrace (prefixWord ++ tailWord_7998168) baseStart_7998168 baseEnd_7998168 := by
    simpa [prefixWord, tailWord_7998168, baseEnd_7998168] using wordTrace_append hprefix tailTrace_7998168
  have hstable : (prefixWord ++ tailWord_7998168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998168).length < 2 ^ (prefixWord ++ tailWord_7998168).sum := by decide
  have hdescent : baseEnd_7998168 < baseStart_7998168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998241 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7998241 : Nat := 118140960795 + 7998241 * 2 ^ 59
def prefixEnd_7998241 : Nat := 4983230072969 + 3 ^ 40 * 7998241 * 2
def baseEnd_7998241 : Nat := 4106942023497546579004265

theorem tailTrace_7998241 : CollatzResearch.WordTrace tailWord_7998241 prefixEnd_7998241 4106942023497546579004265 := by
  unfold tailWord_7998241
  simp only [CollatzResearch.WordTrace]
  refine ⟨291719815016746322655826577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194479876677830881770551051 291719815016746322655826577)
  ·
    refine ⟨218789861262559741991869933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291719815016746322655826577 218789861262559741991869933)
    ·
      refine ⟨82046197973459903246951225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218789861262559741991869933 82046197973459903246951225)
      ·
        refine ⟨61534648480094927435213419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82046197973459903246951225 61534648480094927435213419)
        ·
          refine ⟨92301972720142391152820129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61534648480094927435213419 92301972720142391152820129)
          ·
            refine ⟨69226479540106793364615097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92301972720142391152820129 69226479540106793364615097)
            ·
              refine ⟨51919859655080095023461323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69226479540106793364615097 51919859655080095023461323)
              ·
                refine ⟨77879789482620142535191985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51919859655080095023461323 77879789482620142535191985)
                ·
                  refine ⟨58409842111965106901393989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77879789482620142535191985 58409842111965106901393989)
                  ·
                    refine ⟨10951845395993457544011373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58409842111965106901393989 10951845395993457544011373)
                    ·
                      refine ⟨4106942023497546579004265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951845395993457544011373 4106942023497546579004265)
                      ·
                        rfl

theorem cell23_7998241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7998241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998241 prefixEnd_7998241 := by exact prefixLift 7998241
  have htrace : WordTrace (prefixWord ++ tailWord_7998241) baseStart_7998241 baseEnd_7998241 := by
    simpa [prefixWord, tailWord_7998241, baseEnd_7998241] using wordTrace_append hprefix tailTrace_7998241
  have hstable : (prefixWord ++ tailWord_7998241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998241).length < 2 ^ (prefixWord ++ tailWord_7998241).sum := by decide
  have hdescent : baseEnd_7998241 < baseStart_7998241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998276 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7998276 : Nat := 118140960795 + 7998276 * 2 ^ 59
def prefixEnd_7998276 : Nat := 4983230072969 + 3 ^ 40 * 7998276 * 2
def baseEnd_7998276 : Nat := 4106959995320453942066605

theorem tailTrace_7998276 : CollatzResearch.WordTrace tailWord_7998276 prefixEnd_7998276 4106959995320453942066605 := by
  unfold tailWord_7998276
  simp only [CollatzResearch.WordTrace]
  refine ⟨145860545785809761816675341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194480727714413015755567121 145860545785809761816675341)
  ·
    refine ⟨54697704669678660681253253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145860545785809761816675341 54697704669678660681253253)
    ·
      refine ⟨10255819625564748877734985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54697704669678660681253253 10255819625564748877734985)
      ·
        refine ⟨7691864719173561658301239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10255819625564748877734985 7691864719173561658301239)
        ·
          refine ⟨11537797078760342487451859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691864719173561658301239 11537797078760342487451859)
          ·
            refine ⟨17306695618140513731177789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537797078760342487451859 17306695618140513731177789)
            ·
              refine ⟨6490010856802692649191671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17306695618140513731177789 6490010856802692649191671)
              ·
                refine ⟨9735016285204038973787507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490010856802692649191671 9735016285204038973787507)
                ·
                  refine ⟨14602524427806058460681261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735016285204038973787507 14602524427806058460681261)
                  ·
                    refine ⟨5475946660427271922755473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14602524427806058460681261 5475946660427271922755473)
                    ·
                      refine ⟨4106959995320453942066605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475946660427271922755473 4106959995320453942066605)
                      ·
                        rfl

theorem cell23_7998276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7998276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998276 prefixEnd_7998276 := by exact prefixLift 7998276
  have htrace : WordTrace (prefixWord ++ tailWord_7998276) baseStart_7998276 baseEnd_7998276 := by
    simpa [prefixWord, tailWord_7998276, baseEnd_7998276] using wordTrace_append hprefix tailTrace_7998276
  have hstable : (prefixWord ++ tailWord_7998276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998276).length < 2 ^ (prefixWord ++ tailWord_7998276).sum := by decide
  have hdescent : baseEnd_7998276 < baseStart_7998276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998295 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 5]
def baseStart_7998295 : Nat := 118140960795 + 7998295 * 2 ^ 59
def prefixEnd_7998295 : Nat := 4983230072969 + 3 ^ 40 * 7998295 * 2
def baseEnd_7998295 : Nat := 456329972383654374192113

theorem tailTrace_7998295 : CollatzResearch.WordTrace tailWord_7998295 prefixEnd_7998295 456329972383654374192113 := by
  unfold tailWord_7998295
  simp only [CollatzResearch.WordTrace]
  refine ⟨291721784558550689878292339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194481189705700459918861559 291721784558550689878292339)
  ·
    refine ⟨437582676837826034817438509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291721784558550689878292339 437582676837826034817438509)
    ·
      refine ⟨164093503814184763056539441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437582676837826034817438509 164093503814184763056539441)
      ·
        refine ⟨123070127860638572292404581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164093503814184763056539441 123070127860638572292404581)
        ·
          refine ⟨23075648973869732304825859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123070127860638572292404581 23075648973869732304825859)
          ·
            refine ⟨34613473460804598457238789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23075648973869732304825859 34613473460804598457238789)
            ·
              refine ⟨6490026273900862210732273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34613473460804598457238789 6490026273900862210732273)
              ·
                refine ⟨4867519705425646658049205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6490026273900862210732273 4867519705425646658049205)
                ·
                  refine ⟨456329972383654374192113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867519705425646658049205 456329972383654374192113)
                  ·
                    rfl

theorem cell23_7998295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 5].length) (baseStart_7998295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998295 prefixEnd_7998295 := by exact prefixLift 7998295
  have htrace : WordTrace (prefixWord ++ tailWord_7998295) baseStart_7998295 baseEnd_7998295 := by
    simpa [prefixWord, tailWord_7998295, baseEnd_7998295] using wordTrace_append hprefix tailTrace_7998295
  have hstable : (prefixWord ++ tailWord_7998295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998295).length < 2 ^ (prefixWord ++ tailWord_7998295).sum := by decide
  have hdescent : baseEnd_7998295 < baseStart_7998295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998298 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_7998298 : Nat := 118140960795 + 7998298 * 2 ^ 59
def prefixEnd_7998298 : Nat := 4983230072969 + 3 ^ 40 * 7998298 * 2
def baseEnd_7998298 : Nat := 4106971291894852855991503

theorem tailTrace_7998298 : CollatzResearch.WordTrace tailWord_7998298 prefixEnd_7998298 4106971291894852855991503 := by
  unfold tailWord_7998298
  simp only [CollatzResearch.WordTrace]
  refine ⟨72930473494384955347662887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194481262651693214260434365 72930473494384955347662887)
  ·
    refine ⟨109395710241577433021494331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72930473494384955347662887 109395710241577433021494331)
    ·
      refine ⟨164093565362366149532241497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109395710241577433021494331 164093565362366149532241497)
      ·
        refine ⟨123070174021774612149181123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164093565362366149532241497 123070174021774612149181123)
        ·
          refine ⟨184605261032661918223771685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123070174021774612149181123 184605261032661918223771685)
          ·
            refine ⟨34613486443624109666957191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184605261032661918223771685 34613486443624109666957191)
            ·
              refine ⟨51920229665436164500435787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34613486443624109666957191 51920229665436164500435787)
              ·
                refine ⟨77880344498154246750653681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51920229665436164500435787 77880344498154246750653681)
                ·
                  refine ⟨58410258373615685062990261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77880344498154246750653681 58410258373615685062990261)
                  ·
                    refine ⟨5475961722526470474655337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58410258373615685062990261 5475961722526470474655337)
                    ·
                      refine ⟨4106971291894852855991503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5475961722526470474655337 4106971291894852855991503)
                      ·
                        rfl

theorem cell23_7998298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_7998298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998298 prefixEnd_7998298 := by exact prefixLift 7998298
  have htrace : WordTrace (prefixWord ++ tailWord_7998298) baseStart_7998298 baseEnd_7998298 := by
    simpa [prefixWord, tailWord_7998298, baseEnd_7998298] using wordTrace_append hprefix tailTrace_7998298
  have hstable : (prefixWord ++ tailWord_7998298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998298).length < 2 ^ (prefixWord ++ tailWord_7998298).sum := by decide
  have hdescent : baseEnd_7998298 < baseStart_7998298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998325 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7998325 : Nat := 118140960795 + 7998325 * 2 ^ 59
def prefixEnd_7998325 : Nat := 4983230072969 + 3 ^ 40 * 7998325 * 2
def baseEnd_7998325 : Nat := 1368995051957508083451293

theorem tailTrace_7998325 : CollatzResearch.WordTrace tailWord_7998325 prefixEnd_7998325 1368995051957508083451293 := by
  unfold tailWord_7998325
  simp only [CollatzResearch.WordTrace]
  refine ⟨291722878748442005001884429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194481919165628003334589619 291722878748442005001884429)
  ·
    refine ⟨109396079530665751875706661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291722878748442005001884429 109396079530665751875706661)
    ·
      refine ⟨20511764911999828476694999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109396079530665751875706661 20511764911999828476694999)
      ·
        refine ⟨30767647367999742715042499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20511764911999828476694999 30767647367999742715042499)
        ·
          refine ⟨46151471051999614072563749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30767647367999742715042499 46151471051999614072563749)
          ·
            refine ⟨8653400822249927638605703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46151471051999614072563749 8653400822249927638605703)
            ·
              refine ⟨12980101233374891457908555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653400822249927638605703 12980101233374891457908555)
              ·
                refine ⟨19470151850062337186862833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12980101233374891457908555 19470151850062337186862833)
                ·
                  refine ⟨14602613887546752890147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19470151850062337186862833 14602613887546752890147125)
                  ·
                    refine ⟨1368995051957508083451293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14602613887546752890147125 1368995051957508083451293)
                    ·
                      rfl

theorem cell23_7998325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7998325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998325 prefixEnd_7998325 := by exact prefixLift 7998325
  have htrace : WordTrace (prefixWord ++ tailWord_7998325) baseStart_7998325 baseEnd_7998325 := by
    simpa [prefixWord, tailWord_7998325, baseEnd_7998325] using wordTrace_append hprefix tailTrace_7998325
  have hstable : (prefixWord ++ tailWord_7998325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998325).length < 2 ^ (prefixWord ++ tailWord_7998325).sum := by decide
  have hdescent : baseEnd_7998325 < baseStart_7998325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998341 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_7998341 : Nat := 118140960795 + 7998341 * 2 ^ 59
def prefixEnd_7998341 : Nat := 4983230072969 + 3 ^ 40 * 7998341 * 2
def baseEnd_7998341 : Nat := 4106993371562996187753805

theorem tailTrace_7998341 : CollatzResearch.WordTrace tailWord_7998341 prefixEnd_7998341 4106993371562996187753805 := by
  unfold tailWord_7998341
  simp only [CollatzResearch.WordTrace]
  refine ⟨291723462316384039734466877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194482308210922693156311251 291723462316384039734466877)
  ·
    refine ⟨109396298368644014900425079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291723462316384039734466877 109396298368644014900425079)
    ·
      refine ⟨164094447552966022350637619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109396298368644014900425079 164094447552966022350637619)
      ·
        refine ⟨246141671329449033525956429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164094447552966022350637619 246141671329449033525956429)
        ·
          refine ⟨92303126748543387572233661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246141671329449033525956429 92303126748543387572233661)
          ·
            refine ⟨34613672530703770339587623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92303126748543387572233661 34613672530703770339587623)
            ·
              refine ⟨51920508796055655509381435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34613672530703770339587623 51920508796055655509381435)
              ·
                refine ⟨77880763194083483264072153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51920508796055655509381435 77880763194083483264072153)
                ·
                  refine ⟨58410572395562612448054115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77880763194083483264072153 58410572395562612448054115)
                  ·
                    refine ⟨87615858593343918672081173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58410572395562612448054115 87615858593343918672081173)
                    ·
                      refine ⟨4106993371562996187753805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87615858593343918672081173 4106993371562996187753805)
                      ·
                        rfl

theorem cell23_7998341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_7998341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998341 prefixEnd_7998341 := by exact prefixLift 7998341
  have htrace : WordTrace (prefixWord ++ tailWord_7998341) baseStart_7998341 baseEnd_7998341 := by
    simpa [prefixWord, tailWord_7998341, baseEnd_7998341] using wordTrace_append hprefix tailTrace_7998341
  have hstable : (prefixWord ++ tailWord_7998341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998341).length < 2 ^ (prefixWord ++ tailWord_7998341).sum := by decide
  have hdescent : baseEnd_7998341 < baseStart_7998341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998348 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_7998348 : Nat := 118140960795 + 7998348 * 2 ^ 59
def prefixEnd_7998348 : Nat := 4983230072969 + 3 ^ 40 * 7998348 * 2
def baseEnd_7998348 : Nat := 4106996965927577660366273

theorem tailTrace_7998348 : CollatzResearch.WordTrace tailWord_7998348 prefixEnd_7998348 4106996965927577660366273 := by
  unfold tailWord_7998348
  simp only [CollatzResearch.WordTrace]
  refine ⟨145861858813679339964985849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194482478418239119953314465 145861858813679339964985849)
  ·
    refine ⟨109396394110259504973739387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145861858813679339964985849 109396394110259504973739387)
    ·
      refine ⟨164094591165389257460609081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109396394110259504973739387 164094591165389257460609081)
      ·
        refine ⟨123070943374041943095456811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164094591165389257460609081 123070943374041943095456811)
        ·
          refine ⟨184606415061062914643185217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123070943374041943095456811 184606415061062914643185217)
          ·
            refine ⟨138454811295797185982388913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184606415061062914643185217 138454811295797185982388913)
            ·
              refine ⟨103841108471847889486791685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138454811295797185982388913 103841108471847889486791685)
              ·
                refine ⟨19470207838471479278773441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103841108471847889486791685 19470207838471479278773441)
                ·
                  refine ⟨14602655878853609459080081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19470207838471479278773441 14602655878853609459080081)
                  ·
                    refine ⟨10951991909140207094310061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14602655878853609459080081 10951991909140207094310061)
                    ·
                      refine ⟨4106996965927577660366273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10951991909140207094310061 4106996965927577660366273)
                      ·
                        rfl

theorem cell23_7998348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_7998348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998348 prefixEnd_7998348 := by exact prefixLift 7998348
  have htrace : WordTrace (prefixWord ++ tailWord_7998348) baseStart_7998348 baseEnd_7998348 := by
    simpa [prefixWord, tailWord_7998348, baseEnd_7998348] using wordTrace_append hprefix tailTrace_7998348
  have hstable : (prefixWord ++ tailWord_7998348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998348).length < 2 ^ (prefixWord ++ tailWord_7998348).sum := by decide
  have hdescent : baseEnd_7998348 < baseStart_7998348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998469 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_7998469 : Nat := 118140960795 + 7998469 * 2 ^ 59
def prefixEnd_7998469 : Nat := 4983230072969 + 3 ^ 40 * 7998469 * 2
def baseEnd_7998469 : Nat := 4107059097086771686953217

theorem tailTrace_7998469 : CollatzResearch.WordTrace tailWord_7998469 prefixEnd_7998469 4107059097086771686953217 := by
  unfold tailWord_7998469
  simp only [CollatzResearch.WordTrace]
  refine ⟨291728130859920317595126461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194485420573280211730084307 291728130859920317595126461)
  ·
    refine ⟨109398049072470119098172423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291728130859920317595126461 109398049072470119098172423)
    ·
      refine ⟨164097073608705178647258635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109398049072470119098172423 164097073608705178647258635)
      ·
        refine ⟨246145610413057767970887953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164097073608705178647258635 246145610413057767970887953)
        ·
          refine ⟨184609207809793325978165965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246145610413057767970887953 184609207809793325978165965)
          ·
            refine ⟨69228452928672497241812237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184609207809793325978165965 69228452928672497241812237)
            ·
              refine ⟨25960669848252186465679589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69228452928672497241812237 25960669848252186465679589)
              ·
                refine ⟨4867625596547284962314923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25960669848252186465679589 4867625596547284962314923)
                ·
                  refine ⟨7301438394820927443472385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867625596547284962314923 7301438394820927443472385)
                  ·
                    refine ⟨5476078796115695582604289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7301438394820927443472385 5476078796115695582604289)
                    ·
                      refine ⟨4107059097086771686953217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476078796115695582604289 4107059097086771686953217)
                      ·
                        rfl

theorem cell23_7998469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_7998469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998469 prefixEnd_7998469 := by exact prefixLift 7998469
  have htrace : WordTrace (prefixWord ++ tailWord_7998469) baseStart_7998469 baseEnd_7998469 := by
    simpa [prefixWord, tailWord_7998469, baseEnd_7998469] using wordTrace_append hprefix tailTrace_7998469
  have hstable : (prefixWord ++ tailWord_7998469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998469).length < 2 ^ (prefixWord ++ tailWord_7998469).sum := by decide
  have hdescent : baseEnd_7998469 < baseStart_7998469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998485 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_7998485 : Nat := 118140960795 + 7998485 * 2 ^ 59
def prefixEnd_7998485 : Nat := 4983230072969 + 3 ^ 40 * 7998485 * 2
def baseEnd_7998485 : Nat := 4107067312777243624353143

theorem tailTrace_7998485 : CollatzResearch.WordTrace tailWord_7998485 prefixEnd_7998485 4107067312777243624353143 := by
  unfold tailWord_7998485
  simp only [CollatzResearch.WordTrace]
  refine ⟨291728714427862352327708909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194485809618574901551805939 291728714427862352327708909)
  ·
    refine ⟨109398267910448382122890841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291728714427862352327708909 109398267910448382122890841)
    ·
      refine ⟨82048700932836286592168131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109398267910448382122890841 82048700932836286592168131)
      ·
        refine ⟨123073051399254429888252197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82048700932836286592168131 123073051399254429888252197)
        ·
          refine ⟨23076197137360205604047287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123073051399254429888252197 23076197137360205604047287)
          ·
            refine ⟨34614295706040308406070931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076197137360205604047287 34614295706040308406070931)
            ·
              refine ⟨51921443559060462609106397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34614295706040308406070931 51921443559060462609106397)
              ·
                refine ⟨19470541334647673478414899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51921443559060462609106397 19470541334647673478414899)
                ·
                  refine ⟨29205812001971510217622349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19470541334647673478414899 29205812001971510217622349)
                  ·
                    refine ⟨10952179500739316331608381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29205812001971510217622349 10952179500739316331608381)
                    ·
                      refine ⟨4107067312777243624353143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952179500739316331608381 4107067312777243624353143)
                      ·
                        rfl

theorem cell23_7998485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_7998485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998485 prefixEnd_7998485 := by exact prefixLift 7998485
  have htrace : WordTrace (prefixWord ++ tailWord_7998485) baseStart_7998485 baseEnd_7998485 := by
    simpa [prefixWord, tailWord_7998485, baseEnd_7998485] using wordTrace_append hprefix tailTrace_7998485
  have hstable : (prefixWord ++ tailWord_7998485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998485).length < 2 ^ (prefixWord ++ tailWord_7998485).sum := by decide
  have hdescent : baseEnd_7998485 < baseStart_7998485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998503 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7998503 : Nat := 118140960795 + 7998503 * 2 ^ 59
def prefixEnd_7998503 : Nat := 4983230072969 + 3 ^ 40 * 7998503 * 2
def baseEnd_7998503 : Nat := 4107076555429024553928061

theorem tailTrace_7998503 : CollatzResearch.WordTrace tailWord_7998503 prefixEnd_7998503 4107076555429024553928061 := by
  unfold tailWord_7998503
  simp only [CollatzResearch.WordTrace]
  refine ⟨291729370941797141401864163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194486247294531427601242775 291729370941797141401864163)
  ·
    refine ⟨437594056412695712102796245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291729370941797141401864163 437594056412695712102796245)
    ·
      refine ⟨10256110697172555752409287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 437594056412695712102796245 10256110697172555752409287)
      ·
        refine ⟨15384166045758833628613931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256110697172555752409287 15384166045758833628613931)
        ·
          refine ⟨23076249068638250442920897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384166045758833628613931 23076249068638250442920897)
          ·
            refine ⟨17307186801478687832190673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23076249068638250442920897 17307186801478687832190673)
            ·
              refine ⟨12980390101109015874143005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17307186801478687832190673 12980390101109015874143005)
              ·
                refine ⟨4867646287915880952803627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12980390101109015874143005 4867646287915880952803627)
                ·
                  refine ⟨7301469431873821429205441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867646287915880952803627 7301469431873821429205441)
                  ·
                    refine ⟨5476102073905366071904081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7301469431873821429205441 5476102073905366071904081)
                    ·
                      refine ⟨4107076555429024553928061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476102073905366071904081 4107076555429024553928061)
                      ·
                        rfl

theorem cell23_7998503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7998503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998503 prefixEnd_7998503 := by exact prefixLift 7998503
  have htrace : WordTrace (prefixWord ++ tailWord_7998503) baseStart_7998503 baseEnd_7998503 := by
    simpa [prefixWord, tailWord_7998503, baseEnd_7998503] using wordTrace_append hprefix tailTrace_7998503
  have hstable : (prefixWord ++ tailWord_7998503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998503).length < 2 ^ (prefixWord ++ tailWord_7998503).sum := by decide
  have hdescent : baseEnd_7998503 < baseStart_7998503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998506 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7998506 : Nat := 118140960795 + 7998506 * 2 ^ 59
def prefixEnd_7998506 : Nat := 4983230072969 + 3 ^ 40 * 7998506 * 2
def baseEnd_7998506 : Nat := 4107078095870988042190547

theorem tailTrace_7998506 : CollatzResearch.WordTrace tailWord_7998506 prefixEnd_7998506 4107078095870988042190547 := by
  unfold tailWord_7998506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72932370090196568228555843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194486320240524181942815581 72932370090196568228555843)
  ·
    refine ⟨109398555135294852342833765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72932370090196568228555843 109398555135294852342833765)
    ·
      refine ⟨20512229087867784814281331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109398555135294852342833765 20512229087867784814281331)
      ·
        refine ⟨30768343631801677221421997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20512229087867784814281331 30768343631801677221421997)
        ·
          refine ⟨11538128861925628958033249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30768343631801677221421997 11538128861925628958033249)
          ·
            refine ⟨8653596646444221718524937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11538128861925628958033249 8653596646444221718524937)
            ·
              refine ⟨6490197484833166288893703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653596646444221718524937 6490197484833166288893703)
              ·
                refine ⟨9735296227249749433340555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490197484833166288893703 9735296227249749433340555)
                ·
                  refine ⟨14602944340874624150010833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735296227249749433340555 14602944340874624150010833)
                  ·
                    refine ⟨10952208255655968112508125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14602944340874624150010833 10952208255655968112508125)
                    ·
                      refine ⟨4107078095870988042190547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952208255655968112508125 4107078095870988042190547)
                      ·
                        rfl

theorem cell23_7998506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7998506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998506 prefixEnd_7998506 := by exact prefixLift 7998506
  have htrace : WordTrace (prefixWord ++ tailWord_7998506) baseStart_7998506 baseEnd_7998506 := by
    simpa [prefixWord, tailWord_7998506, baseEnd_7998506] using wordTrace_append hprefix tailTrace_7998506
  have hstable : (prefixWord ++ tailWord_7998506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998506).length < 2 ^ (prefixWord ++ tailWord_7998506).sum := by decide
  have hdescent : baseEnd_7998506 < baseStart_7998506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998512 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2]
def baseStart_7998512 : Nat := 118140960795 + 7998512 * 2 ^ 59
def prefixEnd_7998512 : Nat := 4983230072969 + 3 ^ 40 * 7998512 * 2
def baseEnd_7998512 : Nat := 4107081176754915018715519

theorem tailTrace_7998512 : CollatzResearch.WordTrace tailWord_7998512 prefixEnd_7998512 4107081176754915018715519 := by
  unfold tailWord_7998512
  simp only [CollatzResearch.WordTrace]
  refine ⟨145864849599382267969470895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194486466132509690625961193 145864849599382267969470895)
  ·
    refine ⟨218797274399073401954206343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145864849599382267969470895 218797274399073401954206343)
    ·
      refine ⟨328195911598610102931309515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218797274399073401954206343 328195911598610102931309515)
      ·
        refine ⟨492293867397915154396964273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328195911598610102931309515 492293867397915154396964273)
        ·
          refine ⟨369220400548436365797723205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492293867397915154396964273 369220400548436365797723205)
          ·
            refine ⟨69228825102831818587073101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369220400548436365797723205 69228825102831818587073101)
            ·
              refine ⟨25960809413561931970152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69228825102831818587073101 25960809413561931970152413)
              ·
                refine ⟨9735303530085724488807155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25960809413561931970152413 9735303530085724488807155)
                ·
                  refine ⟨14602955295128586733210733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735303530085724488807155 14602955295128586733210733)
                  ·
                    refine ⟨5476108235673220024954025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14602955295128586733210733 5476108235673220024954025)
                    ·
                      refine ⟨4107081176754915018715519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476108235673220024954025 4107081176754915018715519)
                      ·
                        rfl

theorem cell23_7998512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2].length) (baseStart_7998512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998512 prefixEnd_7998512 := by exact prefixLift 7998512
  have htrace : WordTrace (prefixWord ++ tailWord_7998512) baseStart_7998512 baseEnd_7998512 := by
    simpa [prefixWord, tailWord_7998512, baseEnd_7998512] using wordTrace_append hprefix tailTrace_7998512
  have hstable : (prefixWord ++ tailWord_7998512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998512).length < 2 ^ (prefixWord ++ tailWord_7998512).sum := by decide
  have hdescent : baseEnd_7998512 < baseStart_7998512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998562 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7998562 : Nat := 118140960795 + 7998562 * 2 ^ 59
def prefixEnd_7998562 : Nat := 4983230072969 + 3 ^ 40 * 7998562 * 2
def baseEnd_7998562 : Nat := 4107106850787639823090289

theorem tailTrace_7998562 : CollatzResearch.WordTrace tailWord_7998562 prefixEnd_7998562 4107106850787639823090289 := by
  unfold tailWord_7998562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72932880712145848619565485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194487681899055596318841293 72932880712145848619565485)
  ·
    refine ⟨27349830267054693232337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72932880712145848619565485 27349830267054693232337057)
    ·
      refine ⟨20512372700291019924252793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27349830267054693232337057 20512372700291019924252793)
      ·
        refine ⟨15384279525218264943189595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20512372700291019924252793 15384279525218264943189595)
        ·
          refine ⟨23076419287827397414784393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384279525218264943189595 23076419287827397414784393)
          ·
            refine ⟨17307314465870548061088295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23076419287827397414784393 17307314465870548061088295)
            ·
              refine ⟨25960971698805822091632443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17307314465870548061088295 25960971698805822091632443)
              ·
                refine ⟨38941457548208733137448665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25960971698805822091632443 38941457548208733137448665)
                ·
                  refine ⟨29206093161156549853086499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38941457548208733137448665 29206093161156549853086499)
                  ·
                    refine ⟨43809139741734824779629749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29206093161156549853086499 43809139741734824779629749)
                    ·
                      refine ⟨4107106850787639823090289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43809139741734824779629749 4107106850787639823090289)
                      ·
                        rfl

theorem cell23_7998562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7998562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998562 prefixEnd_7998562 := by exact prefixLift 7998562
  have htrace : WordTrace (prefixWord ++ tailWord_7998562) baseStart_7998562 baseEnd_7998562 := by
    simpa [prefixWord, tailWord_7998562, baseEnd_7998562] using wordTrace_append hprefix tailTrace_7998562
  have hstable : (prefixWord ++ tailWord_7998562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998562).length < 2 ^ (prefixWord ++ tailWord_7998562).sum := by decide
  have hdescent : baseEnd_7998562 < baseStart_7998562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998593 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7998593 : Nat := 118140960795 + 7998593 * 2 ^ 59
def prefixEnd_7998593 : Nat := 4983230072969 + 3 ^ 40 * 7998593 * 2
def baseEnd_7998593 : Nat := 4107122768687929201802647

theorem tailTrace_7998593 : CollatzResearch.WordTrace tailWord_7998593 prefixEnd_7998593 4107122768687929201802647 := by
  unfold tailWord_7998593
  simp only [CollatzResearch.WordTrace]
  refine ⟨291732653511471086772640433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194488435674314057848426955 291732653511471086772640433)
  ·
    refine ⟨218799490133603315079480325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291732653511471086772640433 218799490133603315079480325)
    ·
      refine ⟨41024904400050621577402561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218799490133603315079480325 41024904400050621577402561)
      ·
        refine ⟨30768678300037966183051921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41024904400050621577402561 30768678300037966183051921)
        ·
          refine ⟨23076508725028474637288941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30768678300037966183051921 23076508725028474637288941)
          ·
            refine ⟨8653690771885677988983353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23076508725028474637288941 8653690771885677988983353)
            ·
              refine ⟨6490268078914258491737515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653690771885677988983353 6490268078914258491737515)
              ·
                refine ⟨9735402118371387737606273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490268078914258491737515 9735402118371387737606273)
                ·
                  refine ⟨7301551588778540803204705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9735402118371387737606273 7301551588778540803204705)
                  ·
                    refine ⟨5476163691583905602403529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7301551588778540803204705 5476163691583905602403529)
                    ·
                      refine ⟨4107122768687929201802647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476163691583905602403529 4107122768687929201802647)
                      ·
                        rfl

theorem cell23_7998593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7998593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998593 prefixEnd_7998593 := by exact prefixLift 7998593
  have htrace : WordTrace (prefixWord ++ tailWord_7998593) baseStart_7998593 baseEnd_7998593 := by
    simpa [prefixWord, tailWord_7998593, baseEnd_7998593] using wordTrace_append hprefix tailTrace_7998593
  have hstable : (prefixWord ++ tailWord_7998593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998593).length < 2 ^ (prefixWord ++ tailWord_7998593).sum := by decide
  have hdescent : baseEnd_7998593 < baseStart_7998593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998622 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7998622 : Nat := 118140960795 + 7998622 * 2 ^ 59
def prefixEnd_7998622 : Nat := 4983230072969 + 3 ^ 40 * 7998622 * 2
def baseEnd_7998622 : Nat := 4107137659626909588340013

theorem tailTrace_7998622 : CollatzResearch.WordTrace tailWord_7998622 prefixEnd_7998622 4107137659626909588340013 := by
  unfold tailWord_7998622
  simp only [CollatzResearch.WordTrace]
  refine ⟨36466713903545753090680765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194489140818910683150297413 36466713903545753090680765)
  ·
    refine ⟨13675017713829657409005287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36466713903545753090680765 13675017713829657409005287)
    ·
      refine ⟨20512526570744486113507931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13675017713829657409005287 20512526570744486113507931)
      ·
        refine ⟨30768789856116729170261897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20512526570744486113507931 30768789856116729170261897)
        ·
          refine ⟨23076592392087546877696423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30768789856116729170261897 23076592392087546877696423)
          ·
            refine ⟨34614888588131320316544635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076592392087546877696423 34614888588131320316544635)
            ·
              refine ⟨51922332882196980474816953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34614888588131320316544635 51922332882196980474816953)
              ·
                refine ⟨38941749661647735356112715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51922332882196980474816953 38941749661647735356112715)
                ·
                  refine ⟨58412624492471603034169073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38941749661647735356112715 58412624492471603034169073)
                  ·
                    refine ⟨43809468369353702275626805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58412624492471603034169073 43809468369353702275626805)
                    ·
                      refine ⟨4107137659626909588340013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43809468369353702275626805 4107137659626909588340013)
                      ·
                        rfl

theorem cell23_7998622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7998622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998622 prefixEnd_7998622 := by exact prefixLift 7998622
  have htrace : WordTrace (prefixWord ++ tailWord_7998622) baseStart_7998622 baseEnd_7998622 := by
    simpa [prefixWord, tailWord_7998622, baseEnd_7998622] using wordTrace_append hprefix tailTrace_7998622
  have hstable : (prefixWord ++ tailWord_7998622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998622).length < 2 ^ (prefixWord ++ tailWord_7998622).sum := by decide
  have hdescent : baseEnd_7998622 < baseStart_7998622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998655 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 6]
def baseStart_7998655 : Nat := 118140960795 + 7998655 * 2 ^ 59
def prefixEnd_7998655 : Nat := 4983230072969 + 3 ^ 40 * 7998655 * 2
def baseEnd_7998655 : Nat := 456350511609834217691929

theorem tailTrace_7998655 : CollatzResearch.WordTrace tailWord_7998655 prefixEnd_7998655 456350511609834217691929 := by
  unfold tailWord_7998655
  simp only [CollatzResearch.WordTrace]
  refine ⟨291734914837246471361397419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194489943224830980907598279 291734914837246471361397419)
  ·
    refine ⟨437602372255869707042096129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291734914837246471361397419 437602372255869707042096129)
    ·
      refine ⟨328201779191902280281572097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437602372255869707042096129 328201779191902280281572097)
      ·
        refine ⟨246151334393926710211179073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328201779191902280281572097 246151334393926710211179073)
        ·
          refine ⟨184613500795445032658384305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246151334393926710211179073 184613500795445032658384305)
          ·
            refine ⟨138460125596583774493788229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184613500795445032658384305 138460125596583774493788229)
            ·
              refine ⟨25961273549359457717585293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138460125596583774493788229 25961273549359457717585293)
              ·
                refine ⟨9735477581009796644094485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25961273549359457717585293 9735477581009796644094485)
                ·
                  refine ⟨456350511609834217691929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9735477581009796644094485 456350511609834217691929)
                  ·
                    rfl

theorem cell23_7998655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 6].length) (baseStart_7998655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998655 prefixEnd_7998655 := by exact prefixLift 7998655
  have htrace : WordTrace (prefixWord ++ tailWord_7998655) baseStart_7998655 baseEnd_7998655 := by
    simpa [prefixWord, tailWord_7998655, baseEnd_7998655] using wordTrace_append hprefix tailTrace_7998655
  have hstable : (prefixWord ++ tailWord_7998655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998655).length < 2 ^ (prefixWord ++ tailWord_7998655).sum := by decide
  have hdescent : baseEnd_7998655 < baseStart_7998655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998682 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_7998682 : Nat := 118140960795 + 7998682 * 2 ^ 59
def prefixEnd_7998682 : Nat := 4983230072969 + 3 ^ 40 * 7998682 * 2
def baseEnd_7998682 : Nat := 4107168468466179353589737

theorem tailTrace_7998682 : CollatzResearch.WordTrace tailWord_7998682 prefixEnd_7998682 4107168468466179353589737 := by
  unfold tailWord_7998682
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933974902037163743157575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194490599738765769981753533 72933974902037163743157575)
  ·
    refine ⟨109400962353055745614736363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72933974902037163743157575 109400962353055745614736363)
    ·
      refine ⟨164101443529583618422104545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109400962353055745614736363 164101443529583618422104545)
      ·
        refine ⟨123076082647187713816578409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164101443529583618422104545 123076082647187713816578409)
        ·
          refine ⟨92307061985390785362433807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123076082647187713816578409 92307061985390785362433807)
          ·
            refine ⟨138460592978086178043650711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92307061985390785362433807 138460592978086178043650711)
            ·
              refine ⟨207690889467129267065476067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138460592978086178043650711 207690889467129267065476067)
              ·
                refine ⟨311536334200693900598214101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207690889467129267065476067 311536334200693900598214101)
                ·
                  refine ⟨7301632832828763295270643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 311536334200693900598214101 7301632832828763295270643)
                  ·
                    refine ⟨10952449249243144942905965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7301632832828763295270643 10952449249243144942905965)
                    ·
                      refine ⟨4107168468466179353589737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952449249243144942905965 4107168468466179353589737)
                      ·
                        rfl

theorem cell23_7998682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_7998682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998682 prefixEnd_7998682 := by exact prefixLift 7998682
  have htrace : WordTrace (prefixWord ++ tailWord_7998682) baseStart_7998682 baseEnd_7998682 := by
    simpa [prefixWord, tailWord_7998682, baseEnd_7998682] using wordTrace_append hprefix tailTrace_7998682
  have hstable : (prefixWord ++ tailWord_7998682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998682).length < 2 ^ (prefixWord ++ tailWord_7998682).sum := by decide
  have hdescent : baseEnd_7998682 < baseStart_7998682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998699 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 3]
def baseStart_7998699 : Nat := 118140960795 + 7998699 * 2 ^ 59
def prefixEnd_7998699 : Nat := 4983230072969 + 3 ^ 40 * 7998699 * 2
def baseEnd_7998699 : Nat := 4107177197637305787077159

theorem tailTrace_7998699 : CollatzResearch.WordTrace tailWord_7998699 prefixEnd_7998699 4107177197637305787077159 := by
  unfold tailWord_7998699
  simp only [CollatzResearch.WordTrace]
  refine ⟨291736519649087066875999151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194491013099391377917332767 291736519649087066875999151)
  ·
    refine ⟨437604779473630600313998727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291736519649087066875999151 437604779473630600313998727)
    ·
      refine ⟨656407169210445900470998091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437604779473630600313998727 656407169210445900470998091)
      ·
        refine ⟨984610753815668850706497137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656407169210445900470998091 984610753815668850706497137)
        ·
          refine ⟨738458065361751638029872853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984610753815668850706497137 738458065361751638029872853)
          ·
            refine ⟨17307610906916054016325145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 738458065361751638029872853 17307610906916054016325145)
            ·
              refine ⟨12980708180187040512243859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17307610906916054016325145 12980708180187040512243859)
              ·
                refine ⟨19471062270280560768365789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12980708180187040512243859 19471062270280560768365789)
                ·
                  refine ⟨7301648351355210288137171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19471062270280560768365789 7301648351355210288137171)
                  ·
                    refine ⟨10952472527032815432205757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7301648351355210288137171 10952472527032815432205757)
                    ·
                      refine ⟨4107177197637305787077159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952472527032815432205757 4107177197637305787077159)
                      ·
                        rfl

theorem cell23_7998699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 3].length) (baseStart_7998699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998699 prefixEnd_7998699 := by exact prefixLift 7998699
  have htrace : WordTrace (prefixWord ++ tailWord_7998699) baseStart_7998699 baseEnd_7998699 := by
    simpa [prefixWord, tailWord_7998699, baseEnd_7998699] using wordTrace_append hprefix tailTrace_7998699
  have hstable : (prefixWord ++ tailWord_7998699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998699).length < 2 ^ (prefixWord ++ tailWord_7998699).sum := by decide
  have hdescent : baseEnd_7998699 < baseStart_7998699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998725 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_7998725 : Nat := 118140960795 + 7998725 * 2 ^ 59
def prefixEnd_7998725 : Nat := 4983230072969 + 3 ^ 40 * 7998725 * 2
def baseEnd_7998725 : Nat := 4107190548134322685352039

theorem tailTrace_7998725 : CollatzResearch.WordTrace tailWord_7998725 prefixEnd_7998725 4107190548134322685352039 := by
  unfold tailWord_7998725
  simp only [CollatzResearch.WordTrace]
  refine ⟨291737467946992873316445629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194491645297995248877630419 291737467946992873316445629)
  ·
    refine ⟨109401550480122327493667111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291737467946992873316445629 109401550480122327493667111)
    ·
      refine ⟨164102325720183491240500667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109401550480122327493667111 164102325720183491240500667)
      ·
        refine ⟨246153488580275236860751001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164102325720183491240500667 246153488580275236860751001)
        ·
          refine ⟨184615116435206427645563251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246153488580275236860751001 184615116435206427645563251)
          ·
            refine ⟨276922674652809641468344877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184615116435206427645563251 276922674652809641468344877)
            ·
              refine ⟨103846002994803615550629329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276922674652809641468344877 103846002994803615550629329)
              ·
                refine ⟨77884502246102711662971997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103846002994803615550629329 77884502246102711662971997)
                ·
                  refine ⟨29206688342288516873614499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77884502246102711662971997 29206688342288516873614499)
                  ·
                    refine ⟨43810032513432775310421749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29206688342288516873614499 43810032513432775310421749)
                    ·
                      refine ⟨4107190548134322685352039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43810032513432775310421749 4107190548134322685352039)
                      ·
                        rfl

theorem cell23_7998725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_7998725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998725 prefixEnd_7998725 := by exact prefixLift 7998725
  have htrace : WordTrace (prefixWord ++ tailWord_7998725) baseStart_7998725 baseEnd_7998725 := by
    simpa [prefixWord, tailWord_7998725, baseEnd_7998725] using wordTrace_append hprefix tailTrace_7998725
  have hstable : (prefixWord ++ tailWord_7998725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998725).length < 2 ^ (prefixWord ++ tailWord_7998725).sum := by decide
  have hdescent : baseEnd_7998725 < baseStart_7998725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998732 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_7998732 : Nat := 118140960795 + 7998732 * 2 ^ 59
def prefixEnd_7998732 : Nat := 4983230072969 + 3 ^ 40 * 7998732 * 2
def baseEnd_7998732 : Nat := 1369064714166301385988169

theorem tailTrace_7998732 : CollatzResearch.WordTrace tailWord_7998732 prefixEnd_7998732 1369064714166301385988169 := by
  unfold tailWord_7998732
  simp only [CollatzResearch.WordTrace]
  refine ⟨145868861628983756755975225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194491815505311675674633633 145868861628983756755975225)
  ·
    refine ⟨109401646221737817566981419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145868861628983756755975225 109401646221737817566981419)
    ·
      refine ⟨164102469332606726350472129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109401646221737817566981419 164102469332606726350472129)
      ·
        refine ⟨123076851999455044762854097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164102469332606726350472129 123076851999455044762854097)
        ·
          refine ⟨92307638999591283572140573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123076851999455044762854097 92307638999591283572140573)
          ·
            refine ⟨34615364624846731339552715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92307638999591283572140573 34615364624846731339552715)
            ·
              refine ⟨51923046937270097009329073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34615364624846731339552715 51923046937270097009329073)
              ·
                refine ⟨38942285202952572756996805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51923046937270097009329073 38942285202952572756996805)
                ·
                  refine ⟨7301678475553607391936901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38942285202952572756996805 7301678475553607391936901)
                  ·
                    refine ⟨1369064714166301385988169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301678475553607391936901 1369064714166301385988169)
                    ·
                      rfl

theorem cell23_7998732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_7998732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998732 prefixEnd_7998732 := by exact prefixLift 7998732
  have htrace : WordTrace (prefixWord ++ tailWord_7998732) baseStart_7998732 baseEnd_7998732 := by
    simpa [prefixWord, tailWord_7998732, baseEnd_7998732] using wordTrace_append hprefix tailTrace_7998732
  have hstable : (prefixWord ++ tailWord_7998732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998732).length < 2 ^ (prefixWord ++ tailWord_7998732).sum := by decide
  have hdescent : baseEnd_7998732 < baseStart_7998732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998749 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7998749 : Nat := 118140960795 + 7998749 * 2 ^ 59
def prefixEnd_7998749 : Nat := 4983230072969 + 3 ^ 40 * 7998749 * 2
def baseEnd_7998749 : Nat := 1369067623890010197150643

theorem tailTrace_7998749 : CollatzResearch.WordTrace tailWord_7998749 prefixEnd_7998749 1369067623890010197150643 := by
  unfold tailWord_7998749
  simp only [CollatzResearch.WordTrace]
  refine ⟨291738343298905925415319301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194492228865937283610212867 291738343298905925415319301)
  ·
    refine ⟨54700939368544861015372369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291738343298905925415319301 54700939368544861015372369)
    ·
      refine ⟨41025704526408645761529277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54700939368544861015372369 41025704526408645761529277)
      ·
        refine ⟨15384639197403242160573479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41025704526408645761529277 15384639197403242160573479)
        ·
          refine ⟨23076958796104863240860219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384639197403242160573479 23076958796104863240860219)
          ·
            refine ⟨34615438194157294861290329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076958796104863240860219 34615438194157294861290329)
            ·
              refine ⟨25961578645617971145967747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34615438194157294861290329 25961578645617971145967747)
              ·
                refine ⟨38942367968426956718951621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25961578645617971145967747 38942367968426956718951621)
                ·
                  refine ⟨7301693994080054384803429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38942367968426956718951621 7301693994080054384803429)
                  ·
                    refine ⟨1369067623890010197150643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301693994080054384803429 1369067623890010197150643)
                    ·
                      rfl

theorem cell23_7998749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7998749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998749 prefixEnd_7998749 := by exact prefixLift 7998749
  have htrace : WordTrace (prefixWord ++ tailWord_7998749) baseStart_7998749 baseEnd_7998749 := by
    simpa [prefixWord, tailWord_7998749, baseEnd_7998749] using wordTrace_append hprefix tailTrace_7998749
  have hstable : (prefixWord ++ tailWord_7998749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998749).length < 2 ^ (prefixWord ++ tailWord_7998749).sum := by decide
  have hdescent : baseEnd_7998749 < baseStart_7998749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998750 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7998750 : Nat := 118140960795 + 7998750 * 2 ^ 59
def prefixEnd_7998750 : Nat := 4983230072969 + 3 ^ 40 * 7998750 * 2
def baseEnd_7998750 : Nat := 4107203385150685087539425

theorem tailTrace_7998750 : CollatzResearch.WordTrace tailWord_7998750 prefixEnd_7998750 4107203385150685087539425 := by
  unfold tailWord_7998750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36467297471487787823263213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194492253181268201724070469 36467297471487787823263213)
  ·
    refine ⟨13675236551807920433723705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36467297471487787823263213 13675236551807920433723705)
    ·
      refine ⟨10256427413855940325292779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675236551807920433723705 10256427413855940325292779)
      ·
        refine ⟨15384641120783910487939169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256427413855940325292779 15384641120783910487939169)
        ·
          refine ⟨11538480840587932865954377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15384641120783910487939169 11538480840587932865954377)
          ·
            refine ⟨8653860630440949649465783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11538480840587932865954377 8653860630440949649465783)
            ·
              refine ⟨12980790945661424474198675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653860630440949649465783 12980790945661424474198675)
              ·
                refine ⟨19471186418492136711298013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12980790945661424474198675 19471186418492136711298013)
                ·
                  refine ⟨7301694906934551266736755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19471186418492136711298013 7301694906934551266736755)
                  ·
                    refine ⟨10952542360401826900105133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7301694906934551266736755 10952542360401826900105133)
                    ·
                      refine ⟨4107203385150685087539425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952542360401826900105133 4107203385150685087539425)
                      ·
                        rfl

theorem cell23_7998750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7998750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998750 prefixEnd_7998750 := by exact prefixLift 7998750
  have htrace : WordTrace (prefixWord ++ tailWord_7998750) baseStart_7998750 baseEnd_7998750 := by
    simpa [prefixWord, tailWord_7998750, baseEnd_7998750] using wordTrace_append hprefix tailTrace_7998750
  have hstable : (prefixWord ++ tailWord_7998750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998750).length < 2 ^ (prefixWord ++ tailWord_7998750).sum := by decide
  have hdescent : baseEnd_7998750 < baseStart_7998750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998762 : List Nat := [3, 1, 4, 2, 1, 1, 1, 10]
def baseStart_7998762 : Nat := 118140960795 + 7998762 * 2 ^ 59
def prefixEnd_7998762 : Nat := 4983230072969 + 3 ^ 40 * 7998762 * 2
def baseEnd_7998762 : Nat := 152118872108094038540347

theorem tailTrace_7998762 : CollatzResearch.WordTrace tailWord_7998762 prefixEnd_7998762 152118872108094038540347 := by
  unfold tailWord_7998762
  simp only [CollatzResearch.WordTrace]
  refine ⟨72934704361964707158885635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194492544965239219090361693 72934704361964707158885635)
  ·
    refine ⟨109402056542947060738328453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72934704361964707158885635 109402056542947060738328453)
    ·
      refine ⟨20512885601802573888436585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109402056542947060738328453 20512885601802573888436585)
      ·
        refine ⟨15384664201351930416327439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20512885601802573888436585 15384664201351930416327439)
        ·
          refine ⟨23076996302027895624491159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384664201351930416327439 23076996302027895624491159)
          ·
            refine ⟨34615494453041843436736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076996302027895624491159 34615494453041843436736739)
            ·
              refine ⟨51923241679562765155105109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34615494453041843436736739 51923241679562765155105109)
              ·
                refine ⟨152118872108094038540347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51923241679562765155105109 152118872108094038540347)
                ·
                  rfl

theorem cell23_7998762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_7998762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998762 prefixEnd_7998762 := by exact prefixLift 7998762
  have htrace : WordTrace (prefixWord ++ tailWord_7998762) baseStart_7998762 baseEnd_7998762 := by
    simpa [prefixWord, tailWord_7998762, baseEnd_7998762] using wordTrace_append hprefix tailTrace_7998762
  have hstable : (prefixWord ++ tailWord_7998762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998762).length < 2 ^ (prefixWord ++ tailWord_7998762).sum := by decide
  have hdescent : baseEnd_7998762 < baseStart_7998762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998813 : List Nat := [1, 4, 5, 1, 1, 2, 1, 8]
def baseStart_7998813 : Nat := 118140960795 + 7998813 * 2 ^ 59
def prefixEnd_7998813 : Nat := 4983230072969 + 3 ^ 40 * 7998813 * 2
def baseEnd_7998813 : Nat := 152119842015996975594505

theorem tailTrace_7998813 : CollatzResearch.WordTrace tailWord_7998813 prefixEnd_7998813 152119842015996975594505 := by
  unfold tailWord_7998813
  simp only [CollatzResearch.WordTrace]
  refine ⟨291740677570674064345649093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194493785047116042897099395 291740677570674064345649093)
  ·
    refine ⟨54701377044501387064809205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291740677570674064345649093 54701377044501387064809205)
    ·
      refine ⟨5128254097922005037325863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54701377044501387064809205 5128254097922005037325863)
      ·
        refine ⟨7692381146883007555988795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128254097922005037325863 7692381146883007555988795)
        ·
          refine ⟨11538571720324511333983193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692381146883007555988795 11538571720324511333983193)
          ·
            refine ⟨8653928790243383500487395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11538571720324511333983193 8653928790243383500487395)
            ·
              refine ⟨12980893185365075250731093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653928790243383500487395 12980893185365075250731093)
              ·
                refine ⟨152119842015996975594505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12980893185365075250731093 152119842015996975594505)
                ·
                  rfl

theorem cell23_7998813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 8].length) (baseStart_7998813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998813 prefixEnd_7998813 := by exact prefixLift 7998813
  have htrace : WordTrace (prefixWord ++ tailWord_7998813) baseStart_7998813 baseEnd_7998813 := by
    simpa [prefixWord, tailWord_7998813, baseEnd_7998813] using wordTrace_append hprefix tailTrace_7998813
  have hstable : (prefixWord ++ tailWord_7998813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998813).length < 2 ^ (prefixWord ++ tailWord_7998813).sum := by decide
  have hdescent : baseEnd_7998813 < baseStart_7998813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998832 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_7998832 : Nat := 118140960795 + 7998832 * 2 ^ 59
def prefixEnd_7998832 : Nat := 4983230072969 + 3 ^ 40 * 7998832 * 2
def baseEnd_7998832 : Nat := 4107245490564353766714047

theorem tailTrace_7998832 : CollatzResearch.WordTrace tailWord_7998832 prefixEnd_7998832 4107245490564353766714047 := by
  unfold tailWord_7998832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145870685278802615295295375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194494247038403487060393833 145870685278802615295295375)
  ·
    refine ⟨218806027918203922942943063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145870685278802615295295375 218806027918203922942943063)
    ·
      refine ⟨328209041877305884414414595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218806027918203922942943063 328209041877305884414414595)
      ·
        refine ⟨492313562815958826621621893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328209041877305884414414595 492313562815958826621621893)
        ·
          refine ⟨92308793027992279991554105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492313562815958826621621893 92308793027992279991554105)
          ·
            refine ⟨69231594770994209993665579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92308793027992279991554105 69231594770994209993665579)
            ·
              refine ⟨103847392156491314990498369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69231594770994209993665579 103847392156491314990498369)
              ·
                refine ⟨77885544117368486242873777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103847392156491314990498369 77885544117368486242873777)
                ·
                  refine ⟨58414158088026364682155333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77885544117368486242873777 58414158088026364682155333)
                  ·
                    refine ⟨10952654641504943377904125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58414158088026364682155333 10952654641504943377904125)
                    ·
                      refine ⟨4107245490564353766714047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952654641504943377904125 4107245490564353766714047)
                      ·
                        rfl

theorem cell23_7998832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_7998832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998832 prefixEnd_7998832 := by exact prefixLift 7998832
  have htrace : WordTrace (prefixWord ++ tailWord_7998832) baseStart_7998832 baseEnd_7998832 := by
    simpa [prefixWord, tailWord_7998832, baseEnd_7998832] using wordTrace_append hprefix tailTrace_7998832
  have hstable : (prefixWord ++ tailWord_7998832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998832).length < 2 ^ (prefixWord ++ tailWord_7998832).sum := by decide
  have hdescent : baseEnd_7998832 < baseStart_7998832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998850 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7998850 : Nat := 118140960795 + 7998850 * 2 ^ 59
def prefixEnd_7998850 : Nat := 4983230072969 + 3 ^ 40 * 7998850 * 2
def baseEnd_7998850 : Nat := 4107254733216134696288965

theorem tailTrace_7998850 : CollatzResearch.WordTrace tailWord_7998850 prefixEnd_7998850 4107254733216134696288965 := by
  unfold tailWord_7998850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72935506767885004916186501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194494684714360013109830669 72935506767885004916186501)
  ·
    refine ⟨13675407518978438421784969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72935506767885004916186501 13675407518978438421784969)
    ·
      refine ⟨10256555639233828816338727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675407518978438421784969 10256555639233828816338727)
      ·
        refine ⟨15384833458850743224508091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256555639233828816338727 15384833458850743224508091)
        ·
          refine ⟨23077250188276114836762137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384833458850743224508091 23077250188276114836762137)
          ·
            refine ⟨17307937641207086127571603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23077250188276114836762137 17307937641207086127571603)
            ·
              refine ⟨25961906461810629191357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17307937641207086127571603 25961906461810629191357405)
              ·
                refine ⟨9735714923178985946759027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25961906461810629191357405 9735714923178985946759027)
                ·
                  refine ⟨14603572384768478920138541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735714923178985946759027 14603572384768478920138541)
                  ·
                    refine ⟨5476339644288179595051953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14603572384768478920138541 5476339644288179595051953)
                    ·
                      refine ⟨4107254733216134696288965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476339644288179595051953 4107254733216134696288965)
                      ·
                        rfl

theorem cell23_7998850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7998850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998850 prefixEnd_7998850 := by exact prefixLift 7998850
  have htrace : WordTrace (prefixWord ++ tailWord_7998850) baseStart_7998850 baseEnd_7998850 := by
    simpa [prefixWord, tailWord_7998850, baseEnd_7998850] using wordTrace_append hprefix tailTrace_7998850
  have hstable : (prefixWord ++ tailWord_7998850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998850).length < 2 ^ (prefixWord ++ tailWord_7998850).sum := by decide
  have hdescent : baseEnd_7998850 < baseStart_7998850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998869 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 5]
def baseStart_7998869 : Nat := 118140960795 + 7998869 * 2 ^ 59
def prefixEnd_7998869 : Nat := 4983230072969 + 3 ^ 40 * 7998869 * 2
def baseEnd_7998869 : Nat := 456362721038730013550153

theorem tailTrace_7998869 : CollatzResearch.WordTrace tailWord_7998869 prefixEnd_7998869 456362721038730013550153 := by
  unfold tailWord_7998869
  simp only [CollatzResearch.WordTrace]
  refine ⟨291742720058471185909687661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194495146705647457273125107 291742720058471185909687661)
  ·
    refine ⟨109403520021926694716132873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291742720058471185909687661 109403520021926694716132873)
    ·
      refine ⟨82052640016445021037099655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109403520021926694716132873 82052640016445021037099655)
      ·
        refine ⟨123078960024667531555649483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82052640016445021037099655 123078960024667531555649483)
        ·
          refine ⟨184618440037001297333474225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123078960024667531555649483 184618440037001297333474225)
          ·
            refine ⟨138463830027750973000105669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184618440037001297333474225 138463830027750973000105669)
            ·
              refine ⟨25961968130203307437519813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138463830027750973000105669 25961968130203307437519813)
              ·
                refine ⟨4867869024413120144534965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25961968130203307437519813 4867869024413120144534965)
                ·
                  refine ⟨456362721038730013550153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867869024413120144534965 456362721038730013550153)
                  ·
                    rfl

theorem cell23_7998869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_7998869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998869 prefixEnd_7998869 := by exact prefixLift 7998869
  have htrace : WordTrace (prefixWord ++ tailWord_7998869) baseStart_7998869 baseEnd_7998869 := by
    simpa [prefixWord, tailWord_7998869, baseEnd_7998869] using wordTrace_append hprefix tailTrace_7998869
  have hstable : (prefixWord ++ tailWord_7998869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998869).length < 2 ^ (prefixWord ++ tailWord_7998869).sum := by decide
  have hdescent : baseEnd_7998869 < baseStart_7998869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998879 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_7998879 : Nat := 118140960795 + 7998879 * 2 ^ 59
def prefixEnd_7998879 : Nat := 4983230072969 + 3 ^ 40 * 7998879 * 2
def baseEnd_7998879 : Nat := 4107269624155115082826331

theorem tailTrace_7998879 : CollatzResearch.WordTrace tailWord_7998879 prefixEnd_7998879 4107269624155115082826331 := by
  unfold tailWord_7998879
  simp only [CollatzResearch.WordTrace]
  refine ⟨291743084788434957617551691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194495389858956638411701127 291743084788434957617551691)
  ·
    refine ⟨437614627182652436426327537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291743084788434957617551691 437614627182652436426327537)
    ·
      refine ⟨328210970386989327319745653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437614627182652436426327537 328210970386989327319745653)
      ·
        refine ⟨30769778473780249436226155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328210970386989327319745653 30769778473780249436226155)
        ·
          refine ⟨46154667710670374154339233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30769778473780249436226155 46154667710670374154339233)
          ·
            refine ⟨34616000783002780615754425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46154667710670374154339233 34616000783002780615754425)
            ·
              refine ⟨25962000587252085461815819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34616000783002780615754425 25962000587252085461815819)
              ·
                refine ⟨38943000880878128192723729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25962000587252085461815819 38943000880878128192723729)
                ·
                  refine ⟨29207250660658596144542797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38943000880878128192723729 29207250660658596144542797)
                  ·
                    refine ⟨10952718997746973554203549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29207250660658596144542797 10952718997746973554203549)
                    ·
                      refine ⟨4107269624155115082826331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952718997746973554203549 4107269624155115082826331)
                      ·
                        rfl

theorem cell23_7998879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_7998879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998879 prefixEnd_7998879 := by exact prefixLift 7998879
  have htrace : WordTrace (prefixWord ++ tailWord_7998879) baseStart_7998879 baseEnd_7998879 := by
    simpa [prefixWord, tailWord_7998879, baseEnd_7998879] using wordTrace_append hprefix tailTrace_7998879
  have hstable : (prefixWord ++ tailWord_7998879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998879).length < 2 ^ (prefixWord ++ tailWord_7998879).sum := by decide
  have hdescent : baseEnd_7998879 < baseStart_7998879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998916 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7998916 : Nat := 118140960795 + 7998916 * 2 ^ 59
def prefixEnd_7998916 : Nat := 4983230072969 + 3 ^ 40 * 7998916 * 2
def baseEnd_7998916 : Nat := 1369096207646443812687887

theorem tailTrace_7998916 : CollatzResearch.WordTrace tailWord_7998916 prefixEnd_7998916 1369096207646443812687887 := by
  unfold tailWord_7998916
  simp only [CollatzResearch.WordTrace]
  refine ⟨145872217144650456468324301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194496289526200608624432401 145872217144650456468324301)
  ·
    refine ⟨54702081429243921175621613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145872217144650456468324301 54702081429243921175621613)
    ·
      refine ⟨20513280535966470440858105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54702081429243921175621613 20513280535966470440858105)
      ·
        refine ⟨15384960401974852830643579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20513280535966470440858105 15384960401974852830643579)
        ·
          refine ⟨23077440602962279245965369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384960401974852830643579 23077440602962279245965369)
          ·
            refine ⟨17308080452221709434474027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23077440602962279245965369 17308080452221709434474027)
            ·
              refine ⟨25962120678332564151711041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17308080452221709434474027 25962120678332564151711041)
              ·
                refine ⟨19471590508749423113783281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25962120678332564151711041 19471590508749423113783281)
                ·
                  refine ⟨14603692881562067335337461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19471590508749423113783281 14603692881562067335337461)
                  ·
                    refine ⟨1369096207646443812687887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14603692881562067335337461 1369096207646443812687887)
                    ·
                      rfl

theorem cell23_7998916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7998916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998916 prefixEnd_7998916 := by exact prefixLift 7998916
  have htrace : WordTrace (prefixWord ++ tailWord_7998916) baseStart_7998916 baseEnd_7998916 := by
    simpa [prefixWord, tailWord_7998916, baseEnd_7998916] using wordTrace_append hprefix tailTrace_7998916
  have hstable : (prefixWord ++ tailWord_7998916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998916).length < 2 ^ (prefixWord ++ tailWord_7998916).sum := by decide
  have hdescent : baseEnd_7998916 < baseStart_7998916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998919 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_7998919 : Nat := 118140960795 + 7998919 * 2 ^ 59
def prefixEnd_7998919 : Nat := 4983230072969 + 3 ^ 40 * 7998919 * 2
def baseEnd_7998919 : Nat := 4107290163381294926326147

theorem tailTrace_7998919 : CollatzResearch.WordTrace tailWord_7998919 prefixEnd_7998919 4107290163381294926326147 := by
  unfold tailWord_7998919
  simp only [CollatzResearch.WordTrace]
  refine ⟨291744543708290044449007811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194496362472193362966005207 291744543708290044449007811)
  ·
    refine ⟨437616815562435066673511717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291744543708290044449007811 437616815562435066673511717)
    ·
      refine ⟨82053152917956575001283447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437616815562435066673511717 82053152917956575001283447)
      ·
        refine ⟨123079729376934862501925171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82053152917956575001283447 123079729376934862501925171)
        ·
          refine ⟨184619594065402293752887757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123079729376934862501925171 184619594065402293752887757)
          ·
            refine ⟨69232347774525860157332909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184619594065402293752887757 69232347774525860157332909)
            ·
              refine ⟨25962130415447197558999841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69232347774525860157332909 25962130415447197558999841)
              ·
                refine ⟨19471597811585398169249881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25962130415447197558999841 19471597811585398169249881)
                ·
                  refine ⟨14603698358689048626937411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19471597811585398169249881 14603698358689048626937411)
                  ·
                    refine ⟨21905547538033572940406117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14603698358689048626937411 21905547538033572940406117)
                    ·
                      refine ⟨4107290163381294926326147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21905547538033572940406117 4107290163381294926326147)
                      ·
                        rfl

theorem cell23_7998919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_7998919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998919 prefixEnd_7998919 := by exact prefixLift 7998919
  have htrace : WordTrace (prefixWord ++ tailWord_7998919) baseStart_7998919 baseEnd_7998919 := by
    simpa [prefixWord, tailWord_7998919, baseEnd_7998919] using wordTrace_append hprefix tailTrace_7998919
  have hstable : (prefixWord ++ tailWord_7998919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998919).length < 2 ^ (prefixWord ++ tailWord_7998919).sum := by decide
  have hdescent : baseEnd_7998919 < baseStart_7998919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998980 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7998980 : Nat := 118140960795 + 7998980 * 2 ^ 59
def prefixEnd_7998980 : Nat := 4983230072969 + 3 ^ 40 * 7998980 * 2
def baseEnd_7998980 : Nat := 1369107161900406395887789

theorem tailTrace_7998980 : CollatzResearch.WordTrace tailWord_7998980 prefixEnd_7998980 1369107161900406395887789 := by
  unfold tailWord_7998980
  simp only [CollatzResearch.WordTrace]
  refine ⟨145873384280534525933489197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194497845707379367911318929 145873384280534525933489197)
  ·
    refine ⟨54702519105200447225058449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145873384280534525933489197 54702519105200447225058449)
    ·
      refine ⟨41026889328900335418793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54702519105200447225058449 41026889328900335418793837)
      ·
        refine ⟨15385083498337625782047689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41026889328900335418793837 15385083498337625782047689)
        ·
          refine ⟨11538812623753219336535767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15385083498337625782047689 11538812623753219336535767)
          ·
            refine ⟨17308218935629829004803651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11538812623753219336535767 17308218935629829004803651)
            ·
              refine ⟨25962328403444743507205477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17308218935629829004803651 25962328403444743507205477)
              ·
                refine ⟨4867936575645889407601027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25962328403444743507205477 4867936575645889407601027)
                ·
                  refine ⟨7301904863468834111401541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867936575645889407601027 7301904863468834111401541)
                  ·
                    refine ⟨1369107161900406395887789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7301904863468834111401541 1369107161900406395887789)
                    ·
                      rfl

theorem cell23_7998980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7998980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7998980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7998980 prefixEnd_7998980 := by exact prefixLift 7998980
  have htrace : WordTrace (prefixWord ++ tailWord_7998980) baseStart_7998980 baseEnd_7998980 := by
    simpa [prefixWord, tailWord_7998980, baseEnd_7998980] using wordTrace_append hprefix tailTrace_7998980
  have hstable : (prefixWord ++ tailWord_7998980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998980).length < 2 ^ (prefixWord ++ tailWord_7998980).sum := by decide
  have hdescent : baseEnd_7998980 < baseStart_7998980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999059 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3]
def baseStart_7999059 : Nat := 118140960795 + 7999059 * 2 ^ 59
def prefixEnd_7999059 : Nat := 4983230072969 + 3 ^ 40 * 7999059 * 2
def baseEnd_7999059 : Nat := 4107362050672924378575503

theorem tailTrace_7999059 : CollatzResearch.WordTrace tailWord_7999059 prefixEnd_7999059 4107362050672924378575503 := by
  unfold tailWord_7999059
  simp only [CollatzResearch.WordTrace]
  refine ⟨291749649927782848359104231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194499766618521898906069487 291749649927782848359104231)
  ·
    refine ⟨437624474891674272538656347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291749649927782848359104231 437624474891674272538656347)
    ·
      refine ⟨656436712337511408807984521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437624474891674272538656347 656436712337511408807984521)
      ·
        refine ⟨492327534253133556605988391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656436712337511408807984521 492327534253133556605988391)
        ·
          refine ⟨738491301379700334908982587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492327534253133556605988391 738491301379700334908982587)
          ·
            refine ⟨1107736952069550502363473881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738491301379700334908982587 1107736952069550502363473881)
            ·
              refine ⟨830802714052162876772605411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107736952069550502363473881 830802714052162876772605411)
              ·
                refine ⟨1246204071078244315158908117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830802714052162876772605411 1246204071078244315158908117)
                ·
                  refine ⟨29207907915896351136536909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1246204071078244315158908117 29207907915896351136536909)
                  ·
                    refine ⟨10952965468461131676201341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29207907915896351136536909 10952965468461131676201341)
                    ·
                      refine ⟨4107362050672924378575503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952965468461131676201341 4107362050672924378575503)
                      ·
                        rfl

theorem cell23_7999059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_7999059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999059 prefixEnd_7999059 := by exact prefixLift 7999059
  have htrace : WordTrace (prefixWord ++ tailWord_7999059) baseStart_7999059 baseEnd_7999059 := by
    simpa [prefixWord, tailWord_7999059, baseEnd_7999059] using wordTrace_append hprefix tailTrace_7999059
  have hstable : (prefixWord ++ tailWord_7999059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999059).length < 2 ^ (prefixWord ++ tailWord_7999059).sum := by decide
  have hdescent : baseEnd_7999059 < baseStart_7999059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999063 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_7999063 : Nat := 118140960795 + 7999063 * 2 ^ 59
def prefixEnd_7999063 : Nat := 4983230072969 + 3 ^ 40 * 7999063 * 2
def baseEnd_7999063 : Nat := 4107364104595542362925485

theorem tailTrace_7999063 : CollatzResearch.WordTrace tailWord_7999063 prefixEnd_7999063 4107364104595542362925485 := by
  unfold tailWord_7999063
  simp only [CollatzResearch.WordTrace]
  refine ⟨291749795819768357042249843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194499863879845571361499895 291749795819768357042249843)
  ·
    refine ⟨437624693729652535563374765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291749795819768357042249843 437624693729652535563374765)
    ·
      refine ⟨164109260148619700836265537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437624693729652535563374765 164109260148619700836265537)
      ·
        refine ⟨123081945111464775627199153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164109260148619700836265537 123081945111464775627199153)
        ·
          refine ⟨92311458833598581720399365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123081945111464775627199153 92311458833598581720399365)
          ·
            refine ⟨17308398531299734072574881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92311458833598581720399365 17308398531299734072574881)
            ·
              refine ⟨12981298898474800554431161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17308398531299734072574881 12981298898474800554431161)
              ·
                refine ⟨9735974173856100415823371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12981298898474800554431161 9735974173856100415823371)
                ·
                  refine ⟨14603961260784150623735057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735974173856100415823371 14603961260784150623735057)
                  ·
                    refine ⟨10952970945588112967801293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14603961260784150623735057 10952970945588112967801293)
                    ·
                      refine ⟨4107364104595542362925485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10952970945588112967801293 4107364104595542362925485)
                      ·
                        rfl

theorem cell23_7999063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_7999063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999063 prefixEnd_7999063 := by exact prefixLift 7999063
  have htrace : WordTrace (prefixWord ++ tailWord_7999063) baseStart_7999063 baseEnd_7999063 := by
    simpa [prefixWord, tailWord_7999063, baseEnd_7999063] using wordTrace_append hprefix tailTrace_7999063
  have hstable : (prefixWord ++ tailWord_7999063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999063).length < 2 ^ (prefixWord ++ tailWord_7999063).sum := by decide
  have hdescent : baseEnd_7999063 < baseStart_7999063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999077 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_7999077 : Nat := 118140960795 + 7999077 * 2 ^ 59
def prefixEnd_7999077 : Nat := 4983230072969 + 3 ^ 40 * 7999077 * 2
def baseEnd_7999077 : Nat := 4107371293324705308150421

theorem tailTrace_7999077 : CollatzResearch.WordTrace tailWord_7999077 prefixEnd_7999077 4107371293324705308150421 := by
  unfold tailWord_7999077
  simp only [CollatzResearch.WordTrace]
  refine ⟨291750306441717637433259485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194500204294478424955506323 291750306441717637433259485)
  ·
    refine ⟨109406364915644114037472307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291750306441717637433259485 109406364915644114037472307)
    ·
      refine ⟨164109547373466171056208461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109406364915644114037472307 164109547373466171056208461)
      ·
        refine ⟨61541080265049814146078173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164109547373466171056208461 61541080265049814146078173)
        ·
          refine ⟨23077905099393680304779315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61541080265049814146078173 23077905099393680304779315)
          ·
            refine ⟨34616857649090520457168973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23077905099393680304779315 34616857649090520457168973)
            ·
              refine ⟨12981321618408945171438365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34616857649090520457168973 12981321618408945171438365)
              ·
                refine ⟨4867995606903354439289387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12981321618408945171438365 4867995606903354439289387)
                ·
                  refine ⟨7301993410355031658934081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867995606903354439289387 7301993410355031658934081)
                  ·
                    refine ⟨5476495057766273744200561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7301993410355031658934081 5476495057766273744200561)
                    ·
                      refine ⟨4107371293324705308150421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476495057766273744200561 4107371293324705308150421)
                      ·
                        rfl

theorem cell23_7999077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_7999077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999077 prefixEnd_7999077 := by exact prefixLift 7999077
  have htrace : WordTrace (prefixWord ++ tailWord_7999077) baseStart_7999077 baseEnd_7999077 := by
    simpa [prefixWord, tailWord_7999077, baseEnd_7999077] using wordTrace_append hprefix tailTrace_7999077
  have hstable : (prefixWord ++ tailWord_7999077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999077).length < 2 ^ (prefixWord ++ tailWord_7999077).sum := by decide
  have hdescent : baseEnd_7999077 < baseStart_7999077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999099 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_7999099 : Nat := 118140960795 + 7999099 * 2 ^ 59
def prefixEnd_7999099 : Nat := 4983230072969 + 3 ^ 40 * 7999099 * 2
def baseEnd_7999099 : Nat := 4107382589899104222075319

theorem tailTrace_7999099 : CollatzResearch.WordTrace tailWord_7999099 prefixEnd_7999099 4107382589899104222075319 := by
  unfold tailWord_7999099
  simp only [CollatzResearch.WordTrace]
  refine ⟨291751108847637935190560351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194500739231758623460373567 291751108847637935190560351)
  ·
    refine ⟨437626663271456902785840527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291751108847637935190560351 437626663271456902785840527)
    ·
      refine ⟨656439994907185354178760791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437626663271456902785840527 656439994907185354178760791)
      ·
        refine ⟨984659992360778031268141187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656439994907185354178760791 984659992360778031268141187)
        ·
          refine ⟨1476989988541167046902211781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984659992360778031268141187 1476989988541167046902211781)
          ·
            refine ⟨276935622851468821294164709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1476989988541167046902211781 276935622851468821294164709)
            ·
              refine ⟨51925429284650403992655883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276935622851468821294164709 51925429284650403992655883)
              ·
                refine ⟨77888143926975605988983825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51925429284650403992655883 77888143926975605988983825)
                ·
                  refine ⟨58416107945231704491737869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77888143926975605988983825 58416107945231704491737869)
                  ·
                    refine ⟨21906040479461889184401701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58416107945231704491737869 21906040479461889184401701)
                    ·
                      refine ⟨4107382589899104222075319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21906040479461889184401701 4107382589899104222075319)
                      ·
                        rfl

theorem cell23_7999099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_7999099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999099 prefixEnd_7999099 := by exact prefixLift 7999099
  have htrace : WordTrace (prefixWord ++ tailWord_7999099) baseStart_7999099 baseEnd_7999099 := by
    simpa [prefixWord, tailWord_7999099, baseEnd_7999099] using wordTrace_append hprefix tailTrace_7999099
  have hstable : (prefixWord ++ tailWord_7999099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999099).length < 2 ^ (prefixWord ++ tailWord_7999099).sum := by decide
  have hdescent : baseEnd_7999099 < baseStart_7999099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999109 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_7999109 : Nat := 118140960795 + 7999109 * 2 ^ 59
def prefixEnd_7999109 : Nat := 4983230072969 + 3 ^ 40 * 7999109 * 2
def baseEnd_7999109 : Nat := 1369129241568549727650091

theorem tailTrace_7999109 : CollatzResearch.WordTrace tailWord_7999109 prefixEnd_7999109 1369129241568549727650091 := by
  unfold tailWord_7999109
  simp only [CollatzResearch.WordTrace]
  refine ⟨291751473577601706898424381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194500982385067804598949587 291751473577601706898424381)
  ·
    refine ⟨109406802591600640086909143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291751473577601706898424381 109406802591600640086909143)
    ·
      refine ⟨164110203887400960130363715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109406802591600640086909143 164110203887400960130363715)
      ·
        refine ⟨246165305831101440195545573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164110203887400960130363715 246165305831101440195545573)
        ·
          refine ⟨46155994843331520036664795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246165305831101440195545573 46155994843331520036664795)
          ·
            refine ⟨69233992264997280054997193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46155994843331520036664795 69233992264997280054997193)
            ·
              refine ⟨51925494198747960041247895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69233992264997280054997193 51925494198747960041247895)
              ·
                refine ⟨77888241298121940061871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51925494198747960041247895 77888241298121940061871843)
                ·
                  refine ⟨116832361947182910092807765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77888241298121940061871843 116832361947182910092807765)
                  ·
                    refine ⟨1369129241568549727650091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116832361947182910092807765 1369129241568549727650091)
                    ·
                      rfl

theorem cell23_7999109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_7999109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999109 prefixEnd_7999109 := by exact prefixLift 7999109
  have htrace : WordTrace (prefixWord ++ tailWord_7999109) baseStart_7999109 baseEnd_7999109 := by
    simpa [prefixWord, tailWord_7999109, baseEnd_7999109] using wordTrace_append hprefix tailTrace_7999109
  have hstable : (prefixWord ++ tailWord_7999109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999109).length < 2 ^ (prefixWord ++ tailWord_7999109).sum := by decide
  have hdescent : baseEnd_7999109 < baseStart_7999109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999129 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_7999129 : Nat := 118140960795 + 7999129 * 2 ^ 59
def prefixEnd_7999129 : Nat := 4983230072969 + 3 ^ 40 * 7999129 * 2
def baseEnd_7999129 : Nat := 4107397994318739104700181

theorem tailTrace_7999129 : CollatzResearch.WordTrace tailWord_7999129 prefixEnd_7999129 4107397994318739104700181 := by
  unfold tailWord_7999129
  simp only [CollatzResearch.WordTrace]
  refine ⟨291752203037529250314152441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194501468691686166876101627 291752203037529250314152441)
  ·
    refine ⟨218814152278146937735614331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291752203037529250314152441 218814152278146937735614331)
    ·
      refine ⟨328221228417220406603421497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218814152278146937735614331 328221228417220406603421497)
      ·
        refine ⟨246165921312915304952566123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328221228417220406603421497 246165921312915304952566123)
        ·
          refine ⟨369248881969372957428849185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246165921312915304952566123 369248881969372957428849185)
          ·
            refine ⟨276936661477029718071636889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369248881969372957428849185 276936661477029718071636889)
            ·
              refine ⟨207702496107772288553727667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276936661477029718071636889 207702496107772288553727667)
              ·
                refine ⟨311553744161658432830591501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207702496107772288553727667 311553744161658432830591501)
                ·
                  refine ⟨116832654060621912311471813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311553744161658432830591501 116832654060621912311471813)
                  ·
                    refine ⟨21906122636366608558400965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116832654060621912311471813 21906122636366608558400965)
                    ·
                      refine ⟨4107397994318739104700181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21906122636366608558400965 4107397994318739104700181)
                      ·
                        rfl

theorem cell23_7999129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_7999129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999129 prefixEnd_7999129 := by exact prefixLift 7999129
  have htrace : WordTrace (prefixWord ++ tailWord_7999129) baseStart_7999129 baseEnd_7999129 := by
    simpa [prefixWord, tailWord_7999129, baseEnd_7999129] using wordTrace_append hprefix tailTrace_7999129
  have hstable : (prefixWord ++ tailWord_7999129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999129).length < 2 ^ (prefixWord ++ tailWord_7999129).sum := by decide
  have hdescent : baseEnd_7999129 < baseStart_7999129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999136 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_7999136 : Nat := 118140960795 + 7999136 * 2 ^ 59
def prefixEnd_7999136 : Nat := 4983230072969 + 3 ^ 40 * 7999136 * 2
def baseEnd_7999136 : Nat := 4107401588683320577312649

theorem tailTrace_7999136 : CollatzResearch.WordTrace tailWord_7999136 prefixEnd_7999136 4107401588683320577312649 := by
  unfold tailWord_7999136
  simp only [CollatzResearch.WordTrace]
  refine ⟨145876229174251945254828631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194501638899002593673104841 145876229174251945254828631)
  ·
    refine ⟨218814343761377917882242947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145876229174251945254828631 218814343761377917882242947)
    ·
      refine ⟨328221515642066876823364421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218814343761377917882242947 328221515642066876823364421)
      ·
        refine ⟨61541534182887539404380829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328221515642066876823364421 61541534182887539404380829)
        ·
          refine ⟨23078075318582827276642811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61541534182887539404380829 23078075318582827276642811)
          ·
            refine ⟨34617112977874240914964217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23078075318582827276642811 34617112977874240914964217)
            ·
              refine ⟨25962834733405680686223163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34617112977874240914964217 25962834733405680686223163)
              ·
                refine ⟨38944252100108521029334745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25962834733405680686223163 38944252100108521029334745)
                ·
                  refine ⟨29208189075081390772001059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38944252100108521029334745 29208189075081390772001059)
                  ·
                    refine ⟨43812283612622086158001589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29208189075081390772001059 43812283612622086158001589)
                    ·
                      refine ⟨4107401588683320577312649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43812283612622086158001589 4107401588683320577312649)
                      ·
                        rfl

theorem cell23_7999136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_7999136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999136 prefixEnd_7999136 := by exact prefixLift 7999136
  have htrace : WordTrace (prefixWord ++ tailWord_7999136) baseStart_7999136 baseEnd_7999136 := by
    simpa [prefixWord, tailWord_7999136, baseEnd_7999136] using wordTrace_append hprefix tailTrace_7999136
  have hstable : (prefixWord ++ tailWord_7999136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999136).length < 2 ^ (prefixWord ++ tailWord_7999136).sum := by decide
  have hdescent : baseEnd_7999136 < baseStart_7999136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999137 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7999137 : Nat := 118140960795 + 7999137 * 2 ^ 59
def prefixEnd_7999137 : Nat := 4983230072969 + 3 ^ 40 * 7999137 * 2
def baseEnd_7999137 : Nat := 4107402102163975073400145

theorem tailTrace_7999137 : CollatzResearch.WordTrace tailWord_7999137 prefixEnd_7999137 4107402102163975073400145 := by
  unfold tailWord_7999137
  simp only [CollatzResearch.WordTrace]
  refine ⟨291752494821500267680443665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194501663214333511786962443 291752494821500267680443665)
  ·
    refine ⟨218814371116125200760332749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291752494821500267680443665 218814371116125200760332749)
    ·
      refine ⟨82055389168546950285124781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218814371116125200760332749 82055389168546950285124781)
      ·
        refine ⟨30770770938205106356921793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82055389168546950285124781 30770770938205106356921793)
        ·
          refine ⟨23078078203653829767691345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30770770938205106356921793 23078078203653829767691345)
          ·
            refine ⟨17308558652740372325768509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23078078203653829767691345 17308558652740372325768509)
            ·
              refine ⟨6490709494777639622163191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17308558652740372325768509 6490709494777639622163191)
              ·
                refine ⟨9736064242166459433244787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490709494777639622163191 9736064242166459433244787)
                ·
                  refine ⟨14604096363249689149867181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736064242166459433244787 14604096363249689149867181)
                  ·
                    refine ⟨5476536136218633431200193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14604096363249689149867181 5476536136218633431200193)
                    ·
                      refine ⟨4107402102163975073400145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476536136218633431200193 4107402102163975073400145)
                      ·
                        rfl

theorem cell23_7999137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7999137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999137 prefixEnd_7999137 := by exact prefixLift 7999137
  have htrace : WordTrace (prefixWord ++ tailWord_7999137) baseStart_7999137 baseEnd_7999137 := by
    simpa [prefixWord, tailWord_7999137, baseEnd_7999137] using wordTrace_append hprefix tailTrace_7999137
  have hstable : (prefixWord ++ tailWord_7999137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999137).length < 2 ^ (prefixWord ++ tailWord_7999137).sum := by decide
  have hdescent : baseEnd_7999137 < baseStart_7999137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999179 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_7999179 : Nat := 118140960795 + 7999179 * 2 ^ 59
def prefixEnd_7999179 : Nat := 4983230072969 + 3 ^ 40 * 7999179 * 2
def baseEnd_7999179 : Nat := 4107423668351463909074951

theorem tailTrace_7999179 : CollatzResearch.WordTrace tailWord_7999179 prefixEnd_7999179 4107423668351463909074951 := by
  unfold tailWord_7999179
  simp only [CollatzResearch.WordTrace]
  refine ⟨291754026687348108853472591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194502684458232072568981727 291754026687348108853472591)
  ·
    refine ⟨437631040031022163280208887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291754026687348108853472591 437631040031022163280208887)
    ·
      refine ⟨656446560046533244920313331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437631040031022163280208887 656446560046533244920313331)
      ·
        refine ⟨984669840069799867380469997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656446560046533244920313331 984669840069799867380469997)
        ·
          refine ⟨369251190026174950267676249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984669840069799867380469997 369251190026174950267676249)
          ·
            refine ⟨276938392519631212700757187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369251190026174950267676249 276938392519631212700757187)
            ·
              refine ⟨415407588779446819051135781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276938392519631212700757187 415407588779446819051135781)
              ·
                refine ⟨77888922896146278572087959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415407588779446819051135781 77888922896146278572087959)
                ·
                  refine ⟨116833384344219417858131939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77888922896146278572087959 116833384344219417858131939)
                  ·
                    refine ⟨175250076516329126787197909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116833384344219417858131939 175250076516329126787197909)
                    ·
                      refine ⟨4107423668351463909074951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175250076516329126787197909 4107423668351463909074951)
                      ·
                        rfl

theorem cell23_7999179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_7999179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999179 prefixEnd_7999179 := by exact prefixLift 7999179
  have htrace : WordTrace (prefixWord ++ tailWord_7999179) baseStart_7999179 baseEnd_7999179 := by
    simpa [prefixWord, tailWord_7999179, baseEnd_7999179] using wordTrace_append hprefix tailTrace_7999179
  have hstable : (prefixWord ++ tailWord_7999179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999179).length < 2 ^ (prefixWord ++ tailWord_7999179).sum := by decide
  have hdescent : baseEnd_7999179 < baseStart_7999179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999220 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7999220 : Nat := 118140960795 + 7999220 * 2 ^ 59
def prefixEnd_7999220 : Nat := 4983230072969 + 3 ^ 40 * 7999220 * 2
def baseEnd_7999220 : Nat := 1369148240352766082887421

theorem tailTrace_7999220 : CollatzResearch.WordTrace tailWord_7999220 prefixEnd_7999220 1369148240352766082887421 := by
  unfold tailWord_7999220
  simp only [CollatzResearch.WordTrace]
  refine ⟨145877761040099786427857557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194503681386799715237143409 145877761040099786427857557)
  ·
    refine ⟨6838020048754677488805823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145877761040099786427857557 6838020048754677488805823)
    ·
      refine ⟨10257030073132016233208735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838020048754677488805823 10257030073132016233208735)
      ·
        refine ⟨15385545109698024349813103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257030073132016233208735 15385545109698024349813103)
        ·
          refine ⟨23078317664547036524719655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15385545109698024349813103 23078317664547036524719655)
          ·
            refine ⟨34617476496820554787079483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23078317664547036524719655 34617476496820554787079483)
            ·
              refine ⟨51926214745230832180619225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34617476496820554787079483 51926214745230832180619225)
              ·
                refine ⟨38944661058923124135464419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51926214745230832180619225 38944661058923124135464419)
                ·
                  refine ⟨58416991588384686203196629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38944661058923124135464419 58416991588384686203196629)
                  ·
                    refine ⟨1369148240352766082887421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58416991588384686203196629 1369148240352766082887421)
                    ·
                      rfl

theorem cell23_7999220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7999220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999220 prefixEnd_7999220 := by exact prefixLift 7999220
  have htrace : WordTrace (prefixWord ++ tailWord_7999220) baseStart_7999220 baseEnd_7999220 := by
    simpa [prefixWord, tailWord_7999220, baseEnd_7999220] using wordTrace_append hprefix tailTrace_7999220
  have hstable : (prefixWord ++ tailWord_7999220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999220).length < 2 ^ (prefixWord ++ tailWord_7999220).sum := by decide
  have hdescent : baseEnd_7999220 < baseStart_7999220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999223 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_7999223 : Nat := 118140960795 + 7999223 * 2 ^ 59
def prefixEnd_7999223 : Nat := 4983230072969 + 3 ^ 40 * 7999223 * 2
def baseEnd_7999223 : Nat := 4107446261500261736924749

theorem tailTrace_7999223 : CollatzResearch.WordTrace tailWord_7999223 prefixEnd_7999223 4107446261500261736924749 := by
  unfold tailWord_7999223
  simp only [CollatzResearch.WordTrace]
  refine ⟨291755631499188704368074323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194503754332792469578716215 291755631499188704368074323)
  ·
    refine ⟨437633447248783056552111485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291755631499188704368074323 437633447248783056552111485)
    ·
      refine ⟨164112542718293646207041807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437633447248783056552111485 164112542718293646207041807)
      ·
        refine ⟨246168814077440469310562711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164112542718293646207041807 246168814077440469310562711)
        ·
          refine ⟨369253221116160703965844067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246168814077440469310562711 369253221116160703965844067)
          ·
            refine ⟨553879831674241055948766101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369253221116160703965844067 553879831674241055948766101)
            ·
              refine ⟨25963117109730049497598411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553879831674241055948766101 25963117109730049497598411)
              ·
                refine ⟨38944675664595074246397617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25963117109730049497598411 38944675664595074246397617)
                ·
                  refine ⟨29208506748446305684798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38944675664595074246397617 29208506748446305684798213)
                  ·
                    refine ⟨5476595015333682315899665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29208506748446305684798213 5476595015333682315899665)
                    ·
                      refine ⟨4107446261500261736924749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476595015333682315899665 4107446261500261736924749)
                      ·
                        rfl

theorem cell23_7999223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_7999223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999223 prefixEnd_7999223 := by exact prefixLift 7999223
  have htrace : WordTrace (prefixWord ++ tailWord_7999223) baseStart_7999223 baseEnd_7999223 := by
    simpa [prefixWord, tailWord_7999223, baseEnd_7999223] using wordTrace_append hprefix tailTrace_7999223
  have hstable : (prefixWord ++ tailWord_7999223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999223).length < 2 ^ (prefixWord ++ tailWord_7999223).sum := by decide
  have hdescent : baseEnd_7999223 < baseStart_7999223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999233 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7999233 : Nat := 118140960795 + 7999233 * 2 ^ 59
def prefixEnd_7999233 : Nat := 4983230072969 + 3 ^ 40 * 7999233 * 2
def baseEnd_7999233 : Nat := 1369150465435602232599901

theorem tailTrace_7999233 : CollatzResearch.WordTrace tailWord_7999233 prefixEnd_7999233 1369150465435602232599901 := by
  unfold tailWord_7999233
  simp only [CollatzResearch.WordTrace]
  refine ⟨291755996229152476075938353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194503997486101650717292235 291755996229152476075938353)
  ·
    refine ⟨218816997171864357056953765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291755996229152476075938353 218816997171864357056953765)
    ·
      refine ⟨41028186969724566948178831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218816997171864357056953765 41028186969724566948178831)
      ·
        refine ⟨61542280454586850422268247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41028186969724566948178831 61542280454586850422268247)
        ·
          refine ⟨92313420681880275633402371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61542280454586850422268247 92313420681880275633402371)
          ·
            refine ⟨138470131022820413450103557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92313420681880275633402371 138470131022820413450103557)
            ·
              refine ⟨25963149566778827521894417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138470131022820413450103557 25963149566778827521894417)
              ·
                refine ⟨19472362175084120641420813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25963149566778827521894417 19472362175084120641420813)
                ·
                  refine ⟨7302135815656545240532805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19472362175084120641420813 7302135815656545240532805)
                  ·
                    refine ⟨1369150465435602232599901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302135815656545240532805 1369150465435602232599901)
                    ·
                      rfl

theorem cell23_7999233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7999233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999233 prefixEnd_7999233 := by exact prefixLift 7999233
  have htrace : WordTrace (prefixWord ++ tailWord_7999233) baseStart_7999233 baseEnd_7999233 := by
    simpa [prefixWord, tailWord_7999233, baseEnd_7999233] using wordTrace_append hprefix tailTrace_7999233
  have hstable : (prefixWord ++ tailWord_7999233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999233).length < 2 ^ (prefixWord ++ tailWord_7999233).sum := by decide
  have hdescent : baseEnd_7999233 < baseStart_7999233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999246 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_7999246 : Nat := 118140960795 + 7999246 * 2 ^ 59
def prefixEnd_7999246 : Nat := 4983230072969 + 3 ^ 40 * 7999246 * 2
def baseEnd_7999246 : Nat := 456384230172812794104127

theorem tailTrace_7999246 : CollatzResearch.WordTrace tailWord_7999246 prefixEnd_7999246 456384230172812794104127 := by
  unfold tailWord_7999246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36469558797263172412020199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194504313585403586197441061 36469558797263172412020199)
  ·
    refine ⟨54704338195894758618030299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36469558797263172412020199 54704338195894758618030299)
    ·
      refine ⟨82056507293842137927045449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54704338195894758618030299 82056507293842137927045449)
      ·
        refine ⟨61542380470381603445284087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82056507293842137927045449 61542380470381603445284087)
        ·
          refine ⟨92313570705572405167926131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61542380470381603445284087 92313570705572405167926131)
          ·
            refine ⟨138470356058358607751889197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92313570705572405167926131 138470356058358607751889197)
            ·
              refine ⟨51926383521884477906958449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138470356058358607751889197 51926383521884477906958449)
              ·
                refine ⟨38944787641413358430218837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51926383521884477906958449 38944787641413358430218837)
                ·
                  refine ⟨456384230172812794104127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38944787641413358430218837 456384230172812794104127)
                  ·
                    rfl

theorem cell23_7999246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_7999246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999246 prefixEnd_7999246 := by exact prefixLift 7999246
  have htrace : WordTrace (prefixWord ++ tailWord_7999246) baseStart_7999246 baseEnd_7999246 := by
    simpa [prefixWord, tailWord_7999246, baseEnd_7999246] using wordTrace_append hprefix tailTrace_7999246
  have hstable : (prefixWord ++ tailWord_7999246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999246).length < 2 ^ (prefixWord ++ tailWord_7999246).sum := by decide
  have hdescent : baseEnd_7999246 < baseStart_7999246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999330 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7999330 : Nat := 118140960795 + 7999330 * 2 ^ 59
def prefixEnd_7999330 : Nat := 4983230072969 + 3 ^ 40 * 7999330 * 2
def baseEnd_7999330 : Nat := 4107501203930292818286757

theorem tailTrace_7999330 : CollatzResearch.WordTrace tailWord_7999330 prefixEnd_7999330 4107501203930292818286757 := by
  unfold tailWord_7999330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72939883527450265410554861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194506356073200707761479629 72939883527450265410554861)
  ·
    refine ⟨27352456322793849528958073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72939883527450265410554861 27352456322793849528958073)
    ·
      refine ⟨20514342242095387146718555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27352456322793849528958073 20514342242095387146718555)
      ·
        refine ⟨30771513363143080720077833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20514342242095387146718555 30771513363143080720077833)
        ·
          refine ⟨23078635022357310540058375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30771513363143080720077833 23078635022357310540058375)
          ·
            refine ⟨34617952533535965810087563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23078635022357310540058375 34617952533535965810087563)
            ·
              refine ⟨51926928800303948715131345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34617952533535965810087563 51926928800303948715131345)
              ·
                refine ⟨38945196600227961536348509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51926928800303948715131345 38945196600227961536348509)
                ·
                  refine ⟨14604448725085485576130691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38945196600227961536348509 14604448725085485576130691)
                  ·
                    refine ⟨21906673087628228364196037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14604448725085485576130691 21906673087628228364196037)
                    ·
                      refine ⟨4107501203930292818286757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21906673087628228364196037 4107501203930292818286757)
                      ·
                        rfl

theorem cell23_7999330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7999330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999330 prefixEnd_7999330 := by exact prefixLift 7999330
  have htrace : WordTrace (prefixWord ++ tailWord_7999330) baseStart_7999330 baseEnd_7999330 := by
    simpa [prefixWord, tailWord_7999330, baseEnd_7999330] using wordTrace_append hprefix tailTrace_7999330
  have hstable : (prefixWord ++ tailWord_7999330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999330).length < 2 ^ (prefixWord ++ tailWord_7999330).sum := by decide
  have hdescent : baseEnd_7999330 < baseStart_7999330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999340 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_7999340 : Nat := 118140960795 + 7999340 * 2 ^ 59
def prefixEnd_7999340 : Nat := 4983230072969 + 3 ^ 40 * 7999340 * 2
def baseEnd_7999340 : Nat := 1369168779578945926387237

theorem tailTrace_7999340 : CollatzResearch.WordTrace tailWord_7999340 prefixEnd_7999340 1369168779578945926387237 := by
  unfold tailWord_7999340
  simp only [CollatzResearch.WordTrace]
  refine ⟨145879949419882416675041737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194506599226509888900055649 145879949419882416675041737)
  ·
    refine ⟨109409962064911812506281303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145879949419882416675041737 109409962064911812506281303)
    ·
      refine ⟨164114943097367718759421955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109409962064911812506281303 164114943097367718759421955)
      ·
        refine ⟨246172414646051578139132933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164114943097367718759421955 246172414646051578139132933)
        ·
          refine ⟨46157327746134670901087425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246172414646051578139132933 46157327746134670901087425)
          ·
            refine ⟨34617995809601003175815569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46157327746134670901087425 34617995809601003175815569)
            ·
              refine ⟨25963496857200752381861677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34617995809601003175815569 25963496857200752381861677)
              ·
                refine ⟨9736311321450282143198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25963496857200752381861677 9736311321450282143198129)
                ·
                  refine ⟨7302233491087711607398597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736311321450282143198129 7302233491087711607398597)
                  ·
                    refine ⟨1369168779578945926387237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302233491087711607398597 1369168779578945926387237)
                    ·
                      rfl

theorem cell23_7999340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_7999340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999340 prefixEnd_7999340 := by exact prefixLift 7999340
  have htrace : WordTrace (prefixWord ++ tailWord_7999340) baseStart_7999340 baseEnd_7999340 := by
    simpa [prefixWord, tailWord_7999340, baseEnd_7999340] using wordTrace_append hprefix tailTrace_7999340
  have hstable : (prefixWord ++ tailWord_7999340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999340).length < 2 ^ (prefixWord ++ tailWord_7999340).sum := by decide
  have hdescent : baseEnd_7999340 < baseStart_7999340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999353 : List Nat := [1, 2, 1, 3, 2, 2, 5, 7]
def baseStart_7999353 : Nat := 118140960795 + 7999353 * 2 ^ 59
def prefixEnd_7999353 : Nat := 4983230072969 + 3 ^ 40 * 7999353 * 2
def baseEnd_7999353 : Nat := 152130111629086897344413

theorem tailTrace_7999353 : CollatzResearch.WordTrace tailWord_7999353 prefixEnd_7999353 152130111629086897344413 := by
  unfold tailWord_7999353
  simp only [CollatzResearch.WordTrace]
  refine ⟨291760372988717736570306713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194506915325811824380204475 291760372988717736570306713)
  ·
    refine ⟨218820279741538302427730035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291760372988717736570306713 218820279741538302427730035)
    ·
      refine ⟨328230419612307453641595053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218820279741538302427730035 328230419612307453641595053)
      ·
        refine ⟨123086407354615295115598145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328230419612307453641595053 123086407354615295115598145)
        ·
          refine ⟨92314805515961471336698609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123086407354615295115598145 92314805515961471336698609)
          ·
            refine ⟨69236104136971103502523957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92314805515961471336698609 69236104136971103502523957)
            ·
              refine ⟨6490884762841040953361621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69236104136971103502523957 6490884762841040953361621)
              ·
                refine ⟨152130111629086897344413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6490884762841040953361621 152130111629086897344413)
                ·
                  rfl

theorem cell23_7999353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 7].length) (baseStart_7999353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999353 prefixEnd_7999353 := by exact prefixLift 7999353
  have htrace : WordTrace (prefixWord ++ tailWord_7999353) baseStart_7999353 baseEnd_7999353 := by
    simpa [prefixWord, tailWord_7999353, baseEnd_7999353] using wordTrace_append hprefix tailTrace_7999353
  have hstable : (prefixWord ++ tailWord_7999353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999353).length < 2 ^ (prefixWord ++ tailWord_7999353).sum := by decide
  have hdescent : baseEnd_7999353 < baseStart_7999353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999361 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7999361 : Nat := 118140960795 + 7999361 * 2 ^ 59
def prefixEnd_7999361 : Nat := 4983230072969 + 3 ^ 40 * 7999361 * 2
def baseEnd_7999361 : Nat := 1369172373943527398999705

theorem tailTrace_7999361 : CollatzResearch.WordTrace tailWord_7999361 prefixEnd_7999361 1369172373943527398999705 := by
  unfold tailWord_7999361
  simp only [CollatzResearch.WordTrace]
  refine ⟨291760664772688753936597937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194507109848459169291065291 291760664772688753936597937)
  ·
    refine ⟨218820498579516565452448453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291760664772688753936597937 218820498579516565452448453)
    ·
      refine ⟨41028843483659356022334085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218820498579516565452448453 41028843483659356022334085)
      ·
        refine ⟨7692908153186129254187641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41028843483659356022334085 7692908153186129254187641)
        ·
          refine ⟨5769681114889596940640731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7692908153186129254187641 5769681114889596940640731)
          ·
            refine ⟨8654521672334395410961097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769681114889596940640731 8654521672334395410961097)
            ·
              refine ⟨6490891254250796558220823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8654521672334395410961097 6490891254250796558220823)
              ·
                refine ⟨9736336881376194837331235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490891254250796558220823 9736336881376194837331235)
                ·
                  refine ⟨14604505322064292255996853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736336881376194837331235 14604505322064292255996853)
                  ·
                    refine ⟨1369172373943527398999705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14604505322064292255996853 1369172373943527398999705)
                    ·
                      rfl

theorem cell23_7999361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7999361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999361 prefixEnd_7999361 := by exact prefixLift 7999361
  have htrace : WordTrace (prefixWord ++ tailWord_7999361) baseStart_7999361 baseEnd_7999361 := by
    simpa [prefixWord, tailWord_7999361, baseEnd_7999361] using wordTrace_append hprefix tailTrace_7999361
  have hstable : (prefixWord ++ tailWord_7999361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999361).length < 2 ^ (prefixWord ++ tailWord_7999361).sum := by decide
  have hdescent : baseEnd_7999361 < baseStart_7999361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999364 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7999364 : Nat := 118140960795 + 7999364 * 2 ^ 59
def prefixEnd_7999364 : Nat := 4983230072969 + 3 ^ 40 * 7999364 * 2
def baseEnd_7999364 : Nat := 4107518662272545685261601

theorem tailTrace_7999364 : CollatzResearch.WordTrace tailWord_7999364 prefixEnd_7999364 4107518662272545685261601 := by
  unfold tailWord_7999364
  simp only [CollatzResearch.WordTrace]
  refine ⟨145880387095838942724478573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194507182794451923632638097 145880387095838942724478573)
  ·
    refine ⟨54705145160939603521679465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145880387095838942724478573 54705145160939603521679465)
    ·
      refine ⟨41028858870704702641259599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54705145160939603521679465 41028858870704702641259599)
      ·
        refine ⟨61543288306057053961889399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41028858870704702641259599 61543288306057053961889399)
        ·
          refine ⟨92314932459085580942834099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61543288306057053961889399 92314932459085580942834099)
          ·
            refine ⟨138472398688628371414251149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92314932459085580942834099 138472398688628371414251149)
            ·
              refine ⟨51927149508235639280344181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138472398688628371414251149 51927149508235639280344181)
              ·
                refine ⟨4868170266397091182532267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51927149508235639280344181 4868170266397091182532267)
                ·
                  refine ⟨7302255399595636773798401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868170266397091182532267 7302255399595636773798401)
                  ·
                    refine ⟨5476691549696727580348801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302255399595636773798401 5476691549696727580348801)
                    ·
                      refine ⟨4107518662272545685261601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476691549696727580348801 4107518662272545685261601)
                      ·
                        rfl

theorem cell23_7999364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7999364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999364 prefixEnd_7999364 := by exact prefixLift 7999364
  have htrace : WordTrace (prefixWord ++ tailWord_7999364) baseStart_7999364 baseEnd_7999364 := by
    simpa [prefixWord, tailWord_7999364, baseEnd_7999364] using wordTrace_append hprefix tailTrace_7999364
  have hstable : (prefixWord ++ tailWord_7999364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999364).length < 2 ^ (prefixWord ++ tailWord_7999364).sum := by decide
  have hdescent : baseEnd_7999364 < baseStart_7999364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999367 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_7999367 : Nat := 118140960795 + 7999367 * 2 ^ 59
def prefixEnd_7999367 : Nat := 4983230072969 + 3 ^ 40 * 7999367 * 2
def baseEnd_7999367 : Nat := 4107520202714509173524087

theorem tailTrace_7999367 : CollatzResearch.WordTrace tailWord_7999367 prefixEnd_7999367 4107520202714509173524087 := by
  unfold tailWord_7999367
  simp only [CollatzResearch.WordTrace]
  refine ⟨291760883610667016961316355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194507255740444677974210903 291760883610667016961316355)
  ·
    refine ⟨437641325416000525441974533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291760883610667016961316355 437641325416000525441974533)
    ·
      refine ⟨82057748515500098520370225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437641325416000525441974533 82057748515500098520370225)
      ·
        refine ⟨61543311386625073890277669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82057748515500098520370225 61543311386625073890277669)
        ·
          refine ⟨11539370884992201354427063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61543311386625073890277669 11539370884992201354427063)
          ·
            refine ⟨17309056327488302031640595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539370884992201354427063 17309056327488302031640595)
            ·
              refine ⟨25963584491232453047460893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17309056327488302031640595 25963584491232453047460893)
              ·
                refine ⟨9736344184212169892797835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25963584491232453047460893 9736344184212169892797835)
                ·
                  refine ⟨14604516276318254839196753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736344184212169892797835 14604516276318254839196753)
                  ·
                    refine ⟨10953387207238691129397565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14604516276318254839196753 10953387207238691129397565)
                    ·
                      refine ⟨4107520202714509173524087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10953387207238691129397565 4107520202714509173524087)
                      ·
                        rfl

theorem cell23_7999367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_7999367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999367 prefixEnd_7999367 := by exact prefixLift 7999367
  have htrace : WordTrace (prefixWord ++ tailWord_7999367) baseStart_7999367 baseEnd_7999367 := by
    simpa [prefixWord, tailWord_7999367, baseEnd_7999367] using wordTrace_append hprefix tailTrace_7999367
  have hstable : (prefixWord ++ tailWord_7999367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999367).length < 2 ^ (prefixWord ++ tailWord_7999367).sum := by decide
  have hdescent : baseEnd_7999367 < baseStart_7999367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999394 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7999394 : Nat := 118140960795 + 7999394 * 2 ^ 59
def prefixEnd_7999394 : Nat := 4983230072969 + 3 ^ 40 * 7999394 * 2
def baseEnd_7999394 : Nat := 4107534066692180567886463

theorem tailTrace_7999394 : CollatzResearch.WordTrace tailWord_7999394 prefixEnd_7999394 4107534066692180567886463 := by
  unfold tailWord_7999394
  simp only [CollatzResearch.WordTrace]
  refine ⟨72940467095392300143137309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194507912254379467048366157 72940467095392300143137309)
  ·
    refine ⟨27352675160772112553676491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72940467095392300143137309 27352675160772112553676491)
    ·
      refine ⟨41029012741158168830514737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27352675160772112553676491 41029012741158168830514737)
      ·
        refine ⟨30771759555868626622886053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41029012741158168830514737 30771759555868626622886053)
        ·
          refine ⟨5769704916725367491791135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30771759555868626622886053 5769704916725367491791135)
          ·
            refine ⟨8654557375088051237686703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769704916725367491791135 8654557375088051237686703)
            ·
              refine ⟨12981836062632076856530055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654557375088051237686703 12981836062632076856530055)
              ·
                refine ⟨19472754093948115284795083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12981836062632076856530055 19472754093948115284795083)
                ·
                  refine ⟨29209131140922172927192625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19472754093948115284795083 29209131140922172927192625)
                  ·
                    refine ⟨21906848355691629695394469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29209131140922172927192625 21906848355691629695394469)
                    ·
                      refine ⟨4107534066692180567886463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21906848355691629695394469 4107534066692180567886463)
                      ·
                        rfl

theorem cell23_7999394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7999394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999394 prefixEnd_7999394 := by exact prefixLift 7999394
  have htrace : WordTrace (prefixWord ++ tailWord_7999394) baseStart_7999394 baseEnd_7999394 := by
    simpa [prefixWord, tailWord_7999394, baseEnd_7999394] using wordTrace_append hprefix tailTrace_7999394
  have hstable : (prefixWord ++ tailWord_7999394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999394).length < 2 ^ (prefixWord ++ tailWord_7999394).sum := by decide
  have hdescent : baseEnd_7999394 < baseStart_7999394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999407 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 1, 3, 2]
def baseStart_7999407 : Nat := 118140960795 + 7999407 * 2 ^ 59
def prefixEnd_7999407 : Nat := 4983230072969 + 3 ^ 40 * 7999407 * 2
def baseEnd_7999407 : Nat := 4107540741940689017023903

theorem tailTrace_7999407 : CollatzResearch.WordTrace tailWord_7999407 prefixEnd_7999407 4107540741940689017023903 := by
  unfold tailWord_7999407
  simp only [CollatzResearch.WordTrace]
  refine ⟨291762342530522103792772475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194508228353681402528514983 291762342530522103792772475)
  ·
    refine ⟨437643513795783155689158713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291762342530522103792772475 437643513795783155689158713)
    ·
      refine ⟨328232635346837366766869035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437643513795783155689158713 328232635346837366766869035)
      ·
        refine ⟨492348953020256050150303553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328232635346837366766869035 492348953020256050150303553)
        ·
          refine ⟨369261714765192037612727665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492348953020256050150303553 369261714765192037612727665)
          ·
            refine ⟨276946286073894028209545749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369261714765192037612727665 276946286073894028209545749)
            ·
              refine ⟨12981857159713782572322457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276946286073894028209545749 12981857159713782572322457)
              ·
                refine ⟨9736392869785336929241843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12981857159713782572322457 9736392869785336929241843)
                ·
                  refine ⟨14604589304678005393862765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736392869785336929241843 14604589304678005393862765)
                  ·
                    refine ⟨5476720989254252022698537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14604589304678005393862765 5476720989254252022698537)
                    ·
                      refine ⟨4107540741940689017023903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476720989254252022698537 4107540741940689017023903)
                      ·
                        rfl

theorem cell23_7999407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3, 2].length) (baseStart_7999407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999407 prefixEnd_7999407 := by exact prefixLift 7999407
  have htrace : WordTrace (prefixWord ++ tailWord_7999407) baseStart_7999407 baseEnd_7999407 := by
    simpa [prefixWord, tailWord_7999407, baseEnd_7999407] using wordTrace_append hprefix tailTrace_7999407
  have hstable : (prefixWord ++ tailWord_7999407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999407).length < 2 ^ (prefixWord ++ tailWord_7999407).sum := by decide
  have hdescent : baseEnd_7999407 < baseStart_7999407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999423 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_7999423 : Nat := 118140960795 + 7999423 * 2 ^ 59
def prefixEnd_7999423 : Nat := 4983230072969 + 3 ^ 40 * 7999423 * 2
def baseEnd_7999423 : Nat := 4107548957631160954423829

theorem tailTrace_7999423 : CollatzResearch.WordTrace tailWord_7999423 prefixEnd_7999423 4107548957631160954423829 := by
  unfold tailWord_7999423
  simp only [CollatzResearch.WordTrace]
  refine ⟨291762926098464138525354923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194508617398976092350236615 291762926098464138525354923)
  ·
    refine ⟨437644389147696207788032385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291762926098464138525354923 437644389147696207788032385)
    ·
      refine ⟨328233291860772155841024289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437644389147696207788032385 328233291860772155841024289)
      ·
        refine ⟨246174968895579116880768217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328233291860772155841024289 246174968895579116880768217)
        ·
          refine ⟨184631226671684337660576163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246174968895579116880768217 184631226671684337660576163)
          ·
            refine ⟨276946840007526506490864245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184631226671684337660576163 276946840007526506490864245)
            ·
              refine ⟨25963766250705609983518523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276946840007526506490864245 25963766250705609983518523)
              ·
                refine ⟨38945649376058414975277785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25963766250705609983518523 38945649376058414975277785)
                ·
                  refine ⟨29209237032043811231458339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38945649376058414975277785 29209237032043811231458339)
                  ·
                    refine ⟨43813855548065716847187509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29209237032043811231458339 43813855548065716847187509)
                    ·
                      refine ⟨4107548957631160954423829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43813855548065716847187509 4107548957631160954423829)
                      ·
                        rfl

theorem cell23_7999423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_7999423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999423 prefixEnd_7999423 := by exact prefixLift 7999423
  have htrace : WordTrace (prefixWord ++ tailWord_7999423) baseStart_7999423 baseEnd_7999423 := by
    simpa [prefixWord, tailWord_7999423, baseEnd_7999423] using wordTrace_append hprefix tailTrace_7999423
  have hstable : (prefixWord ++ tailWord_7999423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999423).length < 2 ^ (prefixWord ++ tailWord_7999423).sum := by decide
  have hdescent : baseEnd_7999423 < baseStart_7999423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999458 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7999458 : Nat := 118140960795 + 7999458 * 2 ^ 59
def prefixEnd_7999458 : Nat := 4983230072969 + 3 ^ 40 * 7999458 * 2
def baseEnd_7999458 : Nat := 4107566929454068317486169

theorem tailTrace_7999458 : CollatzResearch.WordTrace tailWord_7999458 prefixEnd_7999458 4107566929454068317486169 := by
  unfold tailWord_7999458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72941050663334334875719757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194509468435558226335252685 72941050663334334875719757)
  ·
    refine ⟨27352893998750375578394909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72941050663334334875719757 27352893998750375578394909)
    ·
      refine ⟨10257335249531390841898091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27352893998750375578394909 10257335249531390841898091)
      ·
        refine ⟨15386002874297086262847137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257335249531390841898091 15386002874297086262847137)
        ·
          refine ⟨11539502155722814697135353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386002874297086262847137 11539502155722814697135353)
          ·
            refine ⟨8654626616792111022851515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11539502155722814697135353 8654626616792111022851515)
            ·
              refine ⟨12981939925188166534277273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654626616792111022851515 12981939925188166534277273)
              ·
                refine ⟨9736454943891124900707955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12981939925188166534277273 9736454943891124900707955)
                ·
                  refine ⟨14604682415836687351061933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736454943891124900707955 14604682415836687351061933)
                  ·
                    refine ⟨5476755905938757756648225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14604682415836687351061933 5476755905938757756648225)
                    ·
                      refine ⟨4107566929454068317486169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476755905938757756648225 4107566929454068317486169)
                      ·
                        rfl

theorem cell23_7999458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7999458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999458 prefixEnd_7999458 := by exact prefixLift 7999458
  have htrace : WordTrace (prefixWord ++ tailWord_7999458) baseStart_7999458 baseEnd_7999458 := by
    simpa [prefixWord, tailWord_7999458, baseEnd_7999458] using wordTrace_append hprefix tailTrace_7999458
  have hstable : (prefixWord ++ tailWord_7999458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999458).length < 2 ^ (prefixWord ++ tailWord_7999458).sum := by decide
  have hdescent : baseEnd_7999458 < baseStart_7999458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999483 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_7999483 : Nat := 118140960795 + 7999483 * 2 ^ 59
def prefixEnd_7999483 : Nat := 4983230072969 + 3 ^ 40 * 7999483 * 2
def baseEnd_7999483 : Nat := 4107579766470430719673553

theorem tailTrace_7999483 : CollatzResearch.WordTrace tailWord_7999483 prefixEnd_7999483 4107579766470430719673553 := by
  unfold tailWord_7999483
  simp only [CollatzResearch.WordTrace]
  refine ⟨291765114478246768772539103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194510076318831179181692735 291765114478246768772539103)
  ·
    refine ⟨437647671717370153158808655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291765114478246768772539103 437647671717370153158808655)
    ·
      refine ⟨656471507576055229738212983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437647671717370153158808655 656471507576055229738212983)
      ·
        refine ⟨984707261364082844607319475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656471507576055229738212983 984707261364082844607319475)
        ·
          refine ⟨1477060892046124266910979213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984707261364082844607319475 1477060892046124266910979213)
          ·
            refine ⟨553897834517296600091617205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1477060892046124266910979213 553897834517296600091617205)
            ·
              refine ⟨51927921985996556258589113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 553897834517296600091617205 51927921985996556258589113)
              ·
                refine ⟨38945941489497417193941835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51927921985996556258589113 38945941489497417193941835)
                ·
                  refine ⟨58418912234246125790912753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38945941489497417193941835 58418912234246125790912753)
                  ·
                    refine ⟨43814184175684594343184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58418912234246125790912753 43814184175684594343184565)
                    ·
                      refine ⟨4107579766470430719673553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43814184175684594343184565 4107579766470430719673553)
                      ·
                        rfl

theorem cell23_7999483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_7999483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999483 prefixEnd_7999483 := by exact prefixLift 7999483
  have htrace : WordTrace (prefixWord ++ tailWord_7999483) baseStart_7999483 baseEnd_7999483 := by
    simpa [prefixWord, tailWord_7999483, baseEnd_7999483] using wordTrace_append hprefix tailTrace_7999483
  have hstable : (prefixWord ++ tailWord_7999483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999483).length < 2 ^ (prefixWord ++ tailWord_7999483).sum := by decide
  have hdescent : baseEnd_7999483 < baseStart_7999483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999501 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7999501 : Nat := 118140960795 + 7999501 * 2 ^ 59
def prefixEnd_7999501 : Nat := 4983230072969 + 3 ^ 40 * 7999501 * 2
def baseEnd_7999501 : Nat := 4107589009122211649248471

theorem tailTrace_7999501 : CollatzResearch.WordTrace tailWord_7999501 prefixEnd_7999501 4107589009122211649248471 := by
  unfold tailWord_7999501
  simp only [CollatzResearch.WordTrace]
  refine ⟨291765770992181557846694357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194510513994787705231129571 291765770992181557846694357)
  ·
    refine ⟨6838260257629255262031899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 291765770992181557846694357 6838260257629255262031899)
    ·
      refine ⟨10257390386443882893047849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838260257629255262031899 10257390386443882893047849)
      ·
        refine ⟨7693042789832912169785887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10257390386443882893047849 7693042789832912169785887)
        ·
          refine ⟨11539564184749368254678831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693042789832912169785887 11539564184749368254678831)
          ·
            refine ⟨17309346277124052382018247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539564184749368254678831 17309346277124052382018247)
            ·
              refine ⟨25964019415686078573027371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17309346277124052382018247 25964019415686078573027371)
              ·
                refine ⟨38946029123529117859541057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25964019415686078573027371 38946029123529117859541057)
                ·
                  refine ⟨29209521842646838394655793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38946029123529117859541057 29209521842646838394655793)
                  ·
                    refine ⟨21907141381985128795991845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29209521842646838394655793 21907141381985128795991845)
                    ·
                      refine ⟨4107589009122211649248471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21907141381985128795991845 4107589009122211649248471)
                      ·
                        rfl

theorem cell23_7999501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7999501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999501 prefixEnd_7999501 := by exact prefixLift 7999501
  have htrace : WordTrace (prefixWord ++ tailWord_7999501) baseStart_7999501 baseEnd_7999501 := by
    simpa [prefixWord, tailWord_7999501, baseEnd_7999501] using wordTrace_append hprefix tailTrace_7999501
  have hstable : (prefixWord ++ tailWord_7999501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999501).length < 2 ^ (prefixWord ++ tailWord_7999501).sum := by decide
  have hdescent : baseEnd_7999501 < baseStart_7999501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999524 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_7999524 : Nat := 118140960795 + 7999524 * 2 ^ 59
def prefixEnd_7999524 : Nat := 4983230072969 + 3 ^ 40 * 7999524 * 2
def baseEnd_7999524 : Nat := 1369200273059088353086955

theorem tailTrace_7999524 : CollatzResearch.WordTrace tailWord_7999524 prefixEnd_7999524 1369200273059088353086955 := by
  unfold tailWord_7999524
  simp only [CollatzResearch.WordTrace]
  refine ⟨145883304935549116387390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194511073247398821849854417 145883304935549116387390813)
  ·
    refine ⟨54706239350830918645271555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145883304935549116387390813 54706239350830918645271555)
    ·
      refine ⟨82059359026246377967907333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54706239350830918645271555 82059359026246377967907333)
      ·
        refine ⟨15386129817421195868982625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82059359026246377967907333 15386129817421195868982625)
        ·
          refine ⟨11539597363065896901736969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386129817421195868982625 11539597363065896901736969)
          ·
            refine ⟨8654698022299422676302727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11539597363065896901736969 8654698022299422676302727)
            ·
              refine ⟨12982047033449134014454091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654698022299422676302727 12982047033449134014454091)
              ·
                refine ⟨19473070550173701021681137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982047033449134014454091 19473070550173701021681137)
                ·
                  refine ⟨14604802912630275766260853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19473070550173701021681137 14604802912630275766260853)
                  ·
                    refine ⟨1369200273059088353086955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14604802912630275766260853 1369200273059088353086955)
                    ·
                      rfl

theorem cell23_7999524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_7999524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999524 prefixEnd_7999524 := by exact prefixLift 7999524
  have htrace : WordTrace (prefixWord ++ tailWord_7999524) baseStart_7999524 baseEnd_7999524 := by
    simpa [prefixWord, tailWord_7999524, baseEnd_7999524] using wordTrace_append hprefix tailTrace_7999524
  have hstable : (prefixWord ++ tailWord_7999524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999524).length < 2 ^ (prefixWord ++ tailWord_7999524).sum := by decide
  have hdescent : baseEnd_7999524 < baseStart_7999524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999577 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_7999577 : Nat := 118140960795 + 7999577 * 2 ^ 59
def prefixEnd_7999577 : Nat := 4983230072969 + 3 ^ 40 * 7999577 * 2
def baseEnd_7999577 : Nat := 4107628033651953351898121

theorem tailTrace_7999577 : CollatzResearch.WordTrace tailWord_7999577 prefixEnd_7999577 4107628033651953351898121 := by
  unfold tailWord_7999577
  simp only [CollatzResearch.WordTrace]
  refine ⟨291768542939906222826460985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194512361959937481884307323 291768542939906222826460985)
  ·
    refine ⟨218826407204929667119845739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291768542939906222826460985 218826407204929667119845739)
    ·
      refine ⟨328239610807394500679768609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218826407204929667119845739 328239610807394500679768609)
      ·
        refine ⟨246179708105545875509826457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328239610807394500679768609 246179708105545875509826457)
        ·
          refine ⟨184634781079159406632369843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246179708105545875509826457 184634781079159406632369843)
          ·
            refine ⟨276952171618739109948554765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184634781079159406632369843 276952171618739109948554765)
            ·
              refine ⟨103857064357027166230708037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276952171618739109948554765 103857064357027166230708037)
              ·
                refine ⟨19473199566942593668257757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103857064357027166230708037 19473199566942593668257757)
                ·
                  refine ⟨7302449837603472625596659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19473199566942593668257757 7302449837603472625596659)
                  ·
                    refine ⟨10953674756405208938394989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302449837603472625596659 10953674756405208938394989)
                    ·
                      refine ⟨4107628033651953351898121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10953674756405208938394989 4107628033651953351898121)
                      ·
                        rfl

theorem cell23_7999577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_7999577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999577 prefixEnd_7999577 := by exact prefixLift 7999577
  have htrace : WordTrace (prefixWord ++ tailWord_7999577) baseStart_7999577 baseEnd_7999577 := by
    simpa [prefixWord, tailWord_7999577, baseEnd_7999577] using wordTrace_append hprefix tailTrace_7999577
  have hstable : (prefixWord ++ tailWord_7999577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999577).length < 2 ^ (prefixWord ++ tailWord_7999577).sum := by decide
  have hdescent : baseEnd_7999577 < baseStart_7999577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999587 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7999587 : Nat := 118140960795 + 7999587 * 2 ^ 59
def prefixEnd_7999587 : Nat := 4983230072969 + 3 ^ 40 * 7999587 * 2
def baseEnd_7999587 : Nat := 4107633168458498312773075

theorem tailTrace_7999587 : CollatzResearch.WordTrace tailWord_7999587 prefixEnd_7999587 4107633168458498312773075 := by
  unfold tailWord_7999587
  simp only [CollatzResearch.WordTrace]
  refine ⟨291768907669869994534325015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194512605113246663022883343 291768907669869994534325015)
  ·
    refine ⟨437653361504804991801487523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291768907669869994534325015 437653361504804991801487523)
    ·
      refine ⟨656480042257207487702231285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437653361504804991801487523 656480042257207487702231285)
      ·
        refine ⟨61545003961613201972084183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656480042257207487702231285 61545003961613201972084183)
        ·
          refine ⟨92317505942419802958126275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61545003961613201972084183 92317505942419802958126275)
          ·
            refine ⟨138476258913629704437189413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92317505942419802958126275 138476258913629704437189413)
            ·
              refine ⟨25964298546305569581973015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138476258913629704437189413 25964298546305569581973015)
              ·
                refine ⟨38946447819458354372959523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25964298546305569581973015 38946447819458354372959523)
                ·
                  refine ⟨58419671729187531559439285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38946447819458354372959523 58419671729187531559439285)
                  ·
                    refine ⟨5476844224611331083697433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58419671729187531559439285 5476844224611331083697433)
                    ·
                      refine ⟨4107633168458498312773075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476844224611331083697433 4107633168458498312773075)
                      ·
                        rfl

theorem cell23_7999587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7999587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999587 prefixEnd_7999587 := by exact prefixLift 7999587
  have htrace : WordTrace (prefixWord ++ tailWord_7999587) baseStart_7999587 baseEnd_7999587 := by
    simpa [prefixWord, tailWord_7999587, baseEnd_7999587] using wordTrace_append hprefix tailTrace_7999587
  have hstable : (prefixWord ++ tailWord_7999587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999587).length < 2 ^ (prefixWord ++ tailWord_7999587).sum := by decide
  have hdescent : baseEnd_7999587 < baseStart_7999587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999597 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7999597 : Nat := 118140960795 + 7999597 * 2 ^ 59
def prefixEnd_7999597 : Nat := 4983230072969 + 3 ^ 40 * 7999597 * 2
def baseEnd_7999597 : Nat := 1369212767755014424549343

theorem tailTrace_7999597 : CollatzResearch.WordTrace tailWord_7999597 prefixEnd_7999597 1369212767755014424549343 := by
  unfold tailWord_7999597
  simp only [CollatzResearch.WordTrace]
  refine ⟨291769272399833766242189045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194512848266555844161459363 291769272399833766242189045)
  ·
    refine ⟨27353369287484415585205223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291769272399833766242189045 27353369287484415585205223)
    ·
      refine ⟨41030053931226623377807835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27353369287484415585205223 41030053931226623377807835)
      ·
        refine ⟨61545080896839935066711753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41030053931226623377807835 61545080896839935066711753)
        ·
          refine ⟨46158810672629951300033815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61545080896839935066711753 46158810672629951300033815)
          ·
            refine ⟨69238216008944926950050723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46158810672629951300033815 69238216008944926950050723)
            ·
              refine ⟨103857324013417390425076085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69238216008944926950050723 103857324013417390425076085)
              ·
                refine ⟨9736624126257880352350883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103857324013417390425076085 9736624126257880352350883)
                ·
                  refine ⟨14604936189386820528526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9736624126257880352350883 14604936189386820528526325)
                  ·
                    refine ⟨1369212767755014424549343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14604936189386820528526325 1369212767755014424549343)
                    ·
                      rfl

theorem cell23_7999597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7999597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999597 prefixEnd_7999597 := by exact prefixLift 7999597
  have htrace : WordTrace (prefixWord ++ tailWord_7999597) baseStart_7999597 baseEnd_7999597 := by
    simpa [prefixWord, tailWord_7999597, baseEnd_7999597] using wordTrace_append hprefix tailTrace_7999597
  have hstable : (prefixWord ++ tailWord_7999597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999597).length < 2 ^ (prefixWord ++ tailWord_7999597).sum := by decide
  have hdescent : baseEnd_7999597 < baseStart_7999597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999637 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_7999637 : Nat := 118140960795 + 7999637 * 2 ^ 59
def prefixEnd_7999637 : Nat := 4983230072969 + 3 ^ 40 * 7999637 * 2
def baseEnd_7999637 : Nat := 4107658842491223117147845

theorem tailTrace_7999637 : CollatzResearch.WordTrace tailWord_7999637 prefixEnd_7999637 4107658842491223117147845 := by
  unfold tailWord_7999637
  simp only [CollatzResearch.WordTrace]
  refine ⟨291770731319688853073645165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194513820879792568715763443 291770731319688853073645165)
  ·
    refine ⟨109414024244883319902616937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291770731319688853073645165 109414024244883319902616937)
    ·
      refine ⟨82060518183662489926962703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109414024244883319902616937 82060518183662489926962703)
      ·
        refine ⟨123090777275493734890444055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82060518183662489926962703 123090777275493734890444055)
        ·
          refine ⟨184636165913240602335666083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123090777275493734890444055 184636165913240602335666083)
          ·
            refine ⟨276954248869860903503499125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184636165913240602335666083 276954248869860903503499125)
            ·
              refine ⟨25964460831549459703453043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276954248869860903503499125 25964460831549459703453043)
              ·
                refine ⟨38946691247324189555179565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25964460831549459703453043 38946691247324189555179565)
                ·
                  refine ⟨14605009217746571083192337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38946691247324189555179565 14605009217746571083192337)
                  ·
                    refine ⟨10953756913309928312394253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14605009217746571083192337 10953756913309928312394253)
                    ·
                      refine ⟨4107658842491223117147845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10953756913309928312394253 4107658842491223117147845)
                      ·
                        rfl

theorem cell23_7999637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_7999637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999637 prefixEnd_7999637 := by exact prefixLift 7999637
  have htrace : WordTrace (prefixWord ++ tailWord_7999637) baseStart_7999637 baseEnd_7999637 := by
    simpa [prefixWord, tailWord_7999637, baseEnd_7999637] using wordTrace_append hprefix tailTrace_7999637
  have hstable : (prefixWord ++ tailWord_7999637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999637).length < 2 ^ (prefixWord ++ tailWord_7999637).sum := by decide
  have hdescent : baseEnd_7999637 < baseStart_7999637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999647 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7999647 : Nat := 118140960795 + 7999647 * 2 ^ 59
def prefixEnd_7999647 : Nat := 4983230072969 + 3 ^ 40 * 7999647 * 2
def baseEnd_7999647 : Nat := 4107663977297768078022799

theorem tailTrace_7999647 : CollatzResearch.WordTrace tailWord_7999647 prefixEnd_7999647 4107663977297768078022799 := by
  unfold tailWord_7999647
  simp only [CollatzResearch.WordTrace]
  refine ⟨291771096049652624781509195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194514064033101749854339463 291771096049652624781509195)
  ·
    refine ⟨437656644074478937172263793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291771096049652624781509195 437656644074478937172263793)
    ·
      refine ⟨328242483055859202879197845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437656644074478937172263793 328242483055859202879197845)
      ·
        refine ⟨15386366393243400134962399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 328242483055859202879197845 15386366393243400134962399)
        ·
          refine ⟨23079549589865100202443599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15386366393243400134962399 23079549589865100202443599)
          ·
            refine ⟨34619324384797650303665399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079549589865100202443599 34619324384797650303665399)
            ·
              refine ⟨51928986577196475455498099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34619324384797650303665399 51928986577196475455498099)
              ·
                refine ⟨77893479865794713183247149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51928986577196475455498099 77893479865794713183247149)
                ·
                  refine ⟨29210054949673017443717681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77893479865794713183247149 29210054949673017443717681)
                  ·
                    refine ⟨21907541212254763082788261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29210054949673017443717681 21907541212254763082788261)
                    ·
                      refine ⟨4107663977297768078022799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21907541212254763082788261 4107663977297768078022799)
                      ·
                        rfl

theorem cell23_7999647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7999647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999647 prefixEnd_7999647 := by exact prefixLift 7999647
  have htrace : WordTrace (prefixWord ++ tailWord_7999647) baseStart_7999647 baseEnd_7999647 := by
    simpa [prefixWord, tailWord_7999647, baseEnd_7999647] using wordTrace_append hprefix tailTrace_7999647
  have hstable : (prefixWord ++ tailWord_7999647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999647).length < 2 ^ (prefixWord ++ tailWord_7999647).sum := by decide
  have hdescent : baseEnd_7999647 < baseStart_7999647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999661 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7999661 : Nat := 118140960795 + 7999661 * 2 ^ 59
def prefixEnd_7999661 : Nat := 4983230072969 + 3 ^ 40 * 7999661 * 2
def baseEnd_7999661 : Nat := 1369223722008977007749245

theorem tailTrace_7999661 : CollatzResearch.WordTrace tailWord_7999661 prefixEnd_7999661 1369223722008977007749245 := by
  unfold tailWord_7999661
  simp only [CollatzResearch.WordTrace]
  refine ⟨291771606671601905172518837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194514404447734603448345891 291771606671601905172518837)
  ·
    refine ⟨27353588125462678609923641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291771606671601905172518837 27353588125462678609923641)
    ·
      refine ⟨20515191094097008957442731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27353588125462678609923641 20515191094097008957442731)
      ·
        refine ⟨30772786641145513436164097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20515191094097008957442731 30772786641145513436164097)
        ·
          refine ⟨23079589980859135077123073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30772786641145513436164097 23079589980859135077123073)
          ·
            refine ⟨17309692485644351307842305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23079589980859135077123073 17309692485644351307842305)
            ·
              refine ⟨12982269364233263480881729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309692485644351307842305 12982269364233263480881729)
              ·
                refine ⟨9736702023174947610661297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982269364233263480881729 9736702023174947610661297)
                ·
                  refine ⟨7302526517381210707995973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736702023174947610661297 7302526517381210707995973)
                  ·
                    refine ⟨1369223722008977007749245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302526517381210707995973 1369223722008977007749245)
                    ·
                      rfl

theorem cell23_7999661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7999661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999661 prefixEnd_7999661 := by exact prefixLift 7999661
  have htrace : WordTrace (prefixWord ++ tailWord_7999661) baseStart_7999661 baseEnd_7999661 := by
    simpa [prefixWord, tailWord_7999661, baseEnd_7999661] using wordTrace_append hprefix tailTrace_7999661
  have hstable : (prefixWord ++ tailWord_7999661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999661).length < 2 ^ (prefixWord ++ tailWord_7999661).sum := by decide
  have hdescent : baseEnd_7999661 < baseStart_7999661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999681 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7999681 : Nat := 118140960795 + 7999681 * 2 ^ 59
def prefixEnd_7999681 : Nat := 4983230072969 + 3 ^ 40 * 7999681 * 2
def baseEnd_7999681 : Nat := 4107681435640020944997643

theorem tailTrace_7999681 : CollatzResearch.WordTrace tailWord_7999681 prefixEnd_7999681 4107681435640020944997643 := by
  unfold tailWord_7999681
  simp only [CollatzResearch.WordTrace]
  refine ⟨291772336131529448588246897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194514890754352965725497931 291772336131529448588246897)
  ·
    refine ⟨218829252098647086441185173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291772336131529448588246897 218829252098647086441185173)
    ·
      refine ⟨10257621192124082176930555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218829252098647086441185173 10257621192124082176930555)
      ·
        refine ⟨15386431788186123265395833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257621192124082176930555 15386431788186123265395833)
        ·
          refine ⟨11539823841139592449046875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386431788186123265395833 11539823841139592449046875)
          ·
            refine ⟨17309735761709388673570313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539823841139592449046875 17309735761709388673570313)
            ·
              refine ⟨12982301821282041505177735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309735761709388673570313 12982301821282041505177735)
              ·
                refine ⟨19473452731923062257766603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982301821282041505177735 19473452731923062257766603)
                ·
                  refine ⟨29210179097884593386649905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19473452731923062257766603 29210179097884593386649905)
                  ·
                    refine ⟨21907634323413445039987429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29210179097884593386649905 21907634323413445039987429)
                    ·
                      refine ⟨4107681435640020944997643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21907634323413445039987429 4107681435640020944997643)
                      ·
                        rfl

theorem cell23_7999681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7999681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999681 prefixEnd_7999681 := by exact prefixLift 7999681
  have htrace : WordTrace (prefixWord ++ tailWord_7999681) baseStart_7999681 baseEnd_7999681 := by
    simpa [prefixWord, tailWord_7999681, baseEnd_7999681] using wordTrace_append hprefix tailTrace_7999681
  have hstable : (prefixWord ++ tailWord_7999681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999681).length < 2 ^ (prefixWord ++ tailWord_7999681).sum := by decide
  have hdescent : baseEnd_7999681 < baseStart_7999681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999684 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7999684 : Nat := 118140960795 + 7999684 * 2 ^ 59
def prefixEnd_7999684 : Nat := 4983230072969 + 3 ^ 40 * 7999684 * 2
def baseEnd_7999684 : Nat := 4107682976081984433260129

theorem tailTrace_7999684 : CollatzResearch.WordTrace tailWord_7999684 prefixEnd_7999684 4107682976081984433260129 := by
  unfold tailWord_7999684
  simp only [CollatzResearch.WordTrace]
  refine ⟨145886222775259290050303053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194514963700345720067070737 145886222775259290050303053)
  ·
    refine ⟨54707333540722233768863645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145886222775259290050303053 54707333540722233768863645)
    ·
      refine ⟨20515250077770837663323867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54707333540722233768863645 20515250077770837663323867)
      ·
        refine ⟨30772875116656256494985801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20515250077770837663323867 30772875116656256494985801)
        ·
          refine ⟨23079656337492192371239351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30772875116656256494985801 23079656337492192371239351)
          ·
            refine ⟨34619484506238288556859027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079656337492192371239351 34619484506238288556859027)
            ·
              refine ⟨51929226759357432835288541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34619484506238288556859027 51929226759357432835288541)
              ·
                refine ⟨19473460034759037313233203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51929226759357432835288541 19473460034759037313233203)
                ·
                  refine ⟨29210190052138555969849805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19473460034759037313233203 29210190052138555969849805)
                  ·
                    refine ⟨10953821269551958488693677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29210190052138555969849805 10953821269551958488693677)
                    ·
                      refine ⟨4107682976081984433260129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10953821269551958488693677 4107682976081984433260129)
                      ·
                        rfl

theorem cell23_7999684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7999684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999684 prefixEnd_7999684 := by exact prefixLift 7999684
  have htrace : WordTrace (prefixWord ++ tailWord_7999684) baseStart_7999684 baseEnd_7999684 := by
    simpa [prefixWord, tailWord_7999684, baseEnd_7999684] using wordTrace_append hprefix tailTrace_7999684
  have hstable : (prefixWord ++ tailWord_7999684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999684).length < 2 ^ (prefixWord ++ tailWord_7999684).sum := by decide
  have hdescent : baseEnd_7999684 < baseStart_7999684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999702 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7999702 : Nat := 118140960795 + 7999702 * 2 ^ 59
def prefixEnd_7999702 : Nat := 4983230072969 + 3 ^ 40 * 7999702 * 2
def baseEnd_7999702 : Nat := 4107692218733765362835047

theorem tailTrace_7999702 : CollatzResearch.WordTrace tailWord_7999702 prefixEnd_7999702 4107692218733765362835047 := by
  unfold tailWord_7999702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235818879028335573422585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194515401376302246116507573 18235818879028335573422585)
  ·
    refine ⟨13676864159271251680066939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18235818879028335573422585 13676864159271251680066939)
    ·
      refine ⟨20515296238906877520100409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13676864159271251680066939 20515296238906877520100409)
      ·
        refine ⟨15386472179180158140075307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20515296238906877520100409 15386472179180158140075307)
        ·
          refine ⟨23079708268770237210112961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15386472179180158140075307 23079708268770237210112961)
          ·
            refine ⟨17309781201577677907584721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23079708268770237210112961 17309781201577677907584721)
            ·
              refine ⟨12982335901183258430688541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309781201577677907584721 12982335901183258430688541)
              ·
                refine ⟨4868375962943721911508203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12982335901183258430688541 4868375962943721911508203)
                ·
                  refine ⟨7302563944415582867262305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868375962943721911508203 7302563944415582867262305)
                  ·
                    refine ⟨5476922958311687150446729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302563944415582867262305 5476922958311687150446729)
                    ·
                      refine ⟨4107692218733765362835047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476922958311687150446729 4107692218733765362835047)
                      ·
                        rfl

theorem cell23_7999702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7999702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999702 prefixEnd_7999702 := by exact prefixLift 7999702
  have htrace : WordTrace (prefixWord ++ tailWord_7999702) baseStart_7999702 baseEnd_7999702 := by
    simpa [prefixWord, tailWord_7999702, baseEnd_7999702] using wordTrace_append hprefix tailTrace_7999702
  have hstable : (prefixWord ++ tailWord_7999702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999702).length < 2 ^ (prefixWord ++ tailWord_7999702).sum := by decide
  have hdescent : baseEnd_7999702 < baseStart_7999702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999717 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_7999717 : Nat := 118140960795 + 7999717 * 2 ^ 59
def prefixEnd_7999717 : Nat := 4983230072969 + 3 ^ 40 * 7999717 * 2
def baseEnd_7999717 : Nat := 1369233306981194268049159

theorem tailTrace_7999717 : CollatzResearch.WordTrace tailWord_7999717 prefixEnd_7999717 1369233306981194268049159 := by
  unfold tailWord_7999717
  simp only [CollatzResearch.WordTrace]
  refine ⟨291773649159399026736557405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194515766106266017824371603 291773649159399026736557405)
  ·
    refine ⟨109415118434774635026209027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291773649159399026736557405 109415118434774635026209027)
    ·
      refine ⟨164122677652161952539313541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109415118434774635026209027 164122677652161952539313541)
      ·
        refine ⟨30773002059780366101121289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164122677652161952539313541 30773002059780366101121289)
        ·
          refine ⟨23079751544835274575840967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30773002059780366101121289 23079751544835274575840967)
          ·
            refine ⟨34619627317252911863761451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079751544835274575840967 34619627317252911863761451)
            ·
              refine ⟨51929440975879367795642177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34619627317252911863761451 51929440975879367795642177)
              ·
                refine ⟨38947080731909525846731633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51929440975879367795642177 38947080731909525846731633)
                ·
                  refine ⟨29210310548932144385048725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38947080731909525846731633 29210310548932144385048725)
                  ·
                    refine ⟨1369233306981194268049159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29210310548932144385048725 1369233306981194268049159)
                    ·
                      rfl

theorem cell23_7999717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_7999717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999717 prefixEnd_7999717 := by exact prefixLift 7999717
  have htrace : WordTrace (prefixWord ++ tailWord_7999717) baseStart_7999717 baseEnd_7999717 := by
    simpa [prefixWord, tailWord_7999717, baseEnd_7999717] using wordTrace_append hprefix tailTrace_7999717
  have hstable : (prefixWord ++ tailWord_7999717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999717).length < 2 ^ (prefixWord ++ tailWord_7999717).sum := by decide
  have hdescent : baseEnd_7999717 < baseStart_7999717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999741 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_7999741 : Nat := 118140960795 + 7999741 * 2 ^ 59
def prefixEnd_7999741 : Nat := 4983230072969 + 3 ^ 40 * 7999741 * 2
def baseEnd_7999741 : Nat := 4107712244479290710247367

theorem tailTrace_7999741 : CollatzResearch.WordTrace tailWord_7999741 prefixEnd_7999741 4107712244479290710247367 := by
  unfold tailWord_7999741
  simp only [CollatzResearch.WordTrace]
  refine ⟨291774524511312078835431077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194516349674208052556954051 291774524511312078835431077)
  ·
    refine ⟨54707723345871014781643327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291774524511312078835431077 54707723345871014781643327)
    ·
      refine ⟨82061585018806522172464991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54707723345871014781643327 82061585018806522172464991)
      ·
        refine ⟨123092377528209783258697487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82061585018806522172464991 123092377528209783258697487)
        ·
          refine ⟨184638566292314674888046231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123092377528209783258697487 184638566292314674888046231)
          ·
            refine ⟨276957849438472012332069347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184638566292314674888046231 276957849438472012332069347)
            ·
              refine ⟨415436774157708018498104021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276957849438472012332069347 415436774157708018498104021)
              ·
                refine ⟨9736799394321281683549313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 415436774157708018498104021 9736799394321281683549313)
                ·
                  refine ⟨7302599545740961262661985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736799394321281683549313 7302599545740961262661985)
                  ·
                    refine ⟨5476949659305720946996489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302599545740961262661985 5476949659305720946996489)
                    ·
                      refine ⟨4107712244479290710247367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5476949659305720946996489 4107712244479290710247367)
                      ·
                        rfl

theorem cell23_7999741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_7999741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999741 prefixEnd_7999741 := by exact prefixLift 7999741
  have htrace : WordTrace (prefixWord ++ tailWord_7999741) baseStart_7999741 baseEnd_7999741 := by
    simpa [prefixWord, tailWord_7999741, baseEnd_7999741] using wordTrace_append hprefix tailTrace_7999741
  have hstable : (prefixWord ++ tailWord_7999741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999741).length < 2 ^ (prefixWord ++ tailWord_7999741).sum := by decide
  have hdescent : baseEnd_7999741 < baseStart_7999741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999777 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_7999777 : Nat := 118140960795 + 7999777 * 2 ^ 59
def prefixEnd_7999777 : Nat := 4983230072969 + 3 ^ 40 * 7999777 * 2
def baseEnd_7999777 : Nat := 1369243576594284189799067

theorem tailTrace_7999777 : CollatzResearch.WordTrace tailWord_7999777 prefixEnd_7999777 1369243576594284189799067 := by
  unfold tailWord_7999777
  simp only [CollatzResearch.WordTrace]
  refine ⟨291775837539181656983741585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194517225026121104655827723 291775837539181656983741585)
  ·
    refine ⟨218831878154386242737806189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291775837539181656983741585 218831878154386242737806189)
    ·
      refine ⟨82061954307894841026677321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218831878154386242737806189 82061954307894841026677321)
      ·
        refine ⟨61546465730921130770007991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82061954307894841026677321 61546465730921130770007991)
        ·
          refine ⟨92319698596381696155011987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61546465730921130770007991 92319698596381696155011987)
          ·
            refine ⟨138479547894572544232517981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92319698596381696155011987 138479547894572544232517981)
            ·
              refine ⟨51929830460464704087194243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138479547894572544232517981 51929830460464704087194243)
              ·
                refine ⟨77894745690697056130791365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51929830460464704087194243 77894745690697056130791365)
                ·
                  refine ⟨14605264817005698024523381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77894745690697056130791365 14605264817005698024523381)
                  ·
                    refine ⟨1369243576594284189799067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14605264817005698024523381 1369243576594284189799067)
                    ·
                      rfl

theorem cell23_7999777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7999777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999777 prefixEnd_7999777 := by exact prefixLift 7999777
  have htrace : WordTrace (prefixWord ++ tailWord_7999777) baseStart_7999777 baseEnd_7999777 := by
    simpa [prefixWord, tailWord_7999777, baseEnd_7999777] using wordTrace_append hprefix tailTrace_7999777
  have hstable : (prefixWord ++ tailWord_7999777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999777).length < 2 ^ (prefixWord ++ tailWord_7999777).sum := by decide
  have hdescent : baseEnd_7999777 < baseStart_7999777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999781 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 7]
def baseStart_7999781 : Nat := 118140960795 + 7999781 * 2 ^ 59
def prefixEnd_7999781 : Nat := 4983230072969 + 3 ^ 40 * 7999781 * 2
def baseEnd_7999781 : Nat := 456414753745052283749687

theorem tailTrace_7999781 : CollatzResearch.WordTrace tailWord_7999781 prefixEnd_7999781 456414753745052283749687 := by
  unfold tailWord_7999781
  simp only [CollatzResearch.WordTrace]
  refine ⟨291775983431167165666887197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194517322287444777111258131 291775983431167165666887197)
  ·
    refine ⟨109415993786687687125082699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291775983431167165666887197 109415993786687687125082699)
    ·
      refine ⟨164123990680031530687624049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109415993786687687125082699 164123990680031530687624049)
      ·
        refine ⟨123092993010023648015718037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164123990680031530687624049 123092993010023648015718037)
        ·
          refine ⟨5769984047344858500736783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123092993010023648015718037 5769984047344858500736783)
          ·
            refine ⟨8654976071017287751105175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769984047344858500736783 8654976071017287751105175)
            ·
              refine ⟨12982464106525931626657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654976071017287751105175 12982464106525931626657763)
              ·
                refine ⟨19473696159788897439986645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982464106525931626657763 19473696159788897439986645)
                ·
                  refine ⟨456414753745052283749687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19473696159788897439986645 456414753745052283749687)
                  ·
                    rfl

theorem cell23_7999781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_7999781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999781 prefixEnd_7999781 := by exact prefixLift 7999781
  have htrace : WordTrace (prefixWord ++ tailWord_7999781) baseStart_7999781 baseEnd_7999781 := by
    simpa [prefixWord, tailWord_7999781, baseEnd_7999781] using wordTrace_append hprefix tailTrace_7999781
  have hstable : (prefixWord ++ tailWord_7999781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999781).length < 2 ^ (prefixWord ++ tailWord_7999781).sum := by decide
  have hdescent : baseEnd_7999781 < baseStart_7999781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999877 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_7999877 : Nat := 118140960795 + 7999877 * 2 ^ 59
def prefixEnd_7999877 : Nat := 4983230072969 + 3 ^ 40 * 7999877 * 2
def baseEnd_7999877 : Nat := 4107782077848302178146741

theorem tailTrace_7999877 : CollatzResearch.WordTrace tailWord_7999877 prefixEnd_7999877 4107782077848302178146741 := by
  unfold tailWord_7999877
  simp only [CollatzResearch.WordTrace]
  refine ⟨291779484838819374062381885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194519656559212916041587923 291779484838819374062381885)
  ·
    refine ⟨109417306814557265273393207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291779484838819374062381885 109417306814557265273393207)
    ·
      refine ⟨164125960221835897910089811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109417306814557265273393207 164125960221835897910089811)
      ·
        refine ⟨246188940332753846865134717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164125960221835897910089811 246188940332753846865134717)
        ·
          refine ⟨92320852624782692574425519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246188940332753846865134717 92320852624782692574425519)
          ·
            refine ⟨138481278937174038861638279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92320852624782692574425519 138481278937174038861638279)
            ·
              refine ⟨207721918405761058292457419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138481278937174038861638279 207721918405761058292457419)
              ·
                refine ⟨311582877608641587438686129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207721918405761058292457419 311582877608641587438686129)
                ·
                  refine ⟨233687158206481190579014597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311582877608641587438686129 233687158206481190579014597)
                  ·
                    refine ⟨43816342163715223233565237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233687158206481190579014597 43816342163715223233565237)
                    ·
                      refine ⟨4107782077848302178146741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43816342163715223233565237 4107782077848302178146741)
                      ·
                        rfl

theorem cell23_7999877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_7999877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999877 prefixEnd_7999877 := by exact prefixLift 7999877
  have htrace : WordTrace (prefixWord ++ tailWord_7999877) baseStart_7999877 baseEnd_7999877 := by
    simpa [prefixWord, tailWord_7999877, baseEnd_7999877] using wordTrace_append hprefix tailTrace_7999877
  have hstable : (prefixWord ++ tailWord_7999877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999877).length < 2 ^ (prefixWord ++ tailWord_7999877).sum := by decide
  have hdescent : baseEnd_7999877 < baseStart_7999877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999898 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7999898 : Nat := 118140960795 + 7999898 * 2 ^ 59
def prefixEnd_7999898 : Nat := 4983230072969 + 3 ^ 40 * 7999898 * 2
def baseEnd_7999898 : Nat := 4107792860942046595984145

theorem tailTrace_7999898 : CollatzResearch.WordTrace tailWord_7999898 prefixEnd_7999898 4107792860942046595984145 := by
  unfold tailWord_7999898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945062692935823662224087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194520167181162196432597565 72945062692935823662224087)
  ·
    refine ⟨109417594039403735493336131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72945062692935823662224087 109417594039403735493336131)
    ·
      refine ⟨164126391059105603240004197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109417594039403735493336131 164126391059105603240004197)
      ·
        refine ⟨30773698323582300607500787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164126391059105603240004197 30773698323582300607500787)
        ·
          refine ⟨46160547485373450911251181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30773698323582300607500787 46160547485373450911251181)
          ·
            refine ⟨17310205307015044091719193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46160547485373450911251181 17310205307015044091719193)
            ·
              refine ⟨12982653980261283068789395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310205307015044091719193 12982653980261283068789395)
              ·
                refine ⟨19473980970391924603184093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982653980261283068789395 19473980970391924603184093)
                ·
                  refine ⟨7302742863896971726194035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19473980970391924603184093 7302742863896971726194035)
                  ·
                    refine ⟨10954114295845457589291053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302742863896971726194035 10954114295845457589291053)
                    ·
                      refine ⟨4107792860942046595984145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10954114295845457589291053 4107792860942046595984145)
                      ·
                        rfl

theorem cell23_7999898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7999898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999898 prefixEnd_7999898 := by exact prefixLift 7999898
  have htrace : WordTrace (prefixWord ++ tailWord_7999898) baseStart_7999898 baseEnd_7999898 := by
    simpa [prefixWord, tailWord_7999898, baseEnd_7999898] using wordTrace_append hprefix tailTrace_7999898
  have hstable : (prefixWord ++ tailWord_7999898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999898).length < 2 ^ (prefixWord ++ tailWord_7999898).sum := by decide
  have hdescent : baseEnd_7999898 < baseStart_7999898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999921 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_7999921 : Nat := 118140960795 + 7999921 * 2 ^ 59
def prefixEnd_7999921 : Nat := 4983230072969 + 3 ^ 40 * 7999921 * 2
def baseEnd_7999921 : Nat := 4107804670997100005996539

theorem tailTrace_7999921 : CollatzResearch.WordTrace tailWord_7999921 prefixEnd_7999921 4107804670997100005996539 := by
  unfold tailWord_7999921
  simp only [CollatzResearch.WordTrace]
  refine ⟨291781089650659969576983617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194520726433773313051322411 291781089650659969576983617)
  ·
    refine ⟨218835817237994977182737713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291781089650659969576983617 218835817237994977182737713)
    ·
      refine ⟨164126862928496232887053285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218835817237994977182737713 164126862928496232887053285)
      ·
        refine ⟨30773786799093043666322491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164126862928496232887053285 30773786799093043666322491)
        ·
          refine ⟨46160680198639565499483737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30773786799093043666322491 46160680198639565499483737)
          ·
            refine ⟨34620510148979674124612803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46160680198639565499483737 34620510148979674124612803)
            ·
              refine ⟨51930765223469511186919205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34620510148979674124612803 51930765223469511186919205)
              ·
                refine ⟨9737018479400533347547351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51930765223469511186919205 9737018479400533347547351)
                ·
                  refine ⟨14605527719100800021321027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737018479400533347547351 14605527719100800021321027)
                  ·
                    refine ⟨21908291578651200031981541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14605527719100800021321027 21908291578651200031981541)
                    ·
                      refine ⟨4107804670997100005996539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21908291578651200031981541 4107804670997100005996539)
                      ·
                        rfl

theorem cell23_7999921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_7999921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999921 prefixEnd_7999921 := by exact prefixLift 7999921
  have htrace : WordTrace (prefixWord ++ tailWord_7999921) baseStart_7999921 baseEnd_7999921 := by
    simpa [prefixWord, tailWord_7999921, baseEnd_7999921] using wordTrace_append hprefix tailTrace_7999921
  have hstable : (prefixWord ++ tailWord_7999921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999921).length < 2 ^ (prefixWord ++ tailWord_7999921).sum := by decide
  have hdescent : baseEnd_7999921 < baseStart_7999921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999932 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7999932 : Nat := 118140960795 + 7999932 * 2 ^ 59
def prefixEnd_7999932 : Nat := 4983230072969 + 3 ^ 40 * 7999932 * 2
def baseEnd_7999932 : Nat := 4107810319284299462958989

theorem tailTrace_7999932 : CollatzResearch.WordTrace tailWord_7999932 prefixEnd_7999932 4107810319284299462958989 := by
  unfold tailWord_7999932
  simp only [CollatzResearch.WordTrace]
  refine ⟨145890745426810059227817025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194520993902413412303756033 145890745426810059227817025)
  ·
    refine ⟨109418059070107544420862769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145890745426810059227817025 109418059070107544420862769)
    ·
      refine ⟨82063544302580658315647077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109418059070107544420862769 82063544302580658315647077)
      ·
        refine ⟨15386914556733873434183827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82063544302580658315647077 15386914556733873434183827)
        ·
          refine ⟨23080371835100810151275741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15386914556733873434183827 23080371835100810151275741)
          ·
            refine ⟨8655139438162803806728403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23080371835100810151275741 8655139438162803806728403)
            ·
              refine ⟨12982709157244205710092605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655139438162803806728403 12982709157244205710092605)
              ·
                refine ⟨4868515933966577141284727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12982709157244205710092605 4868515933966577141284727)
                ·
                  refine ⟨7302773900949865711927091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868515933966577141284727 7302773900949865711927091)
                  ·
                    refine ⟨10954160851424798567890637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302773900949865711927091 10954160851424798567890637)
                    ·
                      refine ⟨4107810319284299462958989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10954160851424798567890637 4107810319284299462958989)
                      ·
                        rfl

theorem cell23_7999932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7999932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999932 prefixEnd_7999932 := by exact prefixLift 7999932
  have htrace : WordTrace (prefixWord ++ tailWord_7999932) baseStart_7999932 baseEnd_7999932 := by
    simpa [prefixWord, tailWord_7999932, baseEnd_7999932] using wordTrace_append hprefix tailTrace_7999932
  have hstable : (prefixWord ++ tailWord_7999932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999932).length < 2 ^ (prefixWord ++ tailWord_7999932).sum := by decide
  have hdescent : baseEnd_7999932 < baseStart_7999932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999944 : List Nat := [2, 1, 3, 1, 3, 4, 9]
def baseStart_7999944 : Nat := 118140960795 + 7999944 * 2 ^ 59
def prefixEnd_7999944 : Nat := 4983230072969 + 3 ^ 40 * 7999944 * 2
def baseEnd_7999944 : Nat := 50713783716693252049493

theorem tailTrace_7999944 : CollatzResearch.WordTrace tailWord_7999944 prefixEnd_7999944 50713783716693252049493 := by
  unfold tailWord_7999944
  simp only [CollatzResearch.WordTrace]
  refine ⟨145890964264788322252535443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194521285686384429670047257 145890964264788322252535443)
  ·
    refine ⟨218836446397182483378803165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145890964264788322252535443 218836446397182483378803165)
    ·
      refine ⟨82063667398943431267051187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218836446397182483378803165 82063667398943431267051187)
      ·
        refine ⟨123095501098415146900576781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82063667398943431267051187 123095501098415146900576781)
        ·
          refine ⟨46160812911905680087716293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123095501098415146900576781 46160812911905680087716293)
          ·
            refine ⟨8655152420982315016446805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46160812911905680087716293 8655152420982315016446805)
            ·
              refine ⟨50713783716693252049493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8655152420982315016446805 50713783716693252049493)
              ·
                rfl

theorem cell23_7999944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 9].length) (baseStart_7999944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999944 prefixEnd_7999944 := by exact prefixLift 7999944
  have htrace : WordTrace (prefixWord ++ tailWord_7999944) baseStart_7999944 baseEnd_7999944 := by
    simpa [prefixWord, tailWord_7999944, baseEnd_7999944] using wordTrace_append hprefix tailTrace_7999944
  have hstable : (prefixWord ++ tailWord_7999944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999944).length < 2 ^ (prefixWord ++ tailWord_7999944).sum := by decide
  have hdescent : baseEnd_7999944 < baseStart_7999944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7999958 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7999958 : Nat := 118140960795 + 7999958 * 2 ^ 59
def prefixEnd_7999958 : Nat := 4983230072969 + 3 ^ 40 * 7999958 * 2
def baseEnd_7999958 : Nat := 4107823669781316361233869

theorem tailTrace_7999958 : CollatzResearch.WordTrace tailWord_7999958 prefixEnd_7999958 4107823669781316361233869 := by
  unfold tailWord_7999958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236402446970370306005033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194521626101017283264053685 18236402446970370306005033)
  ·
    refine ⟨13677301835227777729503775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18236402446970370306005033 13677301835227777729503775)
    ·
      refine ⟨20515952752841666594255663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13677301835227777729503775 20515952752841666594255663)
      ·
        refine ⟨30773929129262499891383495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20515952752841666594255663 30773929129262499891383495)
        ·
          refine ⟨46160893693893749837075243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30773929129262499891383495 46160893693893749837075243)
          ·
            refine ⟨69241340540840624755612865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46160893693893749837075243 69241340540840624755612865)
            ·
              refine ⟨51931005405630468566709649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69241340540840624755612865 51931005405630468566709649)
              ·
                refine ⟨38948254054222851425032237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51931005405630468566709649 38948254054222851425032237)
                ·
                  refine ⟨14605595270333569284387089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38948254054222851425032237 14605595270333569284387089)
                  ·
                    refine ⟨10954196452750176963290317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14605595270333569284387089 10954196452750176963290317)
                    ·
                      refine ⟨4107823669781316361233869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10954196452750176963290317 4107823669781316361233869)
                      ·
                        rfl

theorem cell23_7999958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7999958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7999958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7999958 prefixEnd_7999958 := by exact prefixLift 7999958
  have htrace : WordTrace (prefixWord ++ tailWord_7999958) baseStart_7999958 baseEnd_7999958 := by
    simpa [prefixWord, tailWord_7999958, baseEnd_7999958] using wordTrace_append hprefix tailTrace_7999958
  have hstable : (prefixWord ++ tailWord_7999958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7999958).length < 2 ^ (prefixWord ++ tailWord_7999958).sum := by decide
  have hdescent : baseEnd_7999958 < baseStart_7999958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7999958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000028 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_8000028 : Nat := 118140960795 + 8000028 * 2 ^ 59
def prefixEnd_8000028 : Nat := 4983230072969 + 3 ^ 40 * 8000028 * 2
def baseEnd_8000028 : Nat := 4107859613427131087358547

theorem tailTrace_8000028 : CollatzResearch.WordTrace tailWord_8000028 prefixEnd_8000028 4107859613427131087358547 := by
  unfold tailWord_8000028
  simp only [CollatzResearch.WordTrace]
  refine ⟨145892496130636163425564369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194523328174181551234085825 145892496130636163425564369)
  ·
    refine ⟨109419372097977122569173277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145892496130636163425564369 109419372097977122569173277)
    ·
      refine ⟨41032264536741420963439979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109419372097977122569173277 41032264536741420963439979)
      ·
        refine ⟨61548396805112131445159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41032264536741420963439979 61548396805112131445159969)
        ·
          refine ⟨46161297603834098583869977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61548396805112131445159969 46161297603834098583869977)
          ·
            refine ⟨34620973202875573937902483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46161297603834098583869977 34620973202875573937902483)
            ·
              refine ⟨51931459804313360906853725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34620973202875573937902483 51931459804313360906853725)
              ·
                refine ⟨19474297426617510340070147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51931459804313360906853725 19474297426617510340070147)
                ·
                  refine ⟨29211446139926265510105221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19474297426617510340070147 29211446139926265510105221)
                  ·
                    refine ⟨5477146151236174783144729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29211446139926265510105221 5477146151236174783144729)
                    ·
                      refine ⟨4107859613427131087358547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477146151236174783144729 4107859613427131087358547)
                      ·
                        rfl

theorem cell23_8000028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_8000028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000028 prefixEnd_8000028 := by exact prefixLift 8000028
  have htrace : WordTrace (prefixWord ++ tailWord_8000028) baseStart_8000028 baseEnd_8000028 := by
    simpa [prefixWord, tailWord_8000028, baseEnd_8000028] using wordTrace_append hprefix tailTrace_8000028
  have hstable : (prefixWord ++ tailWord_8000028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000028).length < 2 ^ (prefixWord ++ tailWord_8000028).sum := by decide
  have hdescent : baseEnd_8000028 < baseStart_8000028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000111 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 5, 4]
def baseStart_8000111 : Nat := 118140960795 + 8000111 * 2 ^ 59
def prefixEnd_8000111 : Nat := 4983230072969 + 3 ^ 40 * 8000111 * 2
def baseEnd_8000111 : Nat := 1369300744107151420873555

theorem tailTrace_8000111 : CollatzResearch.WordTrace tailWord_8000111 prefixEnd_8000111 1369300744107151420873555 := by
  unfold tailWord_8000111
  simp only [CollatzResearch.WordTrace]
  refine ⟨291788019519971632026400187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194525346346647754684266791 291788019519971632026400187)
  ·
    refine ⟨437682029279957448039600281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291788019519971632026400187 437682029279957448039600281)
    ·
      refine ⟨328261521959968086029700211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437682029279957448039600281 328261521959968086029700211)
      ·
        refine ⟨492392282939952129044550317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328261521959968086029700211 492392282939952129044550317)
        ·
          refine ⟨184647106102482048391706369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492392282939952129044550317 184647106102482048391706369)
          ·
            refine ⟨138485329576861536293779777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184647106102482048391706369 138485329576861536293779777)
            ·
              refine ⟨103863997182646152220334833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138485329576861536293779777 103863997182646152220334833)
              ·
                refine ⟨77897997886984614165251125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103863997182646152220334833 77897997886984614165251125)
                ·
                  refine ⟨7302937301904807577992293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77897997886984614165251125 7302937301904807577992293)
                  ·
                    refine ⟨1369300744107151420873555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302937301904807577992293 1369300744107151420873555)
                    ·
                      rfl

theorem cell23_8000111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_8000111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000111 prefixEnd_8000111 := by exact prefixLift 8000111
  have htrace : WordTrace (prefixWord ++ tailWord_8000111) baseStart_8000111 baseEnd_8000111 := by
    simpa [prefixWord, tailWord_8000111, baseEnd_8000111] using wordTrace_append hprefix tailTrace_8000111
  have hstable : (prefixWord ++ tailWord_8000111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000111).length < 2 ^ (prefixWord ++ tailWord_8000111).sum := by decide
  have hdescent : baseEnd_8000111 < baseStart_8000111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000128 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_8000128 : Nat := 118140960795 + 8000128 * 2 ^ 59
def prefixEnd_8000128 : Nat := 4983230072969 + 3 ^ 40 * 8000128 * 2
def baseEnd_8000128 : Nat := 1369303653830860232036029

theorem tailTrace_8000128 : CollatzResearch.WordTrace tailWord_8000128 prefixEnd_8000128 1369303653830860232036029 := by
  unfold tailWord_8000128
  simp only [CollatzResearch.WordTrace]
  refine ⟨145894319780455021964884519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194525759707273362619846025 145894319780455021964884519)
  ·
    refine ⟨218841479670682532947326779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145894319780455021964884519 218841479670682532947326779)
    ·
      refine ⟨328262219506023799420990169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218841479670682532947326779 328262219506023799420990169)
      ·
        refine ⟨246196664629517849565742627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328262219506023799420990169 246196664629517849565742627)
        ·
          refine ⟨369294996944276774348613941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246196664629517849565742627 369294996944276774348613941)
          ·
            refine ⟨34621405963525947595182557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369294996944276774348613941 34621405963525947595182557)
            ·
              refine ⟨12983027236322230348193459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34621405963525947595182557 12983027236322230348193459)
              ·
                refine ⟨19474540854483345522290189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12983027236322230348193459 19474540854483345522290189)
                ·
                  refine ⟨7302952820431254570858821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19474540854483345522290189 7302952820431254570858821)
                  ·
                    refine ⟨1369303653830860232036029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302952820431254570858821 1369303653830860232036029)
                    ·
                      rfl

theorem cell23_8000128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_8000128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000128 prefixEnd_8000128 := by exact prefixLift 8000128
  have htrace : WordTrace (prefixWord ++ tailWord_8000128) baseStart_8000128 baseEnd_8000128 := by
    simpa [prefixWord, tailWord_8000128, baseEnd_8000128] using wordTrace_append hprefix tailTrace_8000128
  have hstable : (prefixWord ++ tailWord_8000128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000128).length < 2 ^ (prefixWord ++ tailWord_8000128).sum := by decide
  have hdescent : baseEnd_8000128 < baseStart_8000128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000130 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_8000130 : Nat := 118140960795 + 8000130 * 2 ^ 59
def prefixEnd_8000130 : Nat := 4983230072969 + 3 ^ 40 * 8000130 * 2
def baseEnd_8000130 : Nat := 4107911988453889688283079

theorem tailTrace_8000130 : CollatzResearch.WordTrace tailWord_8000130 prefixEnd_8000130 4107911988453889688283079 := by
  unfold tailWord_8000130
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947178126725699567835461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194525808337935198847561229 72947178126725699567835461)
  ·
    refine ⟨13677595898761068668969149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72947178126725699567835461 13677595898761068668969149)
    ·
      refine ⟨5129098462035400750863431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13677595898761068668969149 5129098462035400750863431)
      ·
        refine ⟨7693647693053101126295147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129098462035400750863431 7693647693053101126295147)
        ·
          refine ⟨11540471539579651689442721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693647693053101126295147 11540471539579651689442721)
          ·
            refine ⟨8655353654684738767082041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540471539579651689442721 8655353654684738767082041)
            ·
              refine ⟨6491515241013554075311531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655353654684738767082041 6491515241013554075311531)
              ·
                refine ⟨9737272861520331112967297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491515241013554075311531 9737272861520331112967297)
                ·
                  refine ⟨7302954646140248334725473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737272861520331112967297 7302954646140248334725473)
                  ·
                    refine ⟨5477215984605186251044105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302954646140248334725473 5477215984605186251044105)
                    ·
                      refine ⟨4107911988453889688283079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477215984605186251044105 4107911988453889688283079)
                      ·
                        rfl

theorem cell23_8000130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_8000130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000130 prefixEnd_8000130 := by exact prefixLift 8000130
  have htrace : WordTrace (prefixWord ++ tailWord_8000130) baseStart_8000130 baseEnd_8000130 := by
    simpa [prefixWord, tailWord_8000130, baseEnd_8000130] using wordTrace_append hprefix tailTrace_8000130
  have hstable : (prefixWord ++ tailWord_8000130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000130).length < 2 ^ (prefixWord ++ tailWord_8000130).sum := by decide
  have hdescent : baseEnd_8000130 < baseStart_8000130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000178 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_8000178 : Nat := 118140960795 + 8000178 * 2 ^ 59
def prefixEnd_8000178 : Nat := 4983230072969 + 3 ^ 40 * 8000178 * 2
def baseEnd_8000178 : Nat := 4107936635525305500482857

theorem tailTrace_8000178 : CollatzResearch.WordTrace tailWord_8000178 prefixEnd_8000178 4107936635525305500482857 := by
  unfold tailWord_8000178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947615802682225617272297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194526975473819268312726125 72947615802682225617272297)
  ·
    refine ⟨54710711852011669212954223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72947615802682225617272297 54710711852011669212954223)
    ·
      refine ⟨82066067778017503819431335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54710711852011669212954223 82066067778017503819431335)
      ·
        refine ⟨123099101667026255729147003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82066067778017503819431335 123099101667026255729147003)
        ·
          refine ⟨184648652500539383593720505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123099101667026255729147003 184648652500539383593720505)
          ·
            refine ⟨138486489375404537695290379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184648652500539383593720505 138486489375404537695290379)
            ·
              refine ⟨207729734063106806542935569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138486489375404537695290379 207729734063106806542935569)
              ·
                refine ⟨155797300547330104907201677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207729734063106806542935569 155797300547330104907201677)
                ·
                  refine ⟨58423987705248789340200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155797300547330104907201677 58423987705248789340200629)
                  ·
                    refine ⟨5477248847367074000643809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58423987705248789340200629 5477248847367074000643809)
                    ·
                      refine ⟨4107936635525305500482857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477248847367074000643809 4107936635525305500482857)
                      ·
                        rfl

theorem cell23_8000178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_8000178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000178 prefixEnd_8000178 := by exact prefixLift 8000178
  have htrace : WordTrace (prefixWord ++ tailWord_8000178) baseStart_8000178 baseEnd_8000178 := by
    simpa [prefixWord, tailWord_8000178, baseEnd_8000178] using wordTrace_append hprefix tailTrace_8000178
  have hstable : (prefixWord ++ tailWord_8000178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000178).length < 2 ^ (prefixWord ++ tailWord_8000178).sum := by decide
  have hdescent : baseEnd_8000178 < baseStart_8000178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000212 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8000212 : Nat := 118140960795 + 8000212 * 2 ^ 59
def prefixEnd_8000212 : Nat := 4983230072969 + 3 ^ 40 * 8000212 * 2
def baseEnd_8000212 : Nat := 4107954093867558367457701

theorem tailTrace_8000212 : CollatzResearch.WordTrace tailWord_8000212 prefixEnd_8000212 4107954093867558367457701 := by
  unfold tailWord_8000212
  simp only [CollatzResearch.WordTrace]
  refine ⟨145895851646302863137913445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194527802195070484183884593 145895851646302863137913445)
  ·
    refine ⟨27355472183681786838358771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145895851646302863137913445 27355472183681786838358771)
    ·
      refine ⟨41033208275522680257538157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27355472183681786838358771 41033208275522680257538157)
      ·
        refine ⟨15387453103321005096576809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41033208275522680257538157 15387453103321005096576809)
        ·
          refine ⟨11540589827490753822432607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15387453103321005096576809 11540589827490753822432607)
          ·
            refine ⟨17310884741236130733648911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540589827490753822432607 17310884741236130733648911)
            ·
              refine ⟨25966327111854196100473367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17310884741236130733648911 25966327111854196100473367)
              ·
                refine ⟨38949490667781294150710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25966327111854196100473367 38949490667781294150710051)
                ·
                  refine ⟨58424236001671941226065077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38949490667781294150710051 58424236001671941226065077)
                  ·
                    refine ⟨5477272125156744489943601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58424236001671941226065077 5477272125156744489943601)
                    ·
                      refine ⟨4107954093867558367457701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477272125156744489943601 4107954093867558367457701)
                      ·
                        rfl

theorem cell23_8000212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8000212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000212 prefixEnd_8000212 := by exact prefixLift 8000212
  have htrace : WordTrace (prefixWord ++ tailWord_8000212) baseStart_8000212 baseEnd_8000212 := by
    simpa [prefixWord, tailWord_8000212, baseEnd_8000212] using wordTrace_append hprefix tailTrace_8000212
  have hstable : (prefixWord ++ tailWord_8000212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000212).length < 2 ^ (prefixWord ++ tailWord_8000212).sum := by decide
  have hdescent : baseEnd_8000212 < baseStart_8000212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000218 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_8000218 : Nat := 118140960795 + 8000218 * 2 ^ 59
def prefixEnd_8000218 : Nat := 4983230072969 + 3 ^ 40 * 8000218 * 2
def baseEnd_8000218 : Nat := 1369319058250495114660891

theorem tailTrace_8000218 : CollatzResearch.WordTrace tailWord_8000218 prefixEnd_8000218 1369319058250495114660891 := by
  unfold tailWord_8000218
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947980532645997325136327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194527948087055992867030205 72947980532645997325136327)
  ·
    refine ⟨109421970798968995987704491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72947980532645997325136327 109421970798968995987704491)
    ·
      refine ⟨164132956198453493981556737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109421970798968995987704491 164132956198453493981556737)
      ·
        refine ⟨123099717148840120486167553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164132956198453493981556737 123099717148840120486167553)
        ·
          refine ⟨92324787861630090364625665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123099717148840120486167553 92324787861630090364625665)
          ·
            refine ⟨69243590896222567773469249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92324787861630090364625665 69243590896222567773469249)
            ·
              refine ⟨51932693172166925830101937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69243590896222567773469249 51932693172166925830101937)
              ·
                refine ⟨38949519879125194372576453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51932693172166925830101937 38949519879125194372576453)
                ·
                  refine ⟨7303034977335973944858085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38949519879125194372576453 7303034977335973944858085)
                  ·
                    refine ⟨1369319058250495114660891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303034977335973944858085 1369319058250495114660891)
                    ·
                      rfl

theorem cell23_8000218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_8000218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000218 prefixEnd_8000218 := by exact prefixLift 8000218
  have htrace : WordTrace (prefixWord ++ tailWord_8000218) baseStart_8000218 baseEnd_8000218 := by
    simpa [prefixWord, tailWord_8000218, baseEnd_8000218] using wordTrace_append hprefix tailTrace_8000218
  have hstable : (prefixWord ++ tailWord_8000218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000218).length < 2 ^ (prefixWord ++ tailWord_8000218).sum := by decide
  have hdescent : baseEnd_8000218 < baseStart_8000218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000225 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_8000225 : Nat := 118140960795 + 8000225 * 2 ^ 59
def prefixEnd_8000225 : Nat := 4983230072969 + 3 ^ 40 * 8000225 * 2
def baseEnd_8000225 : Nat := 4107960769116066816595141

theorem tailTrace_8000225 : CollatzResearch.WordTrace tailWord_8000225 prefixEnd_8000225 4107960769116066816595141 := by
  unfold tailWord_8000225
  simp only [CollatzResearch.WordTrace]
  refine ⟨291792177441558629496050129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194528118294372419664033419 291792177441558629496050129)
  ·
    refine ⟨218844133081168972122037597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291792177441558629496050129 218844133081168972122037597)
    ·
      refine ⟨82066549905438364545764099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218844133081168972122037597 82066549905438364545764099)
      ·
        refine ⟨123099824858157546818646149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82066549905438364545764099 123099824858157546818646149)
        ·
          refine ⟨23081217160904540028496153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123099824858157546818646149 23081217160904540028496153)
          ·
            refine ⟨17310912870678405021372115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23081217160904540028496153 17310912870678405021372115)
            ·
              refine ⟨25966369306017607532058173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17310912870678405021372115 25966369306017607532058173)
              ·
                refine ⟨9737388489756602824521815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25966369306017607532058173 9737388489756602824521815)
                ·
                  refine ⟨14606082734634904236782723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737388489756602824521815 14606082734634904236782723)
                  ·
                    refine ⟨21909124101952356355174085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14606082734634904236782723 21909124101952356355174085)
                    ·
                      refine ⟨4107960769116066816595141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21909124101952356355174085 4107960769116066816595141)
                      ·
                        rfl

theorem cell23_8000225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_8000225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000225 prefixEnd_8000225 := by exact prefixLift 8000225
  have htrace : WordTrace (prefixWord ++ tailWord_8000225) baseStart_8000225 baseEnd_8000225 := by
    simpa [prefixWord, tailWord_8000225, baseEnd_8000225] using wordTrace_append hprefix tailTrace_8000225
  have hstable : (prefixWord ++ tailWord_8000225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000225).length < 2 ^ (prefixWord ++ tailWord_8000225).sum := by decide
  have hdescent : baseEnd_8000225 < baseStart_8000225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000242 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_8000242 : Nat := 118140960795 + 8000242 * 2 ^ 59
def prefixEnd_8000242 : Nat := 4983230072969 + 3 ^ 40 * 8000242 * 2
def baseEnd_8000242 : Nat := 4107969498287193250082563

theorem tailTrace_8000242 : CollatzResearch.WordTrace tailWord_8000242 prefixEnd_8000242 4107969498287193250082563 := by
  unfold tailWord_8000242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72948199370624260349854745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194528531654998027599612653 72948199370624260349854745)
  ·
    refine ⟨54711149527968195262391059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72948199370624260349854745 54711149527968195262391059)
    ·
      refine ⟨82066724291952292893586589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54711149527968195262391059 82066724291952292893586589)
      ·
        refine ⟨30775021609482109835094971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82066724291952292893586589 30775021609482109835094971)
        ·
          refine ⟨46162532414223164752642457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30775021609482109835094971 46162532414223164752642457)
          ·
            refine ⟨34621899310667373564481843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46162532414223164752642457 34621899310667373564481843)
            ·
              refine ⟨51932848966001060346722765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34621899310667373564481843 51932848966001060346722765)
              ·
                refine ⟨19474818362250397630021037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51932848966001060346722765 19474818362250397630021037)
                ·
                  refine ⟨7303056885843899111257889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19474818362250397630021037 7303056885843899111257889)
                  ·
                    refine ⟨5477292664382924333443417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303056885843899111257889 5477292664382924333443417)
                    ·
                      refine ⟨4107969498287193250082563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477292664382924333443417 4107969498287193250082563)
                      ·
                        rfl

theorem cell23_8000242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_8000242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000242 prefixEnd_8000242 := by exact prefixLift 8000242
  have htrace : WordTrace (prefixWord ++ tailWord_8000242) baseStart_8000242 baseEnd_8000242 := by
    simpa [prefixWord, tailWord_8000242, baseEnd_8000242] using wordTrace_append hprefix tailTrace_8000242
  have hstable : (prefixWord ++ tailWord_8000242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000242).length < 2 ^ (prefixWord ++ tailWord_8000242).sum := by decide
  have hdescent : baseEnd_8000242 < baseStart_8000242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000252 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_8000252 : Nat := 118140960795 + 8000252 * 2 ^ 59
def prefixEnd_8000252 : Nat := 4983230072969 + 3 ^ 40 * 8000252 * 2
def baseEnd_8000252 : Nat := 1369324877697912736985839

theorem tailTrace_8000252 : CollatzResearch.WordTrace tailWord_8000252 prefixEnd_8000252 1369324877697912736985839 := by
  unfold tailWord_8000252
  simp only [CollatzResearch.WordTrace]
  refine ⟨145896581106230406553641505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194528774808307208738188673 145896581106230406553641505)
  ·
    refine ⟨109422435829672804915231129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145896581106230406553641505 109422435829672804915231129)
    ·
      refine ⟨82066826872254603686423347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109422435829672804915231129 82066826872254603686423347)
      ·
        refine ⟨123100240308381905529635021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82066826872254603686423347 123100240308381905529635021)
        ·
          refine ⟨46162590115643214573613133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123100240308381905529635021 46162590115643214573613133)
          ·
            refine ⟨17310971293366205465104925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46162590115643214573613133 17310971293366205465104925)
            ·
              refine ⟨6491614235012327049414347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17310971293366205465104925 6491614235012327049414347)
              ·
                refine ⟨9737421352518490574121521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491614235012327049414347 9737421352518490574121521)
                ·
                  refine ⟨7303066014388867930591141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737421352518490574121521 7303066014388867930591141)
                  ·
                    refine ⟨1369324877697912736985839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303066014388867930591141 1369324877697912736985839)
                    ·
                      rfl

theorem cell23_8000252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_8000252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000252 prefixEnd_8000252 := by exact prefixLift 8000252
  have htrace : WordTrace (prefixWord ++ tailWord_8000252) baseStart_8000252 baseEnd_8000252 := by
    simpa [prefixWord, tailWord_8000252, baseEnd_8000252] using wordTrace_append hprefix tailTrace_8000252
  have hstable : (prefixWord ++ tailWord_8000252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000252).length < 2 ^ (prefixWord ++ tailWord_8000252).sum := by decide
  have hdescent : baseEnd_8000252 < baseStart_8000252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000261 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_8000261 : Nat := 118140960795 + 8000261 * 2 ^ 59
def prefixEnd_8000261 : Nat := 4983230072969 + 3 ^ 40 * 8000261 * 2
def baseEnd_8000261 : Nat := 1369326418139876225248325

theorem tailTrace_8000261 : CollatzResearch.WordTrace tailWord_8000261 prefixEnd_8000261 1369326418139876225248325 := by
  unfold tailWord_8000261
  simp only [CollatzResearch.WordTrace]
  refine ⟨291793490469428207644360637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194528993646285471762907091 291793490469428207644360637)
  ·
    refine ⟨109422558926035577866635239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291793490469428207644360637 109422558926035577866635239)
    ·
      refine ⟨164133838389053366799952859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109422558926035577866635239 164133838389053366799952859)
      ·
        refine ⟨246200757583580050199929289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164133838389053366799952859 246200757583580050199929289)
        ·
          refine ⟨184650568187685037649946967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246200757583580050199929289 184650568187685037649946967)
          ·
            refine ⟨276975852281527556474920451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184650568187685037649946967 276975852281527556474920451)
            ·
              refine ⟨415463778422291334712380677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276975852281527556474920451 415463778422291334712380677)
              ·
                refine ⟨77899458454179625258571377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415463778422291334712380677 77899458454179625258571377)
                ·
                  refine ⟨58424593840634718943928533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77899458454179625258571377 58424593840634718943928533)
                  ·
                    refine ⟨1369326418139876225248325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58424593840634718943928533 1369326418139876225248325)
                    ·
                      rfl

theorem cell23_8000261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_8000261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000261 prefixEnd_8000261 := by exact prefixLift 8000261
  have htrace : WordTrace (prefixWord ++ tailWord_8000261) baseStart_8000261 baseEnd_8000261 := by
    simpa [prefixWord, tailWord_8000261, baseEnd_8000261] using wordTrace_append hprefix tailTrace_8000261
  have hstable : (prefixWord ++ tailWord_8000261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000261).length < 2 ^ (prefixWord ++ tailWord_8000261).sum := by decide
  have hdescent : baseEnd_8000261 < baseStart_8000261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000271 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_8000271 : Nat := 118140960795 + 8000271 * 2 ^ 59
def prefixEnd_8000271 : Nat := 4983230072969 + 3 ^ 40 * 8000271 * 2
def baseEnd_8000271 : Nat := 4107984389226173636619929

theorem tailTrace_8000271 : CollatzResearch.WordTrace tailWord_8000271 prefixEnd_8000271 4107984389226173636619929 := by
  unfold tailWord_8000271
  simp only [CollatzResearch.WordTrace]
  refine ⟨291793855199391979352224667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194529236799594652901483111 291793855199391979352224667)
  ·
    refine ⟨437690782799087969028337001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291793855199391979352224667 437690782799087969028337001)
    ·
      refine ⟨328268087099315976771252751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437690782799087969028337001 328268087099315976771252751)
      ·
        refine ⟨492402130648973965156879127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328268087099315976771252751 492402130648973965156879127)
        ·
          refine ⟨738603195973460947735318691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492402130648973965156879127 738603195973460947735318691)
          ·
            refine ⟨1107904793960191421602978037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738603195973460947735318691 1107904793960191421602978037)
            ·
              refine ⟨103866074433767945775279191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1107904793960191421602978037 103866074433767945775279191)
              ·
                refine ⟨155799111650651918662918787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103866074433767945775279191 155799111650651918662918787)
                ·
                  refine ⟨233698667475977877994378181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155799111650651918662918787 233698667475977877994378181)
                  ·
                    refine ⟨43818500151745852123945909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233698667475977877994378181 43818500151745852123945909)
                    ·
                      refine ⟨4107984389226173636619929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43818500151745852123945909 4107984389226173636619929)
                      ·
                        rfl

theorem cell23_8000271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_8000271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000271 prefixEnd_8000271 := by exact prefixLift 8000271
  have htrace : WordTrace (prefixWord ++ tailWord_8000271) baseStart_8000271 baseEnd_8000271 := by
    simpa [prefixWord, tailWord_8000271, baseEnd_8000271] using wordTrace_append hprefix tailTrace_8000271
  have hstable : (prefixWord ++ tailWord_8000271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000271).length < 2 ^ (prefixWord ++ tailWord_8000271).sum := by decide
  have hdescent : baseEnd_8000271 < baseStart_8000271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000309 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_8000309 : Nat := 118140960795 + 8000309 * 2 ^ 59
def prefixEnd_8000309 : Nat := 4983230072969 + 3 ^ 40 * 8000309 * 2
def baseEnd_8000309 : Nat := 4108003901491044487944755

theorem tailTrace_8000309 : CollatzResearch.WordTrace tailWord_8000309 prefixEnd_8000309 4108003901491044487944755 := by
  unfold tailWord_8000309
  simp only [CollatzResearch.WordTrace]
  refine ⟨291795241173254311842107981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194530160782169541228071987 291795241173254311842107981)
  ·
    refine ⟨109423215439970366940790493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291795241173254311842107981 109423215439970366940790493)
    ·
      refine ⟨41033705789988887602796435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109423215439970366940790493 41033705789988887602796435)
      ·
        refine ⟨61550558684983331404194653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41033705789988887602796435 61550558684983331404194653)
        ·
          refine ⟨23081459506868749276572995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61550558684983331404194653 23081459506868749276572995)
          ·
            refine ⟨34622189260303123914859493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23081459506868749276572995 34622189260303123914859493)
            ·
              refine ⟨6491660486306835734036155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34622189260303123914859493 6491660486306835734036155)
              ·
                refine ⟨9737490729460253601054233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491660486306835734036155 9737490729460253601054233)
                ·
                  refine ⟨7303118047095190200790675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737490729460253601054233 7303118047095190200790675)
                  ·
                    refine ⟨10954677070642785301186013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303118047095190200790675 10954677070642785301186013)
                    ·
                      refine ⟨4108003901491044487944755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10954677070642785301186013 4108003901491044487944755)
                      ·
                        rfl

theorem cell23_8000309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_8000309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000309 prefixEnd_8000309 := by exact prefixLift 8000309
  have htrace : WordTrace (prefixWord ++ tailWord_8000309) baseStart_8000309 baseEnd_8000309 := by
    simpa [prefixWord, tailWord_8000309, baseEnd_8000309] using wordTrace_append hprefix tailTrace_8000309
  have hstable : (prefixWord ++ tailWord_8000309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000309).length < 2 ^ (prefixWord ++ tailWord_8000309).sum := by decide
  have hdescent : baseEnd_8000309 < baseStart_8000309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000319 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 1, 3, 2]
def baseStart_8000319 : Nat := 118140960795 + 8000319 * 2 ^ 59
def prefixEnd_8000319 : Nat := 4983230072969 + 3 ^ 40 * 8000319 * 2
def baseEnd_8000319 : Nat := 4108009036297589448819709

theorem tailTrace_8000319 : CollatzResearch.WordTrace tailWord_8000319 prefixEnd_8000319 4108009036297589448819709 := by
  unfold tailWord_8000319
  simp only [CollatzResearch.WordTrace]
  refine ⟨291795605903218083549972011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194530403935478722366648007 291795605903218083549972011)
  ·
    refine ⟨437693408854827125324958017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291795605903218083549972011 437693408854827125324958017)
    ·
      refine ⟨328270056641120343993718513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437693408854827125324958017 328270056641120343993718513)
      ·
        refine ⟨246202542480840257995288885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328270056641120343993718513 246202542480840257995288885)
        ·
          refine ⟨23081488357578774187058333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246202542480840257995288885 23081488357578774187058333)
          ·
            refine ⟨8655558134092040320146875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23081488357578774187058333 8655558134092040320146875)
            ·
              refine ⟨12983337201138060480220313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655558134092040320146875 12983337201138060480220313)
              ·
                refine ⟨9737502900853545360165235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12983337201138060480220313 9737502900853545360165235)
                ·
                  refine ⟨14606254351280318040247853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737502900853545360165235 14606254351280318040247853)
                  ·
                    refine ⟨5477345381730119265092945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14606254351280318040247853 5477345381730119265092945)
                    ·
                      refine ⟨4108009036297589448819709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477345381730119265092945 4108009036297589448819709)
                      ·
                        rfl

theorem cell23_8000319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_8000319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000319 prefixEnd_8000319 := by exact prefixLift 8000319
  have htrace : WordTrace (prefixWord ++ tailWord_8000319) baseStart_8000319 baseEnd_8000319 := by
    simpa [prefixWord, tailWord_8000319, baseEnd_8000319] using wordTrace_append hprefix tailTrace_8000319
  have hstable : (prefixWord ++ tailWord_8000319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000319).length < 2 ^ (prefixWord ++ tailWord_8000319).sum := by decide
  have hdescent : baseEnd_8000319 < baseStart_8000319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000332 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_8000332 : Nat := 118140960795 + 8000332 * 2 ^ 59
def prefixEnd_8000332 : Nat := 4983230072969 + 3 ^ 40 * 8000332 * 2
def baseEnd_8000332 : Nat := 4108015711546097897957149

theorem tailTrace_8000332 : CollatzResearch.WordTrace tailWord_8000332 prefixEnd_8000332 4108015711546097897957149 := by
  unfold tailWord_8000332
  simp only [CollatzResearch.WordTrace]
  refine ⟨145898040026085493385097625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194530720034780657846796833 145898040026085493385097625)
  ·
    refine ⟨109423530019564120038823219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145898040026085493385097625 109423530019564120038823219)
    ·
      refine ⟨164135295029346180058234829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109423530019564120038823219 164135295029346180058234829)
      ·
        refine ⟨61550735636004817521838061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164135295029346180058234829 61550735636004817521838061)
        ·
          refine ⟨23081525863501806570689273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61550735636004817521838061 23081525863501806570689273)
          ·
            refine ⟨17311144397626354928016955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23081525863501806570689273 17311144397626354928016955)
            ·
              refine ⟨25966716596439532392025433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17311144397626354928016955 25966716596439532392025433)
              ·
                refine ⟨19475037447329649294019075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25966716596439532392025433 19475037447329649294019075)
                ·
                  refine ⟨29212556170994473941028613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19475037447329649294019075 29212556170994473941028613)
                  ·
                    refine ⟨5477354282061463863942865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29212556170994473941028613 5477354282061463863942865)
                    ·
                      refine ⟨4108015711546097897957149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477354282061463863942865 4108015711546097897957149)
                      ·
                        rfl

theorem cell23_8000332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_8000332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000332 prefixEnd_8000332 := by exact prefixLift 8000332
  have htrace : WordTrace (prefixWord ++ tailWord_8000332) baseStart_8000332 baseEnd_8000332 := by
    simpa [prefixWord, tailWord_8000332, baseEnd_8000332] using wordTrace_append hprefix tailTrace_8000332
  have hstable : (prefixWord ++ tailWord_8000332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000332).length < 2 ^ (prefixWord ++ tailWord_8000332).sum := by decide
  have hdescent : baseEnd_8000332 < baseStart_8000332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000368 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_8000368 : Nat := 118140960795 + 8000368 * 2 ^ 59
def prefixEnd_8000368 : Nat := 4983230072969 + 3 ^ 40 * 8000368 * 2
def baseEnd_8000368 : Nat := 1369344732283219919035661

theorem tailTrace_8000368 : CollatzResearch.WordTrace tailWord_8000368 prefixEnd_8000368 1369344732283219919035661 := by
  unfold tailWord_8000368
  simp only [CollatzResearch.WordTrace]
  refine ⟨145898696540020282459252879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194531595386693709945670505 145898696540020282459252879)
  ·
    refine ⟨218848044810030423688879319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145898696540020282459252879 218848044810030423688879319)
    ·
      refine ⟨328272067215045635533318979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218848044810030423688879319 328272067215045635533318979)
      ·
        refine ⟨492408100822568453299978469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328272067215045635533318979 492408100822568453299978469)
        ·
          refine ⟨92326518904231584993745963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492408100822568453299978469 92326518904231584993745963)
          ·
            refine ⟨138489778356347377490618945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92326518904231584993745963 138489778356347377490618945)
            ·
              refine ⟨103867333767260533117964209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138489778356347377490618945 103867333767260533117964209)
              ·
                refine ⟨77900500325445399838473157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103867333767260533117964209 77900500325445399838473157)
                ·
                  refine ⟨14606343811021012469713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77900500325445399838473157 14606343811021012469713717)
                  ·
                    refine ⟨1369344732283219919035661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14606343811021012469713717 1369344732283219919035661)
                    ·
                      rfl

theorem cell23_8000368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_8000368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000368 prefixEnd_8000368 := by exact prefixLift 8000368
  have htrace : WordTrace (prefixWord ++ tailWord_8000368) baseStart_8000368 baseEnd_8000368 := by
    simpa [prefixWord, tailWord_8000368, baseEnd_8000368] using wordTrace_append hprefix tailTrace_8000368
  have hstable : (prefixWord ++ tailWord_8000368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000368).length < 2 ^ (prefixWord ++ tailWord_8000368).sum := by decide
  have hdescent : baseEnd_8000368 < baseStart_8000368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000406 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_8000406 : Nat := 118140960795 + 8000406 * 2 ^ 59
def prefixEnd_8000406 : Nat := 4983230072969 + 3 ^ 40 * 8000406 * 2
def baseEnd_8000406 : Nat := 456450412123836734270201

theorem tailTrace_8000406 : CollatzResearch.WordTrace tailWord_8000406 prefixEnd_8000406 456450412123836734270201 := by
  unfold tailWord_8000406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237423690868931088024317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194532519369268598272259381 18237423690868931088024317)
  ·
    refine ⟨6839033884075849158009119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18237423690868931088024317 6839033884075849158009119)
    ·
      refine ⟨10258550826113773737013679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839033884075849158009119 10258550826113773737013679)
      ·
        refine ⟨15387826239170660605520519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258550826113773737013679 15387826239170660605520519)
        ·
          refine ⟨23081739358755990908280779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387826239170660605520519 23081739358755990908280779)
          ·
            refine ⟨34622609038133986362421169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23081739358755990908280779 34622609038133986362421169)
            ·
              refine ⟨25966956778600489771815877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34622609038133986362421169 25966956778600489771815877)
              ·
                refine ⟨4868804395987591832215477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25966956778600489771815877 4868804395987591832215477)
                ·
                  refine ⟨456450412123836734270201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4868804395987591832215477 456450412123836734270201)
                  ·
                    rfl

theorem cell23_8000406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_8000406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000406 prefixEnd_8000406 := by exact prefixLift 8000406
  have htrace : WordTrace (prefixWord ++ tailWord_8000406) baseStart_8000406 baseEnd_8000406 := by
    simpa [prefixWord, tailWord_8000406, baseEnd_8000406] using wordTrace_append hprefix tailTrace_8000406
  have hstable : (prefixWord ++ tailWord_8000406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000406).length < 2 ^ (prefixWord ++ tailWord_8000406).sum := by decide
  have hdescent : baseEnd_8000406 < baseStart_8000406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000479 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 6]
def baseStart_8000479 : Nat := 118140960795 + 8000479 * 2 ^ 59
def prefixEnd_8000479 : Nat := 4983230072969 + 3 ^ 40 * 8000479 * 2
def baseEnd_8000479 : Nat := 456454577022478758090997

theorem tailTrace_8000479 : CollatzResearch.WordTrace tailWord_8000479 prefixEnd_8000479 456454577022478758090997 := by
  unfold tailWord_8000479
  simp only [CollatzResearch.WordTrace]
  refine ⟨291801441582638430875796491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194534294388425620583864327 291801441582638430875796491)
  ·
    refine ⟨437702162373957646313694737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291801441582638430875796491 437702162373957646313694737)
    ·
      refine ⟨328276621780468234735271053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437702162373957646313694737 328276621780468234735271053)
      ·
        refine ⟨123103733167675588025726645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328276621780468234735271053 123103733167675588025726645)
        ·
          refine ⟨11540974984469586377411873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123103733167675588025726645 11540974984469586377411873)
          ·
            refine ⟨8655731238352189783058905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540974984469586377411873 8655731238352189783058905)
            ·
              refine ⟨6491798428764142337294179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655731238352189783058905 6491798428764142337294179)
              ·
                refine ⟨9737697643146213505941269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491798428764142337294179 9737697643146213505941269)
                ·
                  refine ⟨456454577022478758090997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9737697643146213505941269 456454577022478758090997)
                  ·
                    rfl

theorem cell23_8000479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 6].length) (baseStart_8000479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000479 prefixEnd_8000479 := by exact prefixLift 8000479
  have htrace : WordTrace (prefixWord ++ tailWord_8000479) baseStart_8000479 baseEnd_8000479 := by
    simpa [prefixWord, tailWord_8000479, baseEnd_8000479] using wordTrace_append hprefix tailTrace_8000479
  have hstable : (prefixWord ++ tailWord_8000479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000479).length < 2 ^ (prefixWord ++ tailWord_8000479).sum := by decide
  have hdescent : baseEnd_8000479 < baseStart_8000479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000505 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_8000505 : Nat := 118140960795 + 8000505 * 2 ^ 59
def prefixEnd_8000505 : Nat := 4983230072969 + 3 ^ 40 * 8000505 * 2
def baseEnd_8000505 : Nat := 1369368181233108573697951

theorem tailTrace_8000505 : CollatzResearch.WordTrace tailWord_8000505 prefixEnd_8000505 1369368181233108573697951 := by
  unfold tailWord_8000505
  simp only [CollatzResearch.WordTrace]
  refine ⟨291802389880544237316242969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194534926587029491544161979 291802389880544237316242969)
  ·
    refine ⟨218851792410408177987182227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291802389880544237316242969 218851792410408177987182227)
    ·
      refine ⟨328277688615612266980773341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218851792410408177987182227 328277688615612266980773341)
      ·
        refine ⟨123104133230854600117790003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328277688615612266980773341 123104133230854600117790003)
        ·
          refine ⟨184656199846281900176685005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123104133230854600117790003 184656199846281900176685005)
          ·
            refine ⟨69246074942355712566256877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184656199846281900176685005 69246074942355712566256877)
            ·
              refine ⟨25967278103383392212346329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69246074942355712566256877 25967278103383392212346329)
              ·
                refine ⟨19475458577537544159259747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25967278103383392212346329 19475458577537544159259747)
                ·
                  refine ⟨29213187866306316238889621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19475458577537544159259747 29213187866306316238889621)
                  ·
                    refine ⟨1369368181233108573697951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29213187866306316238889621 1369368181233108573697951)
                    ·
                      rfl

theorem cell23_8000505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_8000505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000505 prefixEnd_8000505 := by exact prefixLift 8000505
  have htrace : WordTrace (prefixWord ++ tailWord_8000505) baseStart_8000505 baseEnd_8000505 := by
    simpa [prefixWord, tailWord_8000505, baseEnd_8000505] using wordTrace_append hprefix tailTrace_8000505
  have hstable : (prefixWord ++ tailWord_8000505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000505).length < 2 ^ (prefixWord ++ tailWord_8000505).sum := by decide
  have hdescent : baseEnd_8000505 < baseStart_8000505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000523 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 1, 1, 3]
def baseStart_8000523 : Nat := 118140960795 + 8000523 * 2 ^ 59
def prefixEnd_8000523 : Nat := 4983230072969 + 3 ^ 40 * 8000523 * 2
def baseEnd_8000523 : Nat := 4108113786351106650668771

theorem tailTrace_8000523 : CollatzResearch.WordTrace tailWord_8000523 prefixEnd_8000523 4108113786351106650668771 := by
  unfold tailWord_8000523
  simp only [CollatzResearch.WordTrace]
  refine ⟨291803046394479026390398223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194535364262986017593598815 291803046394479026390398223)
  ·
    refine ⟨437704569591718539585597335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291803046394479026390398223 437704569591718539585597335)
    ·
      refine ⟨656556854387577809378396003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437704569591718539585597335 656556854387577809378396003)
      ·
        refine ⟨984835281581366714067594005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656556854387577809378396003 984835281581366714067594005)
        ·
          refine ⟨46164153824126564721918469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 984835281581366714067594005 46164153824126564721918469)
          ·
            refine ⟨8655778842023730885359713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46164153824126564721918469 8655778842023730885359713)
            ·
              refine ⟨6491834131517798164019785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655778842023730885359713 6491834131517798164019785)
              ·
                refine ⟨4868875598638348623014839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491834131517798164019785 4868875598638348623014839)
                ·
                  refine ⟨7303313397957522934522259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868875598638348623014839 7303313397957522934522259)
                  ·
                    refine ⟨10954970096936284401783389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303313397957522934522259 10954970096936284401783389)
                    ·
                      refine ⟨4108113786351106650668771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10954970096936284401783389 4108113786351106650668771)
                      ·
                        rfl

theorem cell23_8000523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 1, 3].length) (baseStart_8000523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000523 prefixEnd_8000523 := by exact prefixLift 8000523
  have htrace : WordTrace (prefixWord ++ tailWord_8000523) baseStart_8000523 baseEnd_8000523 := by
    simpa [prefixWord, tailWord_8000523, baseEnd_8000523] using wordTrace_append hprefix tailTrace_8000523
  have hstable : (prefixWord ++ tailWord_8000523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000523).length < 2 ^ (prefixWord ++ tailWord_8000523).sum := by decide
  have hdescent : baseEnd_8000523 < baseStart_8000523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000546 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_8000546 : Nat := 118140960795 + 8000546 * 2 ^ 59
def prefixEnd_8000546 : Nat := 4983230072969 + 3 ^ 40 * 8000546 * 2
def baseEnd_8000546 : Nat := 4108125596406160060681165

theorem tailTrace_8000546 : CollatzResearch.WordTrace tailWord_8000546 prefixEnd_8000546 4108125596406160060681165 := by
  unfold tailWord_8000546
  simp only [CollatzResearch.WordTrace]
  refine ⟨72950971318348925329621373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194535923515597134212323661 72950971318348925329621373)
  ·
    refine ⟨27356614244380846998608015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72950971318348925329621373 27356614244380846998608015)
    ·
      refine ⟨41034921366571270497912023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27356614244380846998608015 41034921366571270497912023)
      ·
        refine ⟨61552382049856905746868035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41034921366571270497912023 61552382049856905746868035)
        ·
          refine ⟨92328573074785358620302053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61552382049856905746868035 92328573074785358620302053)
          ·
            refine ⟨17311607451522254741306635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92328573074785358620302053 17311607451522254741306635)
            ·
              refine ⟨25967411177283382111959953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17311607451522254741306635 25967411177283382111959953)
              ·
                refine ⟨19475558382962536583969965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25967411177283382111959953 19475558382962536583969965)
                ·
                  refine ⟨7303334393610951218988737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19475558382962536583969965 7303334393610951218988737)
                  ·
                    refine ⟨5477500795208213414241553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303334393610951218988737 5477500795208213414241553)
                    ·
                      refine ⟨4108125596406160060681165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477500795208213414241553 4108125596406160060681165)
                      ·
                        rfl

theorem cell23_8000546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_8000546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000546 prefixEnd_8000546 := by exact prefixLift 8000546
  have htrace : WordTrace (prefixWord ++ tailWord_8000546) baseStart_8000546 baseEnd_8000546 := by
    simpa [prefixWord, tailWord_8000546, baseEnd_8000546] using wordTrace_append hprefix tailTrace_8000546
  have hstable : (prefixWord ++ tailWord_8000546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000546).length < 2 ^ (prefixWord ++ tailWord_8000546).sum := by decide
  have hdescent : baseEnd_8000546 < baseStart_8000546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000562 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_8000562 : Nat := 118140960795 + 8000562 * 2 ^ 59
def prefixEnd_8000562 : Nat := 4983230072969 + 3 ^ 40 * 8000562 * 2
def baseEnd_8000562 : Nat := 4108133812096631998081091

theorem tailTrace_8000562 : CollatzResearch.WordTrace tailWord_8000562 prefixEnd_8000562 4108133812096631998081091 := by
  unfold tailWord_8000562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72951117210334434012766985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194536312560891824034045293 72951117210334434012766985)
  ·
    refine ⟨54713337907750825509575239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72951117210334434012766985 54713337907750825509575239)
    ·
      refine ⟨82070006861626238264362859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54713337907750825509575239 82070006861626238264362859)
      ·
        refine ⟨123105010292439357396544289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82070006861626238264362859 123105010292439357396544289)
        ·
          refine ⟨92328757719329518047408217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123105010292439357396544289 92328757719329518047408217)
          ·
            refine ⟨69246568289497138535556163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92328757719329518047408217 69246568289497138535556163)
            ·
              refine ⟨103869852434245707803334245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69246568289497138535556163 103869852434245707803334245)
              ·
                refine ⟨19475597331421070213125171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103869852434245707803334245 19475597331421070213125171)
                ·
                  refine ⟨29213395997131605319687757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19475597331421070213125171 29213395997131605319687757)
                  ·
                    refine ⟨10955023498924351994882909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29213395997131605319687757 10955023498924351994882909)
                    ·
                      refine ⟨4108133812096631998081091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955023498924351994882909 4108133812096631998081091)
                      ·
                        rfl

theorem cell23_8000562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_8000562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000562 prefixEnd_8000562 := by exact prefixLift 8000562
  have htrace : WordTrace (prefixWord ++ tailWord_8000562) baseStart_8000562 baseEnd_8000562 := by
    simpa [prefixWord, tailWord_8000562, baseEnd_8000562] using wordTrace_append hprefix tailTrace_8000562
  have hstable : (prefixWord ++ tailWord_8000562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000562).length < 2 ^ (prefixWord ++ tailWord_8000562).sum := by decide
  have hdescent : baseEnd_8000562 < baseStart_8000562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000566 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_8000566 : Nat := 118140960795 + 8000566 * 2 ^ 59
def prefixEnd_8000566 : Nat := 4983230072969 + 3 ^ 40 * 8000566 * 2
def baseEnd_8000566 : Nat := 4108135866019249982431073

theorem tailTrace_8000566 : CollatzResearch.WordTrace tailWord_8000566 prefixEnd_8000566 4108135866019249982431073 := by
  unfold tailWord_8000566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237788420832702795888347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194536409822215496489475701 18237788420832702795888347)
  ·
    refine ⟨27356682631249054193832521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18237788420832702795888347 27356682631249054193832521)
    ·
      refine ⟨20517511973436790645374391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27356682631249054193832521 20517511973436790645374391)
      ·
        refine ⟨30776267960155185968061587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20517511973436790645374391 30776267960155185968061587)
        ·
          refine ⟨46164401940232778952092381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30776267960155185968061587 46164401940232778952092381)
          ·
            refine ⟨17311650727587292107034643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46164401940232778952092381 17311650727587292107034643)
            ·
              refine ⟨25967476091380938160551965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17311650727587292107034643 25967476091380938160551965)
              ·
                refine ⟨9737803534267851810206987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25967476091380938160551965 9737803534267851810206987)
                ·
                  refine ⟨14606705301401777715310481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737803534267851810206987 14606705301401777715310481)
                  ·
                    refine ⟨10955028976051333286482861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14606705301401777715310481 10955028976051333286482861)
                    ·
                      refine ⟨4108135866019249982431073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955028976051333286482861 4108135866019249982431073)
                      ·
                        rfl

theorem cell23_8000566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_8000566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000566 prefixEnd_8000566 := by exact prefixLift 8000566
  have htrace : WordTrace (prefixWord ++ tailWord_8000566) baseStart_8000566 baseEnd_8000566 := by
    simpa [prefixWord, tailWord_8000566, baseEnd_8000566] using wordTrace_append hprefix tailTrace_8000566
  have hstable : (prefixWord ++ tailWord_8000566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000566).length < 2 ^ (prefixWord ++ tailWord_8000566).sum := by decide
  have hdescent : baseEnd_8000566 < baseStart_8000566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000585 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_8000585 : Nat := 118140960795 + 8000585 * 2 ^ 59
def prefixEnd_8000585 : Nat := 4983230072969 + 3 ^ 40 * 8000585 * 2
def baseEnd_8000585 : Nat := 4108145622151685408093485

theorem tailTrace_8000585 : CollatzResearch.WordTrace tailWord_8000585 prefixEnd_8000585 4108145622151685408093485 := by
  unfold tailWord_8000585
  simp only [CollatzResearch.WordTrace]
  refine ⟨291805307720254410979155209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194536871813502940652770139 291805307720254410979155209)
  ·
    refine ⟨218853980790190808234366407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291805307720254410979155209 218853980790190808234366407)
    ·
      refine ⟨328280971185286212351549611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218853980790190808234366407 328280971185286212351549611)
      ·
        refine ⟨492421456777929318527324417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328280971185286212351549611 492421456777929318527324417)
        ·
          refine ⟨369316092583446988895493313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492421456777929318527324417 369316092583446988895493313)
          ·
            refine ⟨276987069437585241671619985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369316092583446988895493313 276987069437585241671619985)
            ·
              refine ⟨207740302078188931253714989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276987069437585241671619985 207740302078188931253714989)
              ·
                refine ⟨77902613279320849220143121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207740302078188931253714989 77902613279320849220143121)
                ·
                  refine ⟨58426959959490636915107341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77902613279320849220143121 58426959959490636915107341)
                  ·
                    refine ⟨21910109984808988843165253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58426959959490636915107341 21910109984808988843165253)
                    ·
                      refine ⟨4108145622151685408093485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21910109984808988843165253 4108145622151685408093485)
                      ·
                        rfl

theorem cell23_8000585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_8000585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000585 prefixEnd_8000585 := by exact prefixLift 8000585
  have htrace : WordTrace (prefixWord ++ tailWord_8000585) baseStart_8000585 baseEnd_8000585 := by
    simpa [prefixWord, tailWord_8000585, baseEnd_8000585] using wordTrace_append hprefix tailTrace_8000585
  have hstable : (prefixWord ++ tailWord_8000585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000585).length < 2 ^ (prefixWord ++ tailWord_8000585).sum := by decide
  have hdescent : baseEnd_8000585 < baseStart_8000585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000622 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_8000622 : Nat := 118140960795 + 8000622 * 2 ^ 59
def prefixEnd_8000622 : Nat := 4983230072969 + 3 ^ 40 * 8000622 * 2
def baseEnd_8000622 : Nat := 4108164620935901763330815

theorem tailTrace_8000622 : CollatzResearch.WordTrace tailWord_8000622 prefixEnd_8000622 4108164620935901763330815 := by
  unfold tailWord_8000622
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475832152640045787281515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194537771480746910865501413 36475832152640045787281515)
  ·
    refine ⟨54713748228960068680922273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36475832152640045787281515 54713748228960068680922273)
    ·
      refine ⟨41035311171720051510691705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54713748228960068680922273 41035311171720051510691705)
      ·
        refine ⟨30776483378790038633018779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41035311171720051510691705 30776483378790038633018779)
        ·
          refine ⟨46164725068185057949528169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30776483378790038633018779 46164725068185057949528169)
          ·
            refine ⟨34623543801138793462146127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46164725068185057949528169 34623543801138793462146127)
            ·
              refine ⟨51935315701708190193219191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34623543801138793462146127 51935315701708190193219191)
              ·
                refine ⟨77902973552562285289828787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51935315701708190193219191 77902973552562285289828787)
                ·
                  refine ⟨116854460328843427934743181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77902973552562285289828787 116854460328843427934743181)
                  ·
                    refine ⟨43820422623316285475528693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116854460328843427934743181 43820422623316285475528693)
                    ·
                      refine ⟨4108164620935901763330815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43820422623316285475528693 4108164620935901763330815)
                      ·
                        rfl

theorem cell23_8000622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_8000622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000622 prefixEnd_8000622 := by exact prefixLift 8000622
  have htrace : WordTrace (prefixWord ++ tailWord_8000622) baseStart_8000622 baseEnd_8000622 := by
    simpa [prefixWord, tailWord_8000622, baseEnd_8000622] using wordTrace_append hprefix tailTrace_8000622
  have hstable : (prefixWord ++ tailWord_8000622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000622).length < 2 ^ (prefixWord ++ tailWord_8000622).sum := by decide
  have hdescent : baseEnd_8000622 < baseStart_8000622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
