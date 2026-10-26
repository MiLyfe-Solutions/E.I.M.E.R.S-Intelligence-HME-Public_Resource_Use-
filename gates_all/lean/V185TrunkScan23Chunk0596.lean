import V185TrunkScan23Chunk0595

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3524113 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3524113 : Nat := 118140960795 + 3524113 * 2 ^ 59
def prefixEnd_3524113 : Nat := 4983230072969 + 3 ^ 40 * 3524113 * 2
def baseEnd_3524113 : Nat := 603187949919425208460135

theorem tailTrace_3524113 : CollatzResearch.WordTrace tailWord_3524113 prefixEnd_3524113 603187949919425208460135 := by
  unfold tailWord_3524113
  simp only [CollatzResearch.WordTrace]
  refine ⟨128534960681747946428144993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85689973787831964285429995 128534960681747946428144993)
  ·
    refine ⟨96401220511310959821108745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128534960681747946428144993 96401220511310959821108745)
    ·
      refine ⟨72300915383483219865831559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96401220511310959821108745 72300915383483219865831559)
      ·
        refine ⟨108451373075224829798747339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72300915383483219865831559 108451373075224829798747339)
        ·
          refine ⟨162677059612837244698121009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108451373075224829798747339 162677059612837244698121009)
          ·
            refine ⟨122007794709627933523590757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162677059612837244698121009 122007794709627933523590757)
            ·
              refine ⟨22876461508055237535673267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122007794709627933523590757 22876461508055237535673267)
              ·
                refine ⟨34314692262082856303509901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22876461508055237535673267 34314692262082856303509901)
                ·
                  refine ⟨12868009598281071113816213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34314692262082856303509901 12868009598281071113816213)
                  ·
                    refine ⟨603187949919425208460135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12868009598281071113816213 603187949919425208460135)
                    ·
                      rfl

theorem cell23_3524113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3524113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524113 prefixEnd_3524113 := by exact prefixLift 3524113
  have htrace : WordTrace (prefixWord ++ tailWord_3524113) baseStart_3524113 baseEnd_3524113 := by
    simpa [prefixWord, tailWord_3524113, baseEnd_3524113] using wordTrace_append hprefix tailTrace_3524113
  have hstable : (prefixWord ++ tailWord_3524113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524113).length < 2 ^ (prefixWord ++ tailWord_3524113).sum := by decide
  have hdescent : baseEnd_3524113 < baseStart_3524113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524131 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 3, 1, 3]
def baseStart_3524131 : Nat := 118140960795 + 3524131 * 2 ^ 59
def prefixEnd_3524131 : Nat := 4983230072969 + 3 ^ 40 * 3524131 * 2
def baseEnd_3524131 : Nat := 1809573092410056554955323

theorem tailTrace_3524131 : CollatzResearch.WordTrace tailWord_3524131 prefixEnd_3524131 1809573092410056554955323 := by
  unfold tailWord_3524131
  simp only [CollatzResearch.WordTrace]
  refine ⟨128535617195682735502300247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85690411463788490334866831 128535617195682735502300247)
  ·
    refine ⟨192803425793524103253450371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128535617195682735502300247 192803425793524103253450371)
    ·
      refine ⟨289205138690286154880175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192803425793524103253450371 289205138690286154880175557)
      ·
        refine ⟨54225963504428654040032917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289205138690286154880175557 54225963504428654040032917)
        ·
          refine ⟨2541842039270093158126543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54225963504428654040032917 2541842039270093158126543)
          ·
            refine ⟨3812763058905139737189815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541842039270093158126543 3812763058905139737189815)
            ·
              refine ⟨5719144588357709605784723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812763058905139737189815 5719144588357709605784723)
              ·
                refine ⟨8578716882536564408677085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719144588357709605784723 8578716882536564408677085)
                ·
                  refine ⟨3217018830951211653253907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8578716882536564408677085 3217018830951211653253907)
                  ·
                    refine ⟨4825528246426817479880861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217018830951211653253907 4825528246426817479880861)
                    ·
                      refine ⟨1809573092410056554955323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825528246426817479880861 1809573092410056554955323)
                      ·
                        rfl

theorem cell23_3524131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_3524131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524131 prefixEnd_3524131 := by exact prefixLift 3524131
  have htrace : WordTrace (prefixWord ++ tailWord_3524131) baseStart_3524131 baseEnd_3524131 := by
    simpa [prefixWord, tailWord_3524131, baseEnd_3524131] using wordTrace_append hprefix tailTrace_3524131
  have hstable : (prefixWord ++ tailWord_3524131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524131).length < 2 ^ (prefixWord ++ tailWord_3524131).sum := by decide
  have hdescent : baseEnd_3524131 < baseStart_3524131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524147 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 2, 4]
def baseStart_3524147 : Nat := 118140960795 + 3524147 * 2 ^ 59
def prefixEnd_3524147 : Nat := 4983230072969 + 3 ^ 40 * 3524147 * 2
def baseEnd_3524147 : Nat := 603193769366842830785083

theorem tailTrace_3524147 : CollatzResearch.WordTrace tailWord_3524147 prefixEnd_3524147 603193769366842830785083 := by
  unfold tailWord_3524147
  simp only [CollatzResearch.WordTrace]
  refine ⟨128536200763624770234882695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85690800509083180156588463 128536200763624770234882695)
  ·
    refine ⟨192804301145437155352324043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128536200763624770234882695 192804301145437155352324043)
    ·
      refine ⟨289206451718155733028486065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192804301145437155352324043 289206451718155733028486065)
      ·
        refine ⟨216904838788616799771364549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289206451718155733028486065 216904838788616799771364549)
        ·
          refine ⟨40669657272865649957130853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216904838788616799771364549 40669657272865649957130853)
          ·
            refine ⟨7625560738662309366962035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40669657272865649957130853 7625560738662309366962035)
            ·
              refine ⟨11438341107993464050443053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625560738662309366962035 11438341107993464050443053)
              ·
                refine ⟨4289377915497549018916145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11438341107993464050443053 4289377915497549018916145)
                ·
                  refine ⟨3217033436623161764187109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289377915497549018916145 3217033436623161764187109)
                  ·
                    refine ⟨603193769366842830785083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217033436623161764187109 603193769366842830785083)
                    ·
                      rfl

theorem cell23_3524147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 4].length) (baseStart_3524147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524147 prefixEnd_3524147 := by exact prefixLift 3524147
  have htrace : WordTrace (prefixWord ++ tailWord_3524147) baseStart_3524147 baseEnd_3524147 := by
    simpa [prefixWord, tailWord_3524147, baseEnd_3524147] using wordTrace_append hprefix tailTrace_3524147
  have hstable : (prefixWord ++ tailWord_3524147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524147).length < 2 ^ (prefixWord ++ tailWord_3524147).sum := by decide
  have hdescent : baseEnd_3524147 < baseStart_3524147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524167 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3524167 : Nat := 118140960795 + 3524167 * 2 ^ 59
def prefixEnd_3524167 : Nat := 4983230072969 + 3 ^ 40 * 3524167 * 2
def baseEnd_3524167 : Nat := 1809591577713618414105157

theorem tailTrace_3524167 : CollatzResearch.WordTrace tailWord_3524167 prefixEnd_3524167 1809591577713618414105157 := by
  unfold tailWord_3524167
  simp only [CollatzResearch.WordTrace]
  refine ⟨128536930223552313650610755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85691286815701542433740503 128536930223552313650610755)
  ·
    refine ⟨192805395335328470475916133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128536930223552313650610755 192805395335328470475916133)
    ·
      refine ⟨36151011625374088214234275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192805395335328470475916133 36151011625374088214234275)
      ·
        refine ⟨54226517438061132321351413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36151011625374088214234275 54226517438061132321351413)
        ·
          refine ⟨5083736009818231155126695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54226517438061132321351413 5083736009818231155126695)
          ·
            refine ⟨7625604014727346732690043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083736009818231155126695 7625604014727346732690043)
            ·
              refine ⟨11438406022091020099035065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625604014727346732690043 11438406022091020099035065)
              ·
                refine ⟨8578804516568265074276299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11438406022091020099035065 8578804516568265074276299)
                ·
                  refine ⟨12868206774852397611414449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8578804516568265074276299 12868206774852397611414449)
                  ·
                    refine ⟨9651155081139298208560837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12868206774852397611414449 9651155081139298208560837)
                    ·
                      refine ⟨1809591577713618414105157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9651155081139298208560837 1809591577713618414105157)
                      ·
                        rfl

theorem cell23_3524167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3524167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524167 prefixEnd_3524167 := by exact prefixLift 3524167
  have htrace : WordTrace (prefixWord ++ tailWord_3524167) baseStart_3524167 baseEnd_3524167 := by
    simpa [prefixWord, tailWord_3524167, baseEnd_3524167] using wordTrace_append hprefix tailTrace_3524167
  have hstable : (prefixWord ++ tailWord_3524167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524167).length < 2 ^ (prefixWord ++ tailWord_3524167).sum := by decide
  have hdescent : baseEnd_3524167 < baseStart_3524167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524188 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3524188 : Nat := 118140960795 + 3524188 * 2 ^ 59
def prefixEnd_3524188 : Nat := 4983230072969 + 3 ^ 40 * 3524188 * 2
def baseEnd_3524188 : Nat := 1809602360807362831942561

theorem tailTrace_3524188 : CollatzResearch.WordTrace tailWord_3524188 prefixEnd_3524188 1809602360807362831942561 := by
  unfold tailWord_3524188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64268848078238117118562609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85691797437650822824750145 64268848078238117118562609)
  ·
    refine ⟨48201636058678587838921957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64268848078238117118562609 48201636058678587838921957)
    ·
      refine ⟨9037806761002235219797867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48201636058678587838921957 9037806761002235219797867)
      ·
        refine ⟨13556710141503352829696801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9037806761002235219797867 13556710141503352829696801)
        ·
          refine ⟨10167532606127514622272601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13556710141503352829696801 10167532606127514622272601)
          ·
            refine ⟨7625649454595635966704451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10167532606127514622272601 7625649454595635966704451)
            ·
              refine ⟨11438474181893453950056677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625649454595635966704451 11438474181893453950056677)
              ·
                refine ⟨2144713909105022615635627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11438474181893453950056677 2144713909105022615635627)
                ·
                  refine ⟨3217070863657533923453441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144713909105022615635627 3217070863657533923453441)
                  ·
                    refine ⟨2412803147743150442590081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217070863657533923453441 2412803147743150442590081)
                    ·
                      refine ⟨1809602360807362831942561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412803147743150442590081 1809602360807362831942561)
                      ·
                        rfl

theorem cell23_3524188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3524188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524188 prefixEnd_3524188 := by exact prefixLift 3524188
  have htrace : WordTrace (prefixWord ++ tailWord_3524188) baseStart_3524188 baseEnd_3524188 := by
    simpa [prefixWord, tailWord_3524188, baseEnd_3524188] using wordTrace_append hprefix tailTrace_3524188
  have hstable : (prefixWord ++ tailWord_3524188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524188).length < 2 ^ (prefixWord ++ tailWord_3524188).sum := by decide
  have hdescent : baseEnd_3524188 < baseStart_3524188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524231 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_3524231 : Nat := 118140960795 + 3524231 * 2 ^ 59
def prefixEnd_3524231 : Nat := 4983230072969 + 3 ^ 40 * 3524231 * 2
def baseEnd_3524231 : Nat := 1809624440475506163704863

theorem tailTrace_3524231 : CollatzResearch.WordTrace tailWord_3524231 prefixEnd_3524231 1809624440475506163704863 := by
  unfold tailWord_3524231
  simp only [CollatzResearch.WordTrace]
  refine ⟨128539264495320452580940547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85692842996880301720627031 128539264495320452580940547)
  ·
    refine ⟨192808896742980678871410821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128539264495320452580940547 192808896742980678871410821)
    ·
      refine ⟨36151668139308877288389529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192808896742980678871410821 36151668139308877288389529)
      ·
        refine ⟨27113751104481657966292147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36151668139308877288389529 27113751104481657966292147)
        ·
          refine ⟨40670626656722486949438221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27113751104481657966292147 40670626656722486949438221)
          ·
            refine ⟨15251484996270932606039333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40670626656722486949438221 15251484996270932606039333)
            ·
              refine ⟨2859653436800799863632375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15251484996270932606039333 2859653436800799863632375)
              ·
                refine ⟨4289480155201199795448563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859653436800799863632375 4289480155201199795448563)
                ·
                  refine ⟨6434220232801799693172845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289480155201199795448563 6434220232801799693172845)
                  ·
                    refine ⟨2412832587300674884939817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6434220232801799693172845 2412832587300674884939817)
                    ·
                      refine ⟨1809624440475506163704863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412832587300674884939817 1809624440475506163704863)
                      ·
                        rfl

theorem cell23_3524231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_3524231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524231 prefixEnd_3524231 := by exact prefixLift 3524231
  have htrace : WordTrace (prefixWord ++ tailWord_3524231) baseStart_3524231 baseEnd_3524231 := by
    simpa [prefixWord, tailWord_3524231, baseEnd_3524231] using wordTrace_append hprefix tailTrace_3524231
  have hstable : (prefixWord ++ tailWord_3524231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524231).length < 2 ^ (prefixWord ++ tailWord_3524231).sum := by decide
  have hdescent : baseEnd_3524231 < baseStart_3524231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524257 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3524257 : Nat := 118140960795 + 3524257 * 2 ^ 59
def prefixEnd_3524257 : Nat := 4983230072969 + 3 ^ 40 * 3524257 * 2
def baseEnd_3524257 : Nat := 1809637790972523061979743

theorem tailTrace_3524257 : CollatzResearch.WordTrace tailWord_3524257 prefixEnd_3524257 1809637790972523061979743 := by
  unfold tailWord_3524257
  simp only [CollatzResearch.WordTrace]
  refine ⟨128540212793226259021387025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85693475195484172680924683 128540212793226259021387025)
  ·
    refine ⟨96405159594919694266040269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128540212793226259021387025 96405159594919694266040269)
    ·
      refine ⟨36151934848094885349765101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96405159594919694266040269 36151934848094885349765101)
      ·
        refine ⟨13556975568035582006161913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36151934848094885349765101 13556975568035582006161913)
        ·
          refine ⟨10167731676026686504621435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13556975568035582006161913 10167731676026686504621435)
          ·
            refine ⟨15251597514040029756932153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10167731676026686504621435 15251597514040029756932153)
            ·
              refine ⟨11438698135530022317699115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251597514040029756932153 11438698135530022317699115)
              ·
                refine ⟨17158047203295033476548673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438698135530022317699115 17158047203295033476548673)
                ·
                  refine ⟨12868535402471275107411505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17158047203295033476548673 12868535402471275107411505)
                  ·
                    refine ⟨9651401551853456330558629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12868535402471275107411505 9651401551853456330558629)
                    ·
                      refine ⟨1809637790972523061979743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9651401551853456330558629 1809637790972523061979743)
                      ·
                        rfl

theorem cell23_3524257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3524257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524257 prefixEnd_3524257 := by exact prefixLift 3524257
  have htrace : WordTrace (prefixWord ++ tailWord_3524257) baseStart_3524257 baseEnd_3524257 := by
    simpa [prefixWord, tailWord_3524257, baseEnd_3524257] using wordTrace_append hprefix tailTrace_3524257
  have hstable : (prefixWord ++ tailWord_3524257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524257).length < 2 ^ (prefixWord ++ tailWord_3524257).sum := by decide
  have hdescent : baseEnd_3524257 < baseStart_3524257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524278 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3524278 : Nat := 118140960795 + 3524278 * 2 ^ 59
def prefixEnd_3524278 : Nat := 4983230072969 + 3 ^ 40 * 3524278 * 2
def baseEnd_3524278 : Nat := 1809648574066267479817147

theorem tailTrace_3524278 : CollatzResearch.WordTrace tailWord_3524278 prefixEnd_3524278 1809648574066267479817147 := by
  unfold tailWord_3524278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8033811170384386225493843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85693985817433453071934325 8033811170384386225493843)
  ·
    refine ⟨12050716755576579338240765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8033811170384386225493843 12050716755576579338240765)
    ·
      refine ⟨4519018783341217251840287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12050716755576579338240765 4519018783341217251840287)
      ·
        refine ⟨6778528175011825877760431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519018783341217251840287 6778528175011825877760431)
        ·
          refine ⟨10167792262517738816640647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6778528175011825877760431 10167792262517738816640647)
          ·
            refine ⟨15251688393776608224960971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10167792262517738816640647 15251688393776608224960971)
            ·
              refine ⟨22877532590664912337441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15251688393776608224960971 22877532590664912337441457)
              ·
                refine ⟨17158149442998684253081093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22877532590664912337441457 17158149442998684253081093)
                ·
                  refine ⟨3217153020562253297452705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17158149442998684253081093 3217153020562253297452705)
                  ·
                    refine ⟨2412864765421689973089529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217153020562253297452705 2412864765421689973089529)
                    ·
                      refine ⟨1809648574066267479817147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412864765421689973089529 1809648574066267479817147)
                      ·
                        rfl

theorem cell23_3524278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3524278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524278 prefixEnd_3524278 := by exact prefixLift 3524278
  have htrace : WordTrace (prefixWord ++ tailWord_3524278) baseStart_3524278 baseEnd_3524278 := by
    simpa [prefixWord, tailWord_3524278, baseEnd_3524278] using wordTrace_append hprefix tailTrace_3524278
  have hstable : (prefixWord ++ tailWord_3524278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524278).length < 2 ^ (prefixWord ++ tailWord_3524278).sum := by decide
  have hdescent : baseEnd_3524278 < baseStart_3524278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524280 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_3524280 : Nat := 118140960795 + 3524280 * 2 ^ 59
def prefixEnd_3524280 : Nat := 4983230072969 + 3 ^ 40 * 3524280 * 2
def baseEnd_3524280 : Nat := 603216533675858823997379

theorem tailTrace_3524280 : CollatzResearch.WordTrace tailWord_3524280 prefixEnd_3524280 603216533675858823997379 := by
  unfold tailWord_3524280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64270525836071466974737147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85694034448095289299649529 64270525836071466974737147)
  ·
    refine ⟨96405788754107200462105721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64270525836071466974737147 96405788754107200462105721)
    ·
      refine ⟨72304341565580400346579291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96405788754107200462105721 72304341565580400346579291)
      ·
        refine ⟨108456512348370600519868937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72304341565580400346579291 108456512348370600519868937)
        ·
          refine ⟨81342384261277950389901703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108456512348370600519868937 81342384261277950389901703)
          ·
            refine ⟨122013576391916925584852555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81342384261277950389901703 122013576391916925584852555)
            ·
              refine ⟨183020364587875388377278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122013576391916925584852555 183020364587875388377278833)
              ·
                refine ⟨137265273440906541282959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183020364587875388377278833 137265273440906541282959125)
                ·
                  refine ⟨6434309692542494122638709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137265273440906541282959125 6434309692542494122638709)
                  ·
                    refine ⟨603216533675858823997379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6434309692542494122638709 603216533675858823997379)
                    ·
                      rfl

theorem cell23_3524280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_3524280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524280 prefixEnd_3524280 := by exact prefixLift 3524280
  have htrace : WordTrace (prefixWord ++ tailWord_3524280) baseStart_3524280 baseEnd_3524280 := by
    simpa [prefixWord, tailWord_3524280, baseEnd_3524280] using wordTrace_append hprefix tailTrace_3524280
  have hstable : (prefixWord ++ tailWord_3524280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524280).length < 2 ^ (prefixWord ++ tailWord_3524280).sum := by decide
  have hdescent : baseEnd_3524280 < baseStart_3524280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524284 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 5]
def baseStart_3524284 : Nat := 118140960795 + 3524284 * 2 ^ 59
def prefixEnd_3524284 : Nat := 4983230072969 + 3 ^ 40 * 3524284 * 2
def baseEnd_3524284 : Nat := 201072406105577161815791

theorem tailTrace_3524284 : CollatzResearch.WordTrace tailWord_3524284 prefixEnd_3524284 201072406105577161815791 := by
  unfold tailWord_3524284
  simp only [CollatzResearch.WordTrace]
  refine ⟨64270598782064221316309953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85694131709418961755079937 64270598782064221316309953)
  ·
    refine ⟨48202949086548165987232465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64270598782064221316309953 48202949086548165987232465)
    ·
      refine ⟨36152211814911124490424349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48202949086548165987232465 36152211814911124490424349)
      ·
        refine ⟨13557079430591671683909131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36152211814911124490424349 13557079430591671683909131)
        ·
          refine ⟨20335619145887507525863697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13557079430591671683909131 20335619145887507525863697)
          ·
            refine ⟨15251714359415630644397773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20335619145887507525863697 15251714359415630644397773)
            ·
              refine ⟨5719392884780861491649165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15251714359415630644397773 5719392884780861491649165)
              ·
                refine ⟨2144772331792823059368437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5719392884780861491649165 2144772331792823059368437)
                ·
                  refine ⟨201072406105577161815791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2144772331792823059368437 201072406105577161815791)
                  ·
                    rfl

theorem cell23_3524284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_3524284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524284 prefixEnd_3524284 := by exact prefixLift 3524284
  have htrace : WordTrace (prefixWord ++ tailWord_3524284) baseStart_3524284 baseEnd_3524284 := by
    simpa [prefixWord, tailWord_3524284, baseEnd_3524284] using wordTrace_append hprefix tailTrace_3524284
  have hstable : (prefixWord ++ tailWord_3524284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524284).length < 2 ^ (prefixWord ++ tailWord_3524284).sum := by decide
  have hdescent : baseEnd_3524284 < baseStart_3524284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524301 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3524301 : Nat := 118140960795 + 3524301 * 2 ^ 59
def prefixEnd_3524301 : Nat := 4983230072969 + 3 ^ 40 * 3524301 * 2
def baseEnd_3524301 : Nat := 201073376013480098869949

theorem tailTrace_3524301 : CollatzResearch.WordTrace tailWord_3524301 prefixEnd_3524301 201073376013480098869949 := by
  unfold tailWord_3524301
  simp only [CollatzResearch.WordTrace]
  refine ⟨128541817605066854535988757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85694545070044569690659171 128541817605066854535988757)
  ·
    refine ⟨6025397700237508806374473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128541817605066854535988757 6025397700237508806374473)
    ·
      refine ⟨4519048275178131604780855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6025397700237508806374473 4519048275178131604780855)
      ·
        refine ⟨6778572412767197407171283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519048275178131604780855 6778572412767197407171283)
        ·
          refine ⟨10167858619150796110756925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6778572412767197407171283 10167858619150796110756925)
          ·
            refine ⟨3812946982181548541533847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10167858619150796110756925 3812946982181548541533847)
            ·
              refine ⟨5719420473272322812300771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812946982181548541533847 5719420473272322812300771)
              ·
                refine ⟨8579130709908484218451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719420473272322812300771 8579130709908484218451157)
                ·
                  refine ⟨201073376013480098869949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8579130709908484218451157 201073376013480098869949)
                  ·
                    rfl

theorem cell23_3524301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3524301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524301 prefixEnd_3524301 := by exact prefixLift 3524301
  have htrace : WordTrace (prefixWord ++ tailWord_3524301) baseStart_3524301 baseEnd_3524301 := by
    simpa [prefixWord, tailWord_3524301, baseEnd_3524301] using wordTrace_append hprefix tailTrace_3524301
  have hstable : (prefixWord ++ tailWord_3524301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524301).length < 2 ^ (prefixWord ++ tailWord_3524301).sum := by decide
  have hdescent : baseEnd_3524301 < baseStart_3524301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524334 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3524334 : Nat := 118140960795 + 3524334 * 2 ^ 59
def prefixEnd_3524334 : Nat := 4983230072969 + 3 ^ 40 * 3524334 * 2
def baseEnd_3524334 : Nat := 1809677328982919260716889

theorem tailTrace_3524334 : CollatzResearch.WordTrace tailWord_3524334 prefixEnd_3524334 1809677328982919260716889 := by
  unfold tailWord_3524334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067877651743412646492507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85695347475964867447960037 16067877651743412646492507)
  ·
    refine ⟨24101816477615118969738761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16067877651743412646492507 24101816477615118969738761)
    ·
      refine ⟨18076362358211339227304071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24101816477615118969738761 18076362358211339227304071)
      ·
        refine ⟨27114543537317008840956107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18076362358211339227304071 27114543537317008840956107)
        ·
          refine ⟨40671815305975513261434161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27114543537317008840956107 40671815305975513261434161)
          ·
            refine ⟨30503861479481634946075621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40671815305975513261434161 30503861479481634946075621)
            ·
              refine ⟨5719474027402806552389179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30503861479481634946075621 5719474027402806552389179)
              ·
                refine ⟨8579211041104209828583769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719474027402806552389179 8579211041104209828583769)
                ·
                  refine ⟨6434408280828157371437827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8579211041104209828583769 6434408280828157371437827)
                  ·
                    refine ⟨9651612421242236057156741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6434408280828157371437827 9651612421242236057156741)
                    ·
                      refine ⟨1809677328982919260716889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9651612421242236057156741 1809677328982919260716889)
                      ·
                        rfl

theorem cell23_3524334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3524334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524334 prefixEnd_3524334 := by exact prefixLift 3524334
  have htrace : WordTrace (prefixWord ++ tailWord_3524334) baseStart_3524334 baseEnd_3524334 := by
    simpa [prefixWord, tailWord_3524334, baseEnd_3524334] using wordTrace_append hprefix tailTrace_3524334
  have hstable : (prefixWord ++ tailWord_3524334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524334).length < 2 ^ (prefixWord ++ tailWord_3524334).sum := by decide
  have hdescent : baseEnd_3524334 < baseStart_3524334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524387 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 3, 5]
def baseStart_3524387 : Nat := 118140960795 + 3524387 * 2 ^ 59
def prefixEnd_3524387 : Nat := 4983230072969 + 3 ^ 40 * 3524387 * 2
def baseEnd_3524387 : Nat := 603234847819202517784715

theorem tailTrace_3524387 : CollatzResearch.WordTrace tailWord_3524387 prefixEnd_3524387 603234847819202517784715 := by
  unfold tailWord_3524387
  simp only [CollatzResearch.WordTrace]
  refine ⟨128544954282755291223619415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85696636188503527482412943 128544954282755291223619415)
  ·
    refine ⟨192817431424132936835429123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128544954282755291223619415 192817431424132936835429123)
    ·
      refine ⟨289226147136199405253143685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192817431424132936835429123 289226147136199405253143685)
      ·
        refine ⟨54229902588037388484964441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289226147136199405253143685 54229902588037388484964441)
        ·
          refine ⟨40672426941028041363723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54229902588037388484964441 40672426941028041363723331)
          ·
            refine ⟨61008640411542062045584997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40672426941028041363723331 61008640411542062045584997)
            ·
              refine ⟨11439120077164136633547187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61008640411542062045584997 11439120077164136633547187)
              ·
                refine ⟨17158680115746204950320781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11439120077164136633547187 17158680115746204950320781)
                ·
                  refine ⟨6434505043404826856370293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17158680115746204950320781 6434505043404826856370293)
                  ·
                    refine ⟨603234847819202517784715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6434505043404826856370293 603234847819202517784715)
                    ·
                      rfl

theorem cell23_3524387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].length) (baseStart_3524387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524387 prefixEnd_3524387 := by exact prefixLift 3524387
  have htrace : WordTrace (prefixWord ++ tailWord_3524387) baseStart_3524387 baseEnd_3524387 := by
    simpa [prefixWord, tailWord_3524387, baseEnd_3524387] using wordTrace_append hprefix tailTrace_3524387
  have hstable : (prefixWord ++ tailWord_3524387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524387).length < 2 ^ (prefixWord ++ tailWord_3524387).sum := by decide
  have hdescent : baseEnd_3524387 < baseStart_3524387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524407 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_3524407 : Nat := 118140960795 + 3524407 * 2 ^ 59
def prefixEnd_3524407 : Nat := 4983230072969 + 3 ^ 40 * 3524407 * 2
def baseEnd_3524407 : Nat := 1809714813070697475104053

theorem tailTrace_3524407 : CollatzResearch.WordTrace tailWord_3524407 prefixEnd_3524407 1809714813070697475104053 := by
  unfold tailWord_3524407
  simp only [CollatzResearch.WordTrace]
  refine ⟨128545683742682834639347475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85697122495121889759564983 128545683742682834639347475)
  ·
    refine ⟨192818525614024251959021213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128545683742682834639347475 192818525614024251959021213)
    ·
      refine ⟨72306947105259094484632955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192818525614024251959021213 72306947105259094484632955)
      ·
        refine ⟨108460420657888641726949433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72306947105259094484632955 108460420657888641726949433)
        ·
          refine ⟨81345315493416481295212075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108460420657888641726949433 81345315493416481295212075)
          ·
            refine ⟨122017973240124721942818113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81345315493416481295212075 122017973240124721942818113)
            ·
              refine ⟨91513479930093541457113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122017973240124721942818113 91513479930093541457113585)
              ·
                refine ⟨68635109947570156092835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91513479930093541457113585 68635109947570156092835189)
                ·
                  refine ⟨6434541557584702133703299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68635109947570156092835189 6434541557584702133703299)
                  ·
                    refine ⟨9651812336377053200554949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6434541557584702133703299 9651812336377053200554949)
                    ·
                      refine ⟨1809714813070697475104053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9651812336377053200554949 1809714813070697475104053)
                      ·
                        rfl

theorem cell23_3524407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_3524407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524407 prefixEnd_3524407 := by exact prefixLift 3524407
  have htrace : WordTrace (prefixWord ++ tailWord_3524407) baseStart_3524407 baseEnd_3524407 := by
    simpa [prefixWord, tailWord_3524407, baseEnd_3524407] using wordTrace_append hprefix tailTrace_3524407
  have hstable : (prefixWord ++ tailWord_3524407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524407).length < 2 ^ (prefixWord ++ tailWord_3524407).sum := by decide
  have hdescent : baseEnd_3524407 < baseStart_3524407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524434 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3524434 : Nat := 118140960795 + 3524434 * 2 ^ 59
def prefixEnd_3524434 : Nat := 4983230072969 + 3 ^ 40 * 3524434 * 2
def baseEnd_3524434 : Nat := 603242892349456289822143

theorem tailTrace_3524434 : CollatzResearch.WordTrace tailWord_3524434 prefixEnd_3524434 603242892349456289822143 := by
  unfold tailWord_3524434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32136667128396254562645089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85697779009056678833720237 32136667128396254562645089)
  ·
    refine ⟨24102500346297190921983817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32136667128396254562645089 24102500346297190921983817)
    ·
      refine ⟨18076875259722893191487863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24102500346297190921983817 18076875259722893191487863)
      ·
        refine ⟨27115312889584339787231795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18076875259722893191487863 27115312889584339787231795)
        ·
          refine ⟨40672969334376509680847693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27115312889584339787231795 40672969334376509680847693)
          ·
            refine ⟨15252363500391191130317885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40672969334376509680847693 15252363500391191130317885)
            ·
              refine ⟨5719636312646696673869207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15252363500391191130317885 5719636312646696673869207)
              ·
                refine ⟨8579454468970045010803811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719636312646696673869207 8579454468970045010803811)
                ·
                  refine ⟨12869181703455067516205717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8579454468970045010803811 12869181703455067516205717)
                  ·
                    refine ⟨603242892349456289822143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12869181703455067516205717 603242892349456289822143)
                    ·
                      rfl

theorem cell23_3524434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3524434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524434 prefixEnd_3524434 := by exact prefixLift 3524434
  have htrace : WordTrace (prefixWord ++ tailWord_3524434) baseStart_3524434 baseEnd_3524434 := by
    simpa [prefixWord, tailWord_3524434, baseEnd_3524434] using wordTrace_append hprefix tailTrace_3524434
  have hstable : (prefixWord ++ tailWord_3524434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524434).length < 2 ^ (prefixWord ++ tailWord_3524434).sum := by decide
  have hdescent : baseEnd_3524434 < baseStart_3524434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524441 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 3, 2, 2]
def baseStart_3524441 : Nat := 118140960795 + 3524441 * 2 ^ 59
def prefixEnd_3524441 : Nat := 4983230072969 + 3 ^ 40 * 3524441 * 2
def baseEnd_3524441 : Nat := 1809732271412950342078897

theorem tailTrace_3524441 : CollatzResearch.WordTrace tailWord_3524441 prefixEnd_3524441 1809732271412950342078897 := by
  unfold tailWord_3524441
  simp only [CollatzResearch.WordTrace]
  refine ⟨128546923824559658446085177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85697949216373105630723451 128546923824559658446085177)
  ·
    refine ⟨96410192868419743834563883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128546923824559658446085177 96410192868419743834563883)
    ·
      refine ⟨144615289302629615751845825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96410192868419743834563883 144615289302629615751845825)
      ·
        refine ⟨108461466976972211813884369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144615289302629615751845825 108461466976972211813884369)
        ·
          refine ⟨81346100232729158860413277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108461466976972211813884369 81346100232729158860413277)
          ·
            refine ⟨30504787587273434572654979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81346100232729158860413277 30504787587273434572654979)
            ·
              refine ⟨45757181380910151858982469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30504787587273434572654979 45757181380910151858982469)
              ·
                refine ⟨8579471508920653473559213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45757181380910151858982469 8579471508920653473559213)
                ·
                  refine ⟨3217301815845245052584705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8579471508920653473559213 3217301815845245052584705)
                  ·
                    refine ⟨2412976361883933789438529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217301815845245052584705 2412976361883933789438529)
                    ·
                      refine ⟨1809732271412950342078897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412976361883933789438529 1809732271412950342078897)
                      ·
                        rfl

theorem cell23_3524441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_3524441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524441 prefixEnd_3524441 := by exact prefixLift 3524441
  have htrace : WordTrace (prefixWord ++ tailWord_3524441) baseStart_3524441 baseEnd_3524441 := by
    simpa [prefixWord, tailWord_3524441, baseEnd_3524441] using wordTrace_append hprefix tailTrace_3524441
  have hstable : (prefixWord ++ tailWord_3524441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524441).length < 2 ^ (prefixWord ++ tailWord_3524441).sum := by decide
  have hdescent : baseEnd_3524441 < baseStart_3524441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524447 : List Nat := [1, 1, 2, 3, 1, 5, 1, 9]
def baseStart_3524447 : Nat := 118140960795 + 3524447 * 2 ^ 59
def prefixEnd_3524447 : Nat := 4983230072969 + 3 ^ 40 * 3524447 * 2
def baseEnd_3524447 : Nat := 67027235270254715503847

theorem tailTrace_3524447 : CollatzResearch.WordTrace tailWord_3524447 prefixEnd_3524447 67027235270254715503847 := by
  unfold tailWord_3524447
  simp only [CollatzResearch.WordTrace]
  refine ⟨128547142662537921470803595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85698095108358614313869063 128547142662537921470803595)
  ·
    refine ⟨192820713993806882206205393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128547142662537921470803595 192820713993806882206205393)
    ·
      refine ⟨144615535495355161654654045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192820713993806882206205393 144615535495355161654654045)
      ·
        refine ⟨54230825810758185620495267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144615535495355161654654045 54230825810758185620495267)
        ·
          refine ⟨81346238716137278430742901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54230825810758185620495267 81346238716137278430742901)
          ·
            refine ⟨7626209879637869852882147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81346238716137278430742901 7626209879637869852882147)
            ·
              refine ⟨11439314819456804779323221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626209879637869852882147 11439314819456804779323221)
              ·
                refine ⟨67027235270254715503847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11439314819456804779323221 67027235270254715503847)
                ·
                  rfl

theorem cell23_3524447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 9].length) (baseStart_3524447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524447 prefixEnd_3524447 := by exact prefixLift 3524447
  have htrace : WordTrace (prefixWord ++ tailWord_3524447) baseStart_3524447 baseEnd_3524447 := by
    simpa [prefixWord, tailWord_3524447, baseEnd_3524447] using wordTrace_append hprefix tailTrace_3524447
  have hstable : (prefixWord ++ tailWord_3524447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524447).length < 2 ^ (prefixWord ++ tailWord_3524447).sum := by decide
  have hdescent : baseEnd_3524447 < baseStart_3524447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524452 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_3524452 : Nat := 118140960795 + 3524452 * 2 ^ 59
def prefixEnd_3524452 : Nat := 4983230072969 + 3 ^ 40 * 3524452 * 2
def baseEnd_3524452 : Nat := 1809737919700149799041347

theorem tailTrace_3524452 : CollatzResearch.WordTrace tailWord_3524452 prefixEnd_3524452 1809737919700149799041347 := by
  unfold tailWord_3524452
  simp only [CollatzResearch.WordTrace]
  refine ⟨64273662513759903662367805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85698216685013204883157073 64273662513759903662367805)
  ·
    refine ⟨24102623442659963873387927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64273662513759903662367805 24102623442659963873387927)
    ·
      refine ⟨36153935163989945810081891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24102623442659963873387927 36153935163989945810081891)
      ·
        refine ⟨54230902745984918715122837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36153935163989945810081891 54230902745984918715122837)
        ·
          refine ⟨2542073566218043064771383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54230902745984918715122837 2542073566218043064771383)
          ·
            refine ⟨3813110349327064597157075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542073566218043064771383 3813110349327064597157075)
            ·
              refine ⟨5719665523990596895735613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813110349327064597157075 5719665523990596895735613)
              ·
                refine ⟨2144874571496473835900855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5719665523990596895735613 2144874571496473835900855)
                ·
                  refine ⟨3217311857244710753851283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144874571496473835900855 3217311857244710753851283)
                  ·
                    refine ⟨4825967785867066130776925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217311857244710753851283 4825967785867066130776925)
                    ·
                      refine ⟨1809737919700149799041347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825967785867066130776925 1809737919700149799041347)
                      ·
                        rfl

theorem cell23_3524452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_3524452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524452 prefixEnd_3524452 := by exact prefixLift 3524452
  have htrace : WordTrace (prefixWord ++ tailWord_3524452) baseStart_3524452 baseEnd_3524452 := by
    simpa [prefixWord, tailWord_3524452, baseEnd_3524452] using wordTrace_append hprefix tailTrace_3524452
  have hstable : (prefixWord ++ tailWord_3524452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524452).length < 2 ^ (prefixWord ++ tailWord_3524452).sum := by decide
  have hdescent : baseEnd_3524452 < baseStart_3524452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524461 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3524461 : Nat := 118140960795 + 3524461 * 2 ^ 59
def prefixEnd_3524461 : Nat := 4983230072969 + 3 ^ 40 * 3524461 * 2
def baseEnd_3524461 : Nat := 1809742541026040263828805

theorem tailTrace_3524461 : CollatzResearch.WordTrace tailWord_3524461 prefixEnd_3524461 1809742541026040263828805 := by
  unfold tailWord_3524461
  simp only [CollatzResearch.WordTrace]
  refine ⟨128547653284487201861813237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85698435522991467907875491 128547653284487201861813237)
  ·
    refine ⟨12051342495420675174544991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128547653284487201861813237 12051342495420675174544991)
    ·
      refine ⟨18077013743131012761817487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12051342495420675174544991 18077013743131012761817487)
      ·
        refine ⟨27115520614696519142726231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077013743131012761817487 27115520614696519142726231)
        ·
          refine ⟨40673280922044778714089347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27115520614696519142726231 40673280922044778714089347)
          ·
            refine ⟨61009921383067168071134021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40673280922044778714089347 61009921383067168071134021)
            ·
              refine ⟨11439360259325094013337629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61009921383067168071134021 11439360259325094013337629)
              ·
                refine ⟨4289760097246910255001611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11439360259325094013337629 4289760097246910255001611)
                ·
                  refine ⟨6434640145870365382502417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289760097246910255001611 6434640145870365382502417)
                  ·
                    refine ⟨4825980109402774036876813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6434640145870365382502417 4825980109402774036876813)
                    ·
                      refine ⟨1809742541026040263828805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825980109402774036876813 1809742541026040263828805)
                      ·
                        rfl

theorem cell23_3524461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3524461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524461 prefixEnd_3524461 := by exact prefixLift 3524461
  have htrace : WordTrace (prefixWord ++ tailWord_3524461) baseStart_3524461 baseEnd_3524461 := by
    simpa [prefixWord, tailWord_3524461, baseEnd_3524461] using wordTrace_append hprefix tailTrace_3524461
  have hstable : (prefixWord ++ tailWord_3524461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524461).length < 2 ^ (prefixWord ++ tailWord_3524461).sum := by decide
  have hdescent : baseEnd_3524461 < baseStart_3524461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524477 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_3524477 : Nat := 118140960795 + 3524477 * 2 ^ 59
def prefixEnd_3524477 : Nat := 4983230072969 + 3 ^ 40 * 3524477 * 2
def baseEnd_3524477 : Nat := 603250252238837400409577

theorem tailTrace_3524477 : CollatzResearch.WordTrace tailWord_3524477 prefixEnd_3524477 603250252238837400409577 := by
  unfold tailWord_3524477
  simp only [CollatzResearch.WordTrace]
  refine ⟨128548236852429236594395685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85698824568286157729597123 128548236852429236594395685)
  ·
    refine ⟨24102794409830481861449191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128548236852429236594395685 24102794409830481861449191)
    ·
      refine ⟨36154191614745722792173787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24102794409830481861449191 36154191614745722792173787)
      ·
        refine ⟨54231287422118584188260681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36154191614745722792173787 54231287422118584188260681)
        ·
          refine ⟨40673465566588938141195511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54231287422118584188260681 40673465566588938141195511)
          ·
            refine ⟨61010198349883407211793267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40673465566588938141195511 61010198349883407211793267)
            ·
              refine ⟨91515297524825110817689901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61010198349883407211793267 91515297524825110817689901)
              ·
                refine ⟨34318236571809416556633713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91515297524825110817689901 34318236571809416556633713)
                ·
                  refine ⟨25738677428857062417475285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34318236571809416556633713 25738677428857062417475285)
                  ·
                    refine ⟨603250252238837400409577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25738677428857062417475285 603250252238837400409577)
                    ·
                      rfl

theorem cell23_3524477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_3524477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524477 prefixEnd_3524477 := by exact prefixLift 3524477
  have htrace : WordTrace (prefixWord ++ tailWord_3524477) baseStart_3524477 baseEnd_3524477 := by
    simpa [prefixWord, tailWord_3524477, baseEnd_3524477] using wordTrace_append hprefix tailTrace_3524477
  have hstable : (prefixWord ++ tailWord_3524477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524477).length < 2 ^ (prefixWord ++ tailWord_3524477).sum := by decide
  have hdescent : baseEnd_3524477 < baseStart_3524477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524481 : List Nat := [1, 2, 4, 4, 1, 1, 2, 8]
def baseStart_3524481 : Nat := 118140960795 + 3524481 * 2 ^ 59
def prefixEnd_3524481 : Nat := 4983230072969 + 3 ^ 40 * 3524481 * 2
def baseEnd_3524481 : Nat := 67027881875523340206619

theorem tailTrace_3524481 : CollatzResearch.WordTrace tailWord_3524481 prefixEnd_3524481 67027881875523340206619 := by
  unfold tailWord_3524481
  simp only [CollatzResearch.WordTrace]
  refine ⟨128548382744414745277541297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85698921829609830185027531 128548382744414745277541297)
  ·
    refine ⟨96411287058311058958155973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128548382744414745277541297 96411287058311058958155973)
    ·
      refine ⟨18077116323433323554654245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96411287058311058958155973 18077116323433323554654245)
      ·
        refine ⟨3389459310643748166497671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18077116323433323554654245 3389459310643748166497671)
        ·
          refine ⟨5084188965965622249746507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389459310643748166497671 5084188965965622249746507)
          ·
            refine ⟨7626283448948433374619761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084188965965622249746507 7626283448948433374619761)
            ·
              refine ⟨5719712586711325030964821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626283448948433374619761 5719712586711325030964821)
              ·
                refine ⟨67027881875523340206619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5719712586711325030964821 67027881875523340206619)
                ·
                  rfl

theorem cell23_3524481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 8].length) (baseStart_3524481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524481 prefixEnd_3524481 := by exact prefixLift 3524481
  have htrace : WordTrace (prefixWord ++ tailWord_3524481) baseStart_3524481 baseEnd_3524481 := by
    simpa [prefixWord, tailWord_3524481, baseEnd_3524481] using wordTrace_append hprefix tailTrace_3524481
  have hstable : (prefixWord ++ tailWord_3524481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524481).length < 2 ^ (prefixWord ++ tailWord_3524481).sum := by decide
  have hdescent : baseEnd_3524481 < baseStart_3524481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524501 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_3524501 : Nat := 118140960795 + 3524501 * 2 ^ 59
def prefixEnd_3524501 : Nat := 4983230072969 + 3 ^ 40 * 3524501 * 2
def baseEnd_3524501 : Nat := 1809763080252220107328621

theorem tailTrace_3524501 : CollatzResearch.WordTrace tailWord_3524501 prefixEnd_3524501 1809763080252220107328621 := by
  unfold tailWord_3524501
  simp only [CollatzResearch.WordTrace]
  refine ⟨128549112204342288693269357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85699408136228192462179571 128549112204342288693269357)
  ·
    refine ⟨48205917076628358259976009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128549112204342288693269357 48205917076628358259976009)
    ·
      refine ⟨36154437807471268694982007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48205917076628358259976009 36154437807471268694982007)
      ·
        refine ⟨54231656711206903042473011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36154437807471268694982007 54231656711206903042473011)
        ·
          refine ⟨81347485066810354563709517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54231656711206903042473011 81347485066810354563709517)
          ·
            refine ⟨30505306900053882961391069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81347485066810354563709517 30505306900053882961391069)
            ·
              refine ⟨11439490087520206110521651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30505306900053882961391069 11439490087520206110521651)
              ·
                refine ⟨17159235131280309165782477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11439490087520206110521651 17159235131280309165782477)
                ·
                  refine ⟨6434713174230115937168429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17159235131280309165782477 6434713174230115937168429)
                  ·
                    refine ⟨2413017440336293476438161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6434713174230115937168429 2413017440336293476438161)
                    ·
                      refine ⟨1809763080252220107328621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413017440336293476438161 1809763080252220107328621)
                      ·
                        rfl

theorem cell23_3524501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_3524501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524501 prefixEnd_3524501 := by exact prefixLift 3524501
  have htrace : WordTrace (prefixWord ++ tailWord_3524501) baseStart_3524501 baseEnd_3524501 := by
    simpa [prefixWord, tailWord_3524501, baseEnd_3524501] using wordTrace_append hprefix tailTrace_3524501
  have hstable : (prefixWord ++ tailWord_3524501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524501).length < 2 ^ (prefixWord ++ tailWord_3524501).sum := by decide
  have hdescent : baseEnd_3524501 < baseStart_3524501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524526 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3524526 : Nat := 118140960795 + 3524526 * 2 ^ 59
def prefixEnd_3524526 : Nat := 4983230072969 + 3 ^ 40 * 3524526 * 2
def baseEnd_3524526 : Nat := 1809775917268582509516007

theorem tailTrace_3524526 : CollatzResearch.WordTrace tailWord_3524526 prefixEnd_3524526 1809775917268582509516007 := by
  unfold tailWord_3524526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16068753003656464745366179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85700016019501145308619621 16068753003656464745366179)
  ·
    refine ⟨24103129505484697118049269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16068753003656464745366179 24103129505484697118049269)
    ·
      refine ⟨2259668391139190354817119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24103129505484697118049269 2259668391139190354817119)
      ·
        refine ⟨3389502586708785532225679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259668391139190354817119 3389502586708785532225679)
        ·
          refine ⟨5084253880063178298338519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389502586708785532225679 5084253880063178298338519)
          ·
            refine ⟨7626380820094767447507779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084253880063178298338519 7626380820094767447507779)
            ·
              refine ⟨11439571230142151171261669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626380820094767447507779 11439571230142151171261669)
              ·
                refine ⟨2144919605651653344611563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11439571230142151171261669 2144919605651653344611563)
                ·
                  refine ⟨3217379408477480016917345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144919605651653344611563 3217379408477480016917345)
                  ·
                    refine ⟨2413034556358110012688009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217379408477480016917345 2413034556358110012688009)
                    ·
                      refine ⟨1809775917268582509516007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413034556358110012688009 1809775917268582509516007)
                      ·
                        rfl

theorem cell23_3524526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3524526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524526 prefixEnd_3524526 := by exact prefixLift 3524526
  have htrace : WordTrace (prefixWord ++ tailWord_3524526) baseStart_3524526 baseEnd_3524526 := by
    simpa [prefixWord, tailWord_3524526, baseEnd_3524526] using wordTrace_append hprefix tailTrace_3524526
  have hstable : (prefixWord ++ tailWord_3524526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524526).length < 2 ^ (prefixWord ++ tailWord_3524526).sum := by decide
  have hdescent : baseEnd_3524526 < baseStart_3524526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524544 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_3524544 : Nat := 118140960795 + 3524544 * 2 ^ 59
def prefixEnd_3524544 : Nat := 4983230072969 + 3 ^ 40 * 3524544 * 2
def baseEnd_3524544 : Nat := 1809785159920363439090923

theorem tailTrace_3524544 : CollatzResearch.WordTrace tailWord_3524544 prefixEnd_3524544 1809785159920363439090923 := by
  unfold tailWord_3524544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64275340271593253518542343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85700453695457671358056457 64275340271593253518542343)
  ·
    refine ⟨96413010407389880277813515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64275340271593253518542343 96413010407389880277813515)
    ·
      refine ⟨144619515611084820416720273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96413010407389880277813515 144619515611084820416720273)
      ·
        refine ⟨108464636708313615312540205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144619515611084820416720273 108464636708313615312540205)
        ·
          refine ⟨40674238765617605742202577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108464636708313615312540205 40674238765617605742202577)
          ·
            refine ⟨30505679074213204306651933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40674238765617605742202577 30505679074213204306651933)
            ·
              refine ⟨11439629652829951614994475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30505679074213204306651933 11439629652829951614994475)
              ·
                refine ⟨17159444479244927422491713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11439629652829951614994475 17159444479244927422491713)
                ·
                  refine ⟨12869583359433695566868785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17159444479244927422491713 12869583359433695566868785)
                  ·
                    refine ⟨9652187519575271675151589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12869583359433695566868785 9652187519575271675151589)
                    ·
                      refine ⟨1809785159920363439090923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9652187519575271675151589 1809785159920363439090923)
                      ·
                        rfl

theorem cell23_3524544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_3524544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524544 prefixEnd_3524544 := by exact prefixLift 3524544
  have htrace : WordTrace (prefixWord ++ tailWord_3524544) baseStart_3524544 baseEnd_3524544 := by
    simpa [prefixWord, tailWord_3524544, baseEnd_3524544] using wordTrace_append hprefix tailTrace_3524544
  have hstable : (prefixWord ++ tailWord_3524544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524544).length < 2 ^ (prefixWord ++ tailWord_3524544).sum := by decide
  have hdescent : baseEnd_3524544 < baseStart_3524544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524584 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3524584 : Nat := 118140960795 + 3524584 * 2 ^ 59
def prefixEnd_3524584 : Nat := 4983230072969 + 3 ^ 40 * 3524584 * 2
def baseEnd_3524584 : Nat := 603268566382181094196913

theorem tailTrace_3524584 : CollatzResearch.WordTrace tailWord_3524584 prefixEnd_3524584 603268566382181094196913 := by
  unfold tailWord_3524584
  simp only [CollatzResearch.WordTrace]
  refine ⟨64276069731520796934270403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85701426308694395912360537 64276069731520796934270403)
  ·
    refine ⟨96414104597281195401405605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64276069731520796934270403 96414104597281195401405605)
    ·
      refine ⟨18077644611990224137763551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96414104597281195401405605 18077644611990224137763551)
      ·
        refine ⟨27116466917985336206645327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077644611990224137763551 27116466917985336206645327)
        ·
          refine ⟨40674700376978004309967991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27116466917985336206645327 40674700376978004309967991)
          ·
            refine ⟨61012050565467006464951987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40674700376978004309967991 61012050565467006464951987)
            ·
              refine ⟨91518075848200509697427981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61012050565467006464951987 91518075848200509697427981)
              ·
                refine ⟨34319278443075191136535493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91518075848200509697427981 34319278443075191136535493)
                ·
                  refine ⟨6434864708076598338100405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34319278443075191136535493 6434864708076598338100405)
                  ·
                    refine ⟨603268566382181094196913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6434864708076598338100405 603268566382181094196913)
                    ·
                      rfl

theorem cell23_3524584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3524584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524584 prefixEnd_3524584 := by exact prefixLift 3524584
  have htrace : WordTrace (prefixWord ++ tailWord_3524584) baseStart_3524584 baseEnd_3524584 := by
    simpa [prefixWord, tailWord_3524584, baseEnd_3524584] using wordTrace_append hprefix tailTrace_3524584
  have hstable : (prefixWord ++ tailWord_3524584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524584).length < 2 ^ (prefixWord ++ tailWord_3524584).sum := by decide
  have hdescent : baseEnd_3524584 < baseStart_3524584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524604 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3524604 : Nat := 118140960795 + 3524604 * 2 ^ 59
def prefixEnd_3524604 : Nat := 4983230072969 + 3 ^ 40 * 3524604 * 2
def baseEnd_3524604 : Nat := 1809815968759633204340647

theorem tailTrace_3524604 : CollatzResearch.WordTrace tailWord_3524604 prefixEnd_3524604 1809815968759633204340647 := by
  unfold tailWord_3524604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64276434461484568642134433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85701912615312758189512577 64276434461484568642134433)
  ·
    refine ⟨48207325846113426481600825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64276434461484568642134433 48207325846113426481600825)
    ·
      refine ⟨36155494384585069861200619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48207325846113426481600825 36155494384585069861200619)
      ·
        refine ⟨54233241576877604791800929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36155494384585069861200619 54233241576877604791800929)
        ·
          refine ⟨40674931182658203593850697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54233241576877604791800929 40674931182658203593850697)
          ·
            refine ⟨30506198386993652695388023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40674931182658203593850697 30506198386993652695388023)
            ·
              refine ⟨45759297580490479043082035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30506198386993652695388023 45759297580490479043082035)
              ·
                refine ⟨68638946370735718564623053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45759297580490479043082035 68638946370735718564623053)
                ·
                  refine ⟨25739604889025894461733645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68638946370735718564623053 25739604889025894461733645)
                  ·
                    refine ⟨9652351833384710423150117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25739604889025894461733645 9652351833384710423150117)
                    ·
                      refine ⟨1809815968759633204340647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9652351833384710423150117 1809815968759633204340647)
                      ·
                        rfl

theorem cell23_3524604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3524604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524604 prefixEnd_3524604 := by exact prefixLift 3524604
  have htrace : WordTrace (prefixWord ++ tailWord_3524604) baseStart_3524604 baseEnd_3524604 := by
    simpa [prefixWord, tailWord_3524604, baseEnd_3524604] using wordTrace_append hprefix tailTrace_3524604
  have hstable : (prefixWord ++ tailWord_3524604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524604).length < 2 ^ (prefixWord ++ tailWord_3524604).sum := by decide
  have hdescent : baseEnd_3524604 < baseStart_3524604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524698 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_3524698 : Nat := 118140960795 + 3524698 * 2 ^ 59
def prefixEnd_3524698 : Nat := 4983230072969 + 3 ^ 40 * 3524698 * 2
def baseEnd_3524698 : Nat := 1809864235941155836565215

theorem tailTrace_3524698 : CollatzResearch.WordTrace tailWord_3524698 prefixEnd_3524698 1809864235941155836565215 := by
  unfold tailWord_3524698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139074346157147834547687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85704198256419060892127165 32139074346157147834547687)
  ·
    refine ⟨48208611519235721751821531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32139074346157147834547687 48208611519235721751821531)
    ·
      refine ⟨72312917278853582627732297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48208611519235721751821531 72312917278853582627732297)
      ·
        refine ⟨54234687959140186970799223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72312917278853582627732297 54234687959140186970799223)
        ·
          refine ⟨81352031938710280456198835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54234687959140186970799223 81352031938710280456198835)
          ·
            refine ⟨122028047908065420684298253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81352031938710280456198835 122028047908065420684298253)
            ·
              refine ⟨45760517965524532756611845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122028047908065420684298253 45760517965524532756611845)
              ·
                refine ⟨8580097118535849891864721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45760517965524532756611845 8580097118535849891864721)
                ·
                  refine ⟨6435072838901887418898541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8580097118535849891864721 6435072838901887418898541)
                  ·
                    refine ⟨2413152314588207782086953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6435072838901887418898541 2413152314588207782086953)
                    ·
                      refine ⟨1809864235941155836565215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413152314588207782086953 1809864235941155836565215)
                      ·
                        rfl

theorem cell23_3524698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_3524698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524698 prefixEnd_3524698 := by exact prefixLift 3524698
  have htrace : WordTrace (prefixWord ++ tailWord_3524698) baseStart_3524698 baseEnd_3524698 := by
    simpa [prefixWord, tailWord_3524698, baseEnd_3524698] using wordTrace_append hprefix tailTrace_3524698
  have hstable : (prefixWord ++ tailWord_3524698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524698).length < 2 ^ (prefixWord ++ tailWord_3524698).sum := by decide
  have hdescent : baseEnd_3524698 < baseStart_3524698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524711 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3524711 : Nat := 118140960795 + 3524711 * 2 ^ 59
def prefixEnd_3524711 : Nat := 4983230072969 + 3 ^ 40 * 3524711 * 2
def baseEnd_3524711 : Nat := 1809870911189664285702655

theorem tailTrace_3524711 : CollatzResearch.WordTrace tailWord_3524711 prefixEnd_3524711 1809870911189664285702655 := by
  unfold tailWord_3524711
  simp only [CollatzResearch.WordTrace]
  refine ⟨128556771533581494558413987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85704514355720996372275991 128556771533581494558413987)
  ·
    refine ⟨192835157300372241837620981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128556771533581494558413987 192835157300372241837620981)
    ·
      refine ⟨18078295996909897672276967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192835157300372241837620981 18078295996909897672276967)
      ·
        refine ⟨27117443995364846508415451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078295996909897672276967 27117443995364846508415451)
        ·
          refine ⟨40676165993047269762623177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27117443995364846508415451 40676165993047269762623177)
          ·
            refine ⟨30507124494785452321967383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40676165993047269762623177 30507124494785452321967383)
            ·
              refine ⟨45760686742178178482951075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30507124494785452321967383 45760686742178178482951075)
              ·
                refine ⟨68641030113267267724426613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45760686742178178482951075 68641030113267267724426613)
                ·
                  refine ⟨6435096573118806349164995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68641030113267267724426613 6435096573118806349164995)
                  ·
                    refine ⟨9652644859678209523747493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435096573118806349164995 9652644859678209523747493)
                    ·
                      refine ⟨1809870911189664285702655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9652644859678209523747493 1809870911189664285702655)
                      ·
                        rfl

theorem cell23_3524711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3524711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524711 prefixEnd_3524711 := by exact prefixLift 3524711
  have htrace : WordTrace (prefixWord ++ tailWord_3524711) baseStart_3524711 baseEnd_3524711 := by
    simpa [prefixWord, tailWord_3524711, baseEnd_3524711] using wordTrace_append hprefix tailTrace_3524711
  have hstable : (prefixWord ++ tailWord_3524711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524711).length < 2 ^ (prefixWord ++ tailWord_3524711).sum := by decide
  have hdescent : baseEnd_3524711 < baseStart_3524711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524721 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_3524721 : Nat := 118140960795 + 3524721 * 2 ^ 59
def prefixEnd_3524721 : Nat := 4983230072969 + 3 ^ 40 * 3524721 * 2
def baseEnd_3524721 : Nat := 603292015332069748859203

theorem tailTrace_3524721 : CollatzResearch.WordTrace tailWord_3524721 prefixEnd_3524721 603292015332069748859203 := by
  unfold tailWord_3524721
  simp only [CollatzResearch.WordTrace]
  refine ⟨128557136263545266266278017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85704757509030177510852011 128557136263545266266278017)
  ·
    refine ⟨96417852197658949699708513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128557136263545266266278017 96417852197658949699708513)
    ·
      refine ⟨72313389148244212274781385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96417852197658949699708513 72313389148244212274781385)
      ·
        refine ⟨54235041861183159206086039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72313389148244212274781385 54235041861183159206086039)
        ·
          refine ⟨81352562791774738809129059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54235041861183159206086039 81352562791774738809129059)
          ·
            refine ⟨122028844187662108213693589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81352562791774738809129059 122028844187662108213693589)
            ·
              refine ⟨5720102071296661322516887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122028844187662108213693589 5720102071296661322516887)
              ·
                refine ⟨8580153106944991983775331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720102071296661322516887 8580153106944991983775331)
                ·
                  refine ⟨12870229660417487975662997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8580153106944991983775331 12870229660417487975662997)
                  ·
                    refine ⟨603292015332069748859203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12870229660417487975662997 603292015332069748859203)
                    ·
                      rfl

theorem cell23_3524721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_3524721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524721 prefixEnd_3524721 := by exact prefixLift 3524721
  have htrace : WordTrace (prefixWord ++ tailWord_3524721) baseStart_3524721 baseEnd_3524721 := by
    simpa [prefixWord, tailWord_3524721, baseEnd_3524721] using wordTrace_append hprefix tailTrace_3524721
  have hstable : (prefixWord ++ tailWord_3524721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524721).length < 2 ^ (prefixWord ++ tailWord_3524721).sum := by decide
  have hdescent : baseEnd_3524721 < baseStart_3524721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524761 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3524761 : Nat := 118140960795 + 3524761 * 2 ^ 59
def prefixEnd_3524761 : Nat := 4983230072969 + 3 ^ 40 * 3524761 * 2
def baseEnd_3524761 : Nat := 1809896585222389090077425

theorem tailTrace_3524761 : CollatzResearch.WordTrace tailWord_3524761 prefixEnd_3524761 1809896585222389090077425 := by
  unfold tailWord_3524761
  simp only [CollatzResearch.WordTrace]
  refine ⟨128558595183400353097734137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85705730122266902065156091 128558595183400353097734137)
  ·
    refine ⟨96418946387550264823300603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128558595183400353097734137 96418946387550264823300603)
    ·
      refine ⟨144628419581325397234950905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96418946387550264823300603 144628419581325397234950905)
      ·
        refine ⟨108471314685994047926213179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144628419581325397234950905 108471314685994047926213179)
        ·
          refine ⟨162706972028991071889319769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108471314685994047926213179 162706972028991071889319769)
          ·
            refine ⟨122030229021743303916989827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162706972028991071889319769 122030229021743303916989827)
            ·
              refine ⟨183045343532614955875484741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122030229021743303916989827 183045343532614955875484741)
              ·
                refine ⟨34321001912365304226653389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183045343532614955875484741 34321001912365304226653389)
                ·
                  refine ⟨12870375717136989084995021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34321001912365304226653389 12870375717136989084995021)
                  ·
                    refine ⟨4826390893926370906873133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12870375717136989084995021 4826390893926370906873133)
                    ·
                      refine ⟨1809896585222389090077425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826390893926370906873133 1809896585222389090077425)
                      ·
                        rfl

theorem cell23_3524761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3524761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524761 prefixEnd_3524761 := by exact prefixLift 3524761
  have htrace : WordTrace (prefixWord ++ tailWord_3524761) baseStart_3524761 baseEnd_3524761 := by
    simpa [prefixWord, tailWord_3524761, baseEnd_3524761] using wordTrace_append hprefix tailTrace_3524761
  have hstable : (prefixWord ++ tailWord_3524761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524761).length < 2 ^ (prefixWord ++ tailWord_3524761).sum := by decide
  have hdescent : baseEnd_3524761 < baseStart_3524761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524772 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_3524772 : Nat := 118140960795 + 3524772 * 2 ^ 59
def prefixEnd_3524772 : Nat := 4983230072969 + 3 ^ 40 * 3524772 * 2
def baseEnd_3524772 : Nat := 603300744503196182346625

theorem tailTrace_3524772 : CollatzResearch.WordTrace tailWord_3524772 prefixEnd_3524772 603300744503196182346625 := by
  unfold tailWord_3524772
  simp only [CollatzResearch.WordTrace]
  refine ⟨64279498193180250988192285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85705997590907001317589713 64279498193180250988192285)
  ·
    refine ⟨24104811822442594120572107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64279498193180250988192285 24104811822442594120572107)
    ·
      refine ⟨36157217733663891180858161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24104811822442594120572107 36157217733663891180858161)
      ·
        refine ⟨27117913300247918385643621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36157217733663891180858161 27117913300247918385643621)
        ·
          refine ⟨5084608743796484697308179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27117913300247918385643621 5084608743796484697308179)
          ·
            refine ⟨7626913115694727045962269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084608743796484697308179 7626913115694727045962269)
            ·
              refine ⟨2860092418385522642235851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7626913115694727045962269 2860092418385522642235851)
              ·
                refine ⟨4290138627578283963353777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860092418385522642235851 4290138627578283963353777)
                ·
                  refine ⟨3217603970683712972515333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290138627578283963353777 3217603970683712972515333)
                  ·
                    refine ⟨603300744503196182346625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217603970683712972515333 603300744503196182346625)
                    ·
                      rfl

theorem cell23_3524772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_3524772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524772 prefixEnd_3524772 := by exact prefixLift 3524772
  have htrace : WordTrace (prefixWord ++ tailWord_3524772) baseStart_3524772 baseEnd_3524772 := by
    simpa [prefixWord, tailWord_3524772, baseEnd_3524772] using wordTrace_append hprefix tailTrace_3524772
  have hstable : (prefixWord ++ tailWord_3524772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524772).length < 2 ^ (prefixWord ++ tailWord_3524772).sum := by decide
  have hdescent : baseEnd_3524772 < baseStart_3524772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524785 : List Nat := [1, 2, 2, 5, 2, 2, 2, 7]
def baseStart_3524785 : Nat := 118140960795 + 3524785 * 2 ^ 59
def prefixEnd_3524785 : Nat := 4983230072969 + 3 ^ 40 * 3524785 * 2
def baseEnd_3524785 : Nat := 67033663287336925784345

theorem tailTrace_3524785 : CollatzResearch.WordTrace tailWord_3524785 prefixEnd_3524785 67033663287336925784345 := by
  unfold tailWord_3524785
  simp only [CollatzResearch.WordTrace]
  refine ⟨128559470535313405196607809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85706313690208936797738539 128559470535313405196607809)
  ·
    refine ⟨96419602901485053897455857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128559470535313405196607809 96419602901485053897455857)
    ·
      refine ⟨72314702176113790423091893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96419602901485053897455857 72314702176113790423091893)
      ·
        refine ⟨6779503329010667852164865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72314702176113790423091893 6779503329010667852164865)
        ·
          refine ⟨5084627496758000889123649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6779503329010667852164865 5084627496758000889123649)
          ·
            refine ⟨3813470622568500666842737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5084627496758000889123649 3813470622568500666842737)
            ·
              refine ⟨2860102966926375500132053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3813470622568500666842737 2860102966926375500132053)
              ·
                refine ⟨67033663287336925784345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2860102966926375500132053 67033663287336925784345)
                ·
                  rfl

theorem cell23_3524785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 7].length) (baseStart_3524785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524785 prefixEnd_3524785 := by exact prefixLift 3524785
  have htrace : WordTrace (prefixWord ++ tailWord_3524785) baseStart_3524785 baseEnd_3524785 := by
    simpa [prefixWord, tailWord_3524785, baseEnd_3524785] using wordTrace_append hprefix tailTrace_3524785
  have hstable : (prefixWord ++ tailWord_3524785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524785).length < 2 ^ (prefixWord ++ tailWord_3524785).sum := by decide
  have hdescent : baseEnd_3524785 < baseStart_3524785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524791 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_3524791 : Nat := 118140960795 + 3524791 * 2 ^ 59
def prefixEnd_3524791 : Nat := 4983230072969 + 3 ^ 40 * 3524791 * 2
def baseEnd_3524791 : Nat := 1809911989642023972702287

theorem tailTrace_3524791 : CollatzResearch.WordTrace tailWord_3524791 prefixEnd_3524791 1809911989642023972702287 := by
  unfold tailWord_3524791
  simp only [CollatzResearch.WordTrace]
  refine ⟨128559689373291668221326227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85706459582194445480884151 128559689373291668221326227)
  ·
    refine ⟨192839534059937502331989341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128559689373291668221326227 192839534059937502331989341)
    ·
      refine ⟨72314825272476563374496003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192839534059937502331989341 72314825272476563374496003)
      ·
        refine ⟨108472237908714845061744005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72314825272476563374496003 108472237908714845061744005)
        ·
          refine ⟨20338544607884033449077001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108472237908714845061744005 20338544607884033449077001)
          ·
            refine ⟨15253908455913025086807751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20338544607884033449077001 15253908455913025086807751)
            ·
              refine ⟨22880862683869537630211627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15253908455913025086807751 22880862683869537630211627)
              ·
                refine ⟨34321294025804306445317441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22880862683869537630211627 34321294025804306445317441)
                ·
                  refine ⟨25740970519353229833988081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34321294025804306445317441 25740970519353229833988081)
                  ·
                    refine ⟨19305727889514922375491061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25740970519353229833988081 19305727889514922375491061)
                    ·
                      refine ⟨1809911989642023972702287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19305727889514922375491061 1809911989642023972702287)
                      ·
                        rfl

theorem cell23_3524791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_3524791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524791 prefixEnd_3524791 := by exact prefixLift 3524791
  have htrace : WordTrace (prefixWord ++ tailWord_3524791) baseStart_3524791 baseEnd_3524791 := by
    simpa [prefixWord, tailWord_3524791, baseEnd_3524791] using wordTrace_append hprefix tailTrace_3524791
  have hstable : (prefixWord ++ tailWord_3524791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524791).length < 2 ^ (prefixWord ++ tailWord_3524791).sum := by decide
  have hdescent : baseEnd_3524791 < baseStart_3524791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524796 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3524796 : Nat := 118140960795 + 3524796 * 2 ^ 59
def prefixEnd_3524796 : Nat := 4983230072969 + 3 ^ 40 * 3524796 * 2
def baseEnd_3524796 : Nat := 1809914557045296453139765

theorem tailTrace_3524796 : CollatzResearch.WordTrace tailWord_3524796 prefixEnd_3524796 1809914557045296453139765 := by
  unfold tailWord_3524796
  simp only [CollatzResearch.WordTrace]
  refine ⟨64279935869136777037629121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85706581158849036050172161 64279935869136777037629121)
  ·
    refine ⟨48209951901852582778221841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64279935869136777037629121 48209951901852582778221841)
    ·
      refine ⟨36157463926389437083666381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48209951901852582778221841 36157463926389437083666381)
      ·
        refine ⟨13559048972396038906374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36157463926389437083666381 13559048972396038906374893)
        ·
          refine ⟨5084643364648514589890585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13559048972396038906374893 5084643364648514589890585)
          ·
            refine ⟨3813482523486385942417939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5084643364648514589890585 3813482523486385942417939)
            ·
              refine ⟨5720223785229578913626909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813482523486385942417939 5720223785229578913626909)
              ·
                refine ⟨2145083919461092092610091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5720223785229578913626909 2145083919461092092610091)
                ·
                  refine ⟨3217625879191638138915137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145083919461092092610091 3217625879191638138915137)
                  ·
                    refine ⟨2413219409393728604186353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217625879191638138915137 2413219409393728604186353)
                    ·
                      refine ⟨1809914557045296453139765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413219409393728604186353 1809914557045296453139765)
                      ·
                        rfl

theorem cell23_3524796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3524796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524796 prefixEnd_3524796 := by exact prefixLift 3524796
  have htrace : WordTrace (prefixWord ++ tailWord_3524796) baseStart_3524796 baseEnd_3524796 := by
    simpa [prefixWord, tailWord_3524796, baseEnd_3524796] using wordTrace_append hprefix tailTrace_3524796
  have hstable : (prefixWord ++ tailWord_3524796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524796).length < 2 ^ (prefixWord ++ tailWord_3524796).sum := by decide
  have hdescent : baseEnd_3524796 < baseStart_3524796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524805 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_3524805 : Nat := 118140960795 + 3524805 * 2 ^ 59
def prefixEnd_3524805 : Nat := 4983230072969 + 3 ^ 40 * 3524805 * 2
def baseEnd_3524805 : Nat := 1809919178371186917927223

theorem tailTrace_3524805 : CollatzResearch.WordTrace tailWord_3524805 prefixEnd_3524805 1809919178371186917927223 := by
  unfold tailWord_3524805
  simp only [CollatzResearch.WordTrace]
  refine ⟨128560199995240948612335869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85706799996827299074890579 128560199995240948612335869)
  ·
    refine ⟨48210074998215355729625951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128560199995240948612335869 48210074998215355729625951)
    ·
      refine ⟨72315112497323033594438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48210074998215355729625951 72315112497323033594438927)
      ·
        refine ⟨108472668745984550391658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72315112497323033594438927 108472668745984550391658391)
        ·
          refine ⟨162709003118976825587487587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108472668745984550391658391 162709003118976825587487587)
          ·
            refine ⟨244063504678465238381231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162709003118976825587487587 244063504678465238381231381)
            ·
              refine ⟨11440476781803058049120221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244063504678465238381231381 11440476781803058049120221)
              ·
                refine ⟨4290178793176146768420083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11440476781803058049120221 4290178793176146768420083)
                ·
                  refine ⟨6435268189764220152630125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290178793176146768420083 6435268189764220152630125)
                  ·
                    refine ⟨2413225571161582557236297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6435268189764220152630125 2413225571161582557236297)
                    ·
                      refine ⟨1809919178371186917927223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413225571161582557236297 1809919178371186917927223)
                      ·
                        rfl

theorem cell23_3524805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_3524805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524805 prefixEnd_3524805 := by exact prefixLift 3524805
  have htrace : WordTrace (prefixWord ++ tailWord_3524805) baseStart_3524805 baseEnd_3524805 := by
    simpa [prefixWord, tailWord_3524805, baseEnd_3524805] using wordTrace_append hprefix tailTrace_3524805
  have hstable : (prefixWord ++ tailWord_3524805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524805).length < 2 ^ (prefixWord ++ tailWord_3524805).sum := by decide
  have hdescent : baseEnd_3524805 < baseStart_3524805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524829 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3524829 : Nat := 118140960795 + 3524829 * 2 ^ 59
def prefixEnd_3524829 : Nat := 4983230072969 + 3 ^ 40 * 3524829 * 2
def baseEnd_3524829 : Nat := 1809931501906894824027113

theorem tailTrace_3524829 : CollatzResearch.WordTrace tailWord_3524829 prefixEnd_3524829 1809931501906894824027113 := by
  unfold tailWord_3524829
  simp only [CollatzResearch.WordTrace]
  refine ⟨128561075347154000711209541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85707383564769333807473027 128561075347154000711209541)
  ·
    refine ⟨24105201627591375133351789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128561075347154000711209541 24105201627591375133351789)
    ·
      refine ⟨9039450610346765675006921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24105201627591375133351789 9039450610346765675006921)
      ·
        refine ⟨6779587957760074256255191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9039450610346765675006921 6779587957760074256255191)
        ·
          refine ⟨10169381936640111384382787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779587957760074256255191 10169381936640111384382787)
          ·
            refine ⟨15254072904960167076574181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169381936640111384382787 15254072904960167076574181)
            ·
              refine ⟨2860138669680031326857659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15254072904960167076574181 2860138669680031326857659)
              ·
                refine ⟨4290208004520046990286489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860138669680031326857659 4290208004520046990286489)
                ·
                  refine ⟨3217656003390035242714867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290208004520046990286489 3217656003390035242714867)
                  ·
                    refine ⟨4826484005085052864072301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217656003390035242714867 4826484005085052864072301)
                    ·
                      refine ⟨1809931501906894824027113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826484005085052864072301 1809931501906894824027113)
                      ·
                        rfl

theorem cell23_3524829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3524829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524829 prefixEnd_3524829 := by exact prefixLift 3524829
  have htrace : WordTrace (prefixWord ++ tailWord_3524829) baseStart_3524829 baseEnd_3524829 := by
    simpa [prefixWord, tailWord_3524829, baseEnd_3524829] using wordTrace_append hprefix tailTrace_3524829
  have hstable : (prefixWord ++ tailWord_3524829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524829).length < 2 ^ (prefixWord ++ tailWord_3524829).sum := by decide
  have hdescent : baseEnd_3524829 < baseStart_3524829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524831 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3524831 : Nat := 118140960795 + 3524831 * 2 ^ 59
def prefixEnd_3524831 : Nat := 4983230072969 + 3 ^ 40 * 3524831 * 2
def baseEnd_3524831 : Nat := 1809932528868203816202103

theorem tailTrace_3524831 : CollatzResearch.WordTrace tailWord_3524831 prefixEnd_3524831 1809932528868203816202103 := by
  unfold tailWord_3524831
  simp only [CollatzResearch.WordTrace]
  refine ⟨128561148293146755052782347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85707432195431170035188231 128561148293146755052782347)
  ·
    refine ⟨192841722439720132579173521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128561148293146755052782347 192841722439720132579173521)
    ·
      refine ⟨144631291829790099434380141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192841722439720132579173521 144631291829790099434380141)
      ·
        refine ⟨54236734436171287287892553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144631291829790099434380141 54236734436171287287892553)
        ·
          refine ⟨40677550827128465465919415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54236734436171287287892553 40677550827128465465919415)
          ·
            refine ⟨61016326240692698198879123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40677550827128465465919415 61016326240692698198879123)
            ·
              refine ⟨91524489361039047298318685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61016326240692698198879123 91524489361039047298318685)
              ·
                refine ⟨34321683510389642736869507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91524489361039047298318685 34321683510389642736869507)
                ·
                  refine ⟨51482525265584464105304261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34321683510389642736869507 51482525265584464105304261)
                  ·
                    refine ⟨9652973487297087019744549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51482525265584464105304261 9652973487297087019744549)
                    ·
                      refine ⟨1809932528868203816202103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9652973487297087019744549 1809932528868203816202103)
                      ·
                        rfl

theorem cell23_3524831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3524831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524831 prefixEnd_3524831 := by exact prefixLift 3524831
  have htrace : WordTrace (prefixWord ++ tailWord_3524831) baseStart_3524831 baseEnd_3524831 := by
    simpa [prefixWord, tailWord_3524831, baseEnd_3524831] using wordTrace_append hprefix tailTrace_3524831
  have hstable : (prefixWord ++ tailWord_3524831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524831).length < 2 ^ (prefixWord ++ tailWord_3524831).sum := by decide
  have hdescent : baseEnd_3524831 < baseStart_3524831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524839 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3524839 : Nat := 118140960795 + 3524839 * 2 ^ 59
def prefixEnd_3524839 : Nat := 4983230072969 + 3 ^ 40 * 3524839 * 2
def baseEnd_3524839 : Nat := 1809936636713439784902067

theorem tailTrace_3524839 : CollatzResearch.WordTrace tailWord_3524839 prefixEnd_3524839 1809936636713439784902067 := by
  unfold tailWord_3524839
  simp only [CollatzResearch.WordTrace]
  refine ⟨128561440077117772419073571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85707626718078514946049047 128561440077117772419073571)
  ·
    refine ⟨192842160115676658628610357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128561440077117772419073571 192842160115676658628610357)
    ·
      refine ⟨18078952510844686746432221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192842160115676658628610357 18078952510844686746432221)
      ·
        refine ⟨6779607191566757529912083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18078952510844686746432221 6779607191566757529912083)
        ·
          refine ⟨10169410787350136294868125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779607191566757529912083 10169410787350136294868125)
          ·
            refine ⟨3813529045256301110575547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10169410787350136294868125 3813529045256301110575547)
            ·
              refine ⟨5720293567884451665863321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813529045256301110575547 5720293567884451665863321)
              ·
                refine ⟨4290220175913338749397491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720293567884451665863321 4290220175913338749397491)
                ·
                  refine ⟨6435330263870008124096237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290220175913338749397491 6435330263870008124096237)
                  ·
                    refine ⟨2413248848951253046536089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6435330263870008124096237 2413248848951253046536089)
                    ·
                      refine ⟨1809936636713439784902067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413248848951253046536089 1809936636713439784902067)
                      ·
                        rfl

theorem cell23_3524839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3524839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524839 prefixEnd_3524839 := by exact prefixLift 3524839
  have htrace : WordTrace (prefixWord ++ tailWord_3524839) baseStart_3524839 baseEnd_3524839 := by
    simpa [prefixWord, tailWord_3524839, baseEnd_3524839] using wordTrace_append hprefix tailTrace_3524839
  have hstable : (prefixWord ++ tailWord_3524839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524839).length < 2 ^ (prefixWord ++ tailWord_3524839).sum := by decide
  have hdescent : baseEnd_3524839 < baseStart_3524839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524909 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 5]
def baseStart_3524909 : Nat := 118140960795 + 3524909 * 2 ^ 59
def prefixEnd_3524909 : Nat := 4983230072969 + 3 ^ 40 * 3524909 * 2
def baseEnd_3524909 : Nat := 201108064484361612336305

theorem tailTrace_3524909 : CollatzResearch.WordTrace tailWord_3524909 prefixEnd_3524909 201108064484361612336305 := by
  unfold tailWord_3524909
  simp only [CollatzResearch.WordTrace]
  refine ⟨128563993186864174374121781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85709328791242782916081187 128563993186864174374121781)
  ·
    refine ⟨12052874361268516347573917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128563993186864174374121781 12052874361268516347573917)
    ·
      refine ⟨4519827885475693630340219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12052874361268516347573917 4519827885475693630340219)
      ·
        refine ⟨6779741828213540445510329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519827885475693630340219 6779741828213540445510329)
        ·
          refine ⟨5084806371160155334132747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6779741828213540445510329 5084806371160155334132747)
          ·
            refine ⟨7627209556740233001199121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084806371160155334132747 7627209556740233001199121)
            ·
              refine ⟨5720407167555174750899341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627209556740233001199121 5720407167555174750899341)
              ·
                refine ⟨2145152687833190531587253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5720407167555174750899341 2145152687833190531587253)
                ·
                  refine ⟨201108064484361612336305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2145152687833190531587253 201108064484361612336305)
                  ·
                    rfl

theorem cell23_3524909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_3524909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524909 prefixEnd_3524909 := by exact prefixLift 3524909
  have htrace : WordTrace (prefixWord ++ tailWord_3524909) baseStart_3524909 baseEnd_3524909 := by
    simpa [prefixWord, tailWord_3524909, baseEnd_3524909] using wordTrace_append hprefix tailTrace_3524909
  have hstable : (prefixWord ++ tailWord_3524909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524909).length < 2 ^ (prefixWord ++ tailWord_3524909).sum := by decide
  have hdescent : baseEnd_3524909 < baseStart_3524909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524935 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3524935 : Nat := 118140960795 + 3524935 * 2 ^ 59
def prefixEnd_3524935 : Nat := 4983230072969 + 3 ^ 40 * 3524935 * 2
def baseEnd_3524935 : Nat := 603328643618757136433875

theorem tailTrace_3524935 : CollatzResearch.WordTrace tailWord_3524935 prefixEnd_3524935 603328643618757136433875 := by
  unfold tailWord_3524935
  simp only [CollatzResearch.WordTrace]
  refine ⟨128564941484769980814568259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85709960989846653876378839 128564941484769980814568259)
  ·
    refine ⟨192847412227154971221852389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128564941484769980814568259 192847412227154971221852389)
    ·
      refine ⟨36158889792591557104097323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192847412227154971221852389 36158889792591557104097323)
      ·
        refine ⟨54238334688887335656145985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36158889792591557104097323 54238334688887335656145985)
        ·
          refine ⟨40678751016665501742109489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54238334688887335656145985 40678751016665501742109489)
          ·
            refine ⟨30509063262499126306582117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40678751016665501742109489 30509063262499126306582117)
            ·
              refine ⟨5720449361718586182484147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30509063262499126306582117 5720449361718586182484147)
              ·
                refine ⟨8580674042577879273726221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720449361718586182484147 8580674042577879273726221)
                ·
                  refine ⟨3217752765966704727647333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8580674042577879273726221 3217752765966704727647333)
                  ·
                    refine ⟨603328643618757136433875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217752765966704727647333 603328643618757136433875)
                    ·
                      rfl

theorem cell23_3524935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3524935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524935 prefixEnd_3524935 := by exact prefixLift 3524935
  have htrace : WordTrace (prefixWord ++ tailWord_3524935) baseStart_3524935 baseEnd_3524935 := by
    simpa [prefixWord, tailWord_3524935, baseEnd_3524935] using wordTrace_append hprefix tailTrace_3524935
  have hstable : (prefixWord ++ tailWord_3524935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524935).length < 2 ^ (prefixWord ++ tailWord_3524935).sum := by decide
  have hdescent : baseEnd_3524935 < baseStart_3524935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525012 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3525012 : Nat := 118140960795 + 3525012 * 2 ^ 59
def prefixEnd_3525012 : Nat := 4983230072969 + 3 ^ 40 * 3525012 * 2
def baseEnd_3525012 : Nat := 603341822955555869346257

theorem tailTrace_3525012 : CollatzResearch.WordTrace tailWord_3525012 prefixEnd_3525012 603341822955555869346257 := by
  unfold tailWord_3525012
  simp only [CollatzResearch.WordTrace]
  refine ⟨64283874952745511482560645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85711833270327348643414193 64283874952745511482560645)
  ·
    refine ⟨12053226553639783402980121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64283874952745511482560645 12053226553639783402980121)
    ·
      refine ⟨9039919915229837552235091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12053226553639783402980121 9039919915229837552235091)
      ·
        refine ⟨13559879872844756328352637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039919915229837552235091 13559879872844756328352637)
        ·
          refine ⟨5084954952316783623132239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13559879872844756328352637 5084954952316783623132239)
          ·
            refine ⟨7627432428475175434698359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084954952316783623132239 7627432428475175434698359)
            ·
              refine ⟨11441148642712763152047539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627432428475175434698359 11441148642712763152047539)
              ·
                refine ⟨17161722964069144728071309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11441148642712763152047539 17161722964069144728071309)
                ·
                  refine ⟨6435646111525929273026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161722964069144728071309 6435646111525929273026741)
                  ·
                    refine ⟨603341822955555869346257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6435646111525929273026741 603341822955555869346257)
                    ·
                      rfl

theorem cell23_3525012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3525012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525012 prefixEnd_3525012 := by exact prefixLift 3525012
  have htrace : WordTrace (prefixWord ++ tailWord_3525012) baseStart_3525012 baseEnd_3525012 := by
    simpa [prefixWord, tailWord_3525012, baseEnd_3525012] using wordTrace_append hprefix tailTrace_3525012
  have hstable : (prefixWord ++ tailWord_3525012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525012).length < 2 ^ (prefixWord ++ tailWord_3525012).sum := by decide
  have hdescent : baseEnd_3525012 < baseStart_3525012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525015 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_3525015 : Nat := 118140960795 + 3525015 * 2 ^ 59
def prefixEnd_3525015 : Nat := 4983230072969 + 3 ^ 40 * 3525015 * 2
def baseEnd_3525015 : Nat := 1810027009308631096301257

theorem tailTrace_3525015 : CollatzResearch.WordTrace tailWord_3525015 prefixEnd_3525015 1810027009308631096301257 := by
  unfold tailWord_3525015
  simp only [CollatzResearch.WordTrace]
  refine ⟨128567859324480154477480499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85711906216320102984986999 128567859324480154477480499)
  ·
    refine ⟨192851788986720231716220749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128567859324480154477480499 192851788986720231716220749)
    ·
      refine ⟨72319420870020086893582781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192851788986720231716220749 72319420870020086893582781)
      ·
        refine ⟨27119782826257532585093543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72319420870020086893582781 27119782826257532585093543)
        ·
          refine ⟨40679674239386298877640315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27119782826257532585093543 40679674239386298877640315)
          ·
            refine ⟨61019511359079448316460473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40679674239386298877640315 61019511359079448316460473)
            ·
              refine ⟨45764633519309586237345355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61019511359079448316460473 45764633519309586237345355)
              ·
                refine ⟨68646950278964379356018033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45764633519309586237345355 68646950278964379356018033)
                ·
                  refine ⟨51485212709223284517013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68646950278964379356018033 51485212709223284517013525)
                  ·
                    refine ⟨2413369345744841461735009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51485212709223284517013525 2413369345744841461735009)
                    ·
                      refine ⟨1810027009308631096301257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413369345744841461735009 1810027009308631096301257)
                      ·
                        rfl

theorem cell23_3525015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_3525015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525015 prefixEnd_3525015 := by exact prefixLift 3525015
  have htrace : WordTrace (prefixWord ++ tailWord_3525015) baseStart_3525015 baseEnd_3525015 := by
    simpa [prefixWord, tailWord_3525015, baseEnd_3525015] using wordTrace_append hprefix tailTrace_3525015
  have hstable : (prefixWord ++ tailWord_3525015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525015).length < 2 ^ (prefixWord ++ tailWord_3525015).sum := by decide
  have hdescent : baseEnd_3525015 < baseStart_3525015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525042 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3525042 : Nat := 118140960795 + 3525042 * 2 ^ 59
def prefixEnd_3525042 : Nat := 4983230072969 + 3 ^ 40 * 3525042 * 2
def baseEnd_3525042 : Nat := 603346957762100830221211

theorem tailTrace_3525042 : CollatzResearch.WordTrace tailWord_3525042 prefixEnd_3525042 603346957762100830221211 := by
  unfold tailWord_3525042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142211023845584522178345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85712562730254892059142253 32142211023845584522178345)
  ·
    refine ⟨24106658267884188391633759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32142211023845584522178345 24106658267884188391633759)
    ·
      refine ⟨36159987401826282587450639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24106658267884188391633759 36159987401826282587450639)
      ·
        refine ⟨54239981102739423881175959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36159987401826282587450639 54239981102739423881175959)
        ·
          refine ⟨81359971654109135821763939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54239981102739423881175959 81359971654109135821763939)
          ·
            refine ⟨122039957481163703732645909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81359971654109135821763939 122039957481163703732645909)
            ·
              refine ⟨5720623006929548612467777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122039957481163703732645909 5720623006929548612467777)
              ·
                refine ⟨4290467255197161459350833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720623006929548612467777 4290467255197161459350833)
                ·
                  refine ⟨3217850441397871094513125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290467255197161459350833 3217850441397871094513125)
                  ·
                    refine ⟨603346957762100830221211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217850441397871094513125 603346957762100830221211)
                    ·
                      rfl

theorem cell23_3525042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3525042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525042 prefixEnd_3525042 := by exact prefixLift 3525042
  have htrace : WordTrace (prefixWord ++ tailWord_3525042) baseStart_3525042 baseEnd_3525042 := by
    simpa [prefixWord, tailWord_3525042, baseEnd_3525042] using wordTrace_append hprefix tailTrace_3525042
  have hstable : (prefixWord ++ tailWord_3525042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525042).length < 2 ^ (prefixWord ++ tailWord_3525042).sum := by decide
  have hdescent : baseEnd_3525042 < baseStart_3525042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525052 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3525052 : Nat := 118140960795 + 3525052 * 2 ^ 59
def prefixEnd_3525052 : Nat := 4983230072969 + 3 ^ 40 * 3525052 * 2
def baseEnd_3525052 : Nat := 1810046008092847451538587

theorem tailTrace_3525052 : CollatzResearch.WordTrace tailWord_3525052 prefixEnd_3525052 1810046008092847451538587 := by
  unfold tailWord_3525052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64284604412673054898288705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85712805883564073197718273 64284604412673054898288705)
  ·
    refine ⟨48213453309504791173716529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64284604412673054898288705 48213453309504791173716529)
    ·
      refine ⟨36160089982128593380287397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48213453309504791173716529 36160089982128593380287397)
      ·
        refine ⟨6780016871649111258803887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36160089982128593380287397 6780016871649111258803887)
        ·
          refine ⟨10170025307473666888205831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780016871649111258803887 10170025307473666888205831)
          ·
            refine ⟨15255037961210500332308747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170025307473666888205831 15255037961210500332308747)
            ·
              refine ⟨22882556941815750498463121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15255037961210500332308747 22882556941815750498463121)
              ·
                refine ⟨17161917706361812873847341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22882556941815750498463121 17161917706361812873847341)
                ·
                  refine ⟨6435719139885679827692753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161917706361812873847341 6435719139885679827692753)
                  ·
                    refine ⟨4826789354914259870769565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6435719139885679827692753 4826789354914259870769565)
                    ·
                      refine ⟨1810046008092847451538587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826789354914259870769565 1810046008092847451538587)
                      ·
                        rfl

theorem cell23_3525052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3525052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525052 prefixEnd_3525052 := by exact prefixLift 3525052
  have htrace : WordTrace (prefixWord ++ tailWord_3525052) baseStart_3525052 baseEnd_3525052 := by
    simpa [prefixWord, tailWord_3525052, baseEnd_3525052] using wordTrace_append hprefix tailTrace_3525052
  have hstable : (prefixWord ++ tailWord_3525052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525052).length < 2 ^ (prefixWord ++ tailWord_3525052).sum := by decide
  have hdescent : baseEnd_3525052 < baseStart_3525052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525065 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_3525065 : Nat := 118140960795 + 3525065 * 2 ^ 59
def prefixEnd_3525065 : Nat := 4983230072969 + 3 ^ 40 * 3525065 * 2
def baseEnd_3525065 : Nat := 1810052683341355900676027

theorem tailTrace_3525065 : CollatzResearch.WordTrace tailWord_3525065 prefixEnd_3525065 1810052683341355900676027 := by
  unfold tailWord_3525065
  simp only [CollatzResearch.WordTrace]
  refine ⟨128569682974299013016800649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85713121982866008677867099 128569682974299013016800649)
  ·
    refine ⟨96427262230724259762600487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128569682974299013016800649 96427262230724259762600487)
    ·
      refine ⟨144640893346086389643900731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96427262230724259762600487 144640893346086389643900731)
      ·
        refine ⟨216961340019129584465851097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144640893346086389643900731 216961340019129584465851097)
        ·
          refine ⟨162721005014347188349388323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216961340019129584465851097 162721005014347188349388323)
          ·
            refine ⟨244081507521520782524082485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162721005014347188349388323 244081507521520782524082485)
            ·
              refine ⟨22882641330142573361632733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244081507521520782524082485 22882641330142573361632733)
              ·
                refine ⟨8580990498803465010612275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22882641330142573361632733 8580990498803465010612275)
                ·
                  refine ⟨12871485748205197515918413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8580990498803465010612275 12871485748205197515918413)
                  ·
                    refine ⟨4826807155576949068469405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12871485748205197515918413 4826807155576949068469405)
                    ·
                      refine ⟨1810052683341355900676027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826807155576949068469405 1810052683341355900676027)
                      ·
                        rfl

theorem cell23_3525065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_3525065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525065 prefixEnd_3525065 := by exact prefixLift 3525065
  have htrace : WordTrace (prefixWord ++ tailWord_3525065) baseStart_3525065 baseEnd_3525065 := by
    simpa [prefixWord, tailWord_3525065, baseEnd_3525065] using wordTrace_append hprefix tailTrace_3525065
  have hstable : (prefixWord ++ tailWord_3525065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525065).length < 2 ^ (prefixWord ++ tailWord_3525065).sum := by decide
  have hdescent : baseEnd_3525065 < baseStart_3525065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525082 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_3525082 : Nat := 118140960795 + 3525082 * 2 ^ 59
def prefixEnd_3525082 : Nat := 4983230072969 + 3 ^ 40 * 3525082 * 2
def baseEnd_3525082 : Nat := 1810061412512482334163449

theorem tailTrace_3525082 : CollatzResearch.WordTrace tailWord_3525082 prefixEnd_3525082 1810061412512482334163449 := by
  unfold tailWord_3525082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142575753809356230042375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85713535343491616613446333 32142575753809356230042375)
  ·
    refine ⟨48213863630714034345063563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32142575753809356230042375 48213863630714034345063563)
    ·
      refine ⟨72320795446071051517595345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48213863630714034345063563 72320795446071051517595345)
      ·
        refine ⟨54240596584553288638196509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72320795446071051517595345 54240596584553288638196509)
        ·
          refine ⟨20340223719207483239323691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54240596584553288638196509 20340223719207483239323691)
          ·
            refine ⟨30510335578811224858985537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20340223719207483239323691 30510335578811224858985537)
            ·
              refine ⟨22882751684108418644239153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30510335578811224858985537 22882751684108418644239153)
              ·
                refine ⟨17162063763081313983179365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22882751684108418644239153 17162063763081313983179365)
                ·
                  refine ⟨3217886955577746371846131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17162063763081313983179365 3217886955577746371846131)
                  ·
                    refine ⟨4826830433366619557769197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217886955577746371846131 4826830433366619557769197)
                    ·
                      refine ⟨1810061412512482334163449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826830433366619557769197 1810061412512482334163449)
                      ·
                        rfl

theorem cell23_3525082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_3525082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525082 prefixEnd_3525082 := by exact prefixLift 3525082
  have htrace : WordTrace (prefixWord ++ tailWord_3525082) baseStart_3525082 baseEnd_3525082 := by
    simpa [prefixWord, tailWord_3525082, baseEnd_3525082] using wordTrace_append hprefix tailTrace_3525082
  have hstable : (prefixWord ++ tailWord_3525082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525082).length < 2 ^ (prefixWord ++ tailWord_3525082).sum := by decide
  have hdescent : baseEnd_3525082 < baseStart_3525082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525125 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_3525125 : Nat := 118140960795 + 3525125 * 2 ^ 59
def prefixEnd_3525125 : Nat := 4983230072969 + 3 ^ 40 * 3525125 * 2
def baseEnd_3525125 : Nat := 1810083492180625665925751

theorem tailTrace_3525125 : CollatzResearch.WordTrace tailWord_3525125 prefixEnd_3525125 1810083492180625665925751 := by
  unfold tailWord_3525125
  simp only [CollatzResearch.WordTrace]
  refine ⟨128571871354081643263984829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85714580902721095509323219 128571871354081643263984829)
  ·
    refine ⟨48214451757780616223994311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128571871354081643263984829 48214451757780616223994311)
    ·
      refine ⟨72321677636670924335991467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48214451757780616223994311 72321677636670924335991467)
      ·
        refine ⟨108482516455006386503987201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72321677636670924335991467 108482516455006386503987201)
        ·
          refine ⟨81361887341254789877990401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108482516455006386503987201 81361887341254789877990401)
          ·
            refine ⟨61021415505941092408492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81361887341254789877990401 61021415505941092408492801)
            ·
              refine ⟨45766061629455819306369601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61021415505941092408492801 45766061629455819306369601)
              ·
                refine ⟨34324546222091864479777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45766061629455819306369601 34324546222091864479777201)
                ·
                  refine ⟨25743409666568898359832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34324546222091864479777201 25743409666568898359832901)
                  ·
                    refine ⟨4826889312481668442468669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25743409666568898359832901 4826889312481668442468669)
                    ·
                      refine ⟨1810083492180625665925751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4826889312481668442468669 1810083492180625665925751)
                      ·
                        rfl

theorem cell23_3525125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_3525125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525125 prefixEnd_3525125 := by exact prefixLift 3525125
  have htrace : WordTrace (prefixWord ++ tailWord_3525125) baseStart_3525125 baseEnd_3525125 := by
    simpa [prefixWord, tailWord_3525125, baseEnd_3525125] using wordTrace_append hprefix tailTrace_3525125
  have hstable : (prefixWord ++ tailWord_3525125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525125).length < 2 ^ (prefixWord ++ tailWord_3525125).sum := by decide
  have hdescent : baseEnd_3525125 < baseStart_3525125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525162 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_3525162 : Nat := 118140960795 + 3525162 * 2 ^ 59
def prefixEnd_3525162 : Nat := 4983230072969 + 3 ^ 40 * 3525162 * 2
def baseEnd_3525162 : Nat := 201122498996093557907009

theorem tailTrace_3525162 : CollatzResearch.WordTrace tailWord_3525162 prefixEnd_3525162 201122498996093557907009 := by
  unfold tailWord_3525162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143305213736899645770435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85715480569965065722054493 32143305213736899645770435)
  ·
    refine ⟨48214957820605349468655653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32143305213736899645770435 48214957820605349468655653)
    ·
      refine ⟨9040304591363503025372935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48214957820605349468655653 9040304591363503025372935)
      ·
        refine ⟨13560456887045254538059403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040304591363503025372935 13560456887045254538059403)
        ·
          refine ⟨20340685330567881807089105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13560456887045254538059403 20340685330567881807089105)
          ·
            refine ⟨15255513997925911355316829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20340685330567881807089105 15255513997925911355316829)
            ·
              refine ⟨5720817749222216758243811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15255513997925911355316829 5720817749222216758243811)
              ·
                refine ⟨8581226623833325137365717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720817749222216758243811 8581226623833325137365717)
                ·
                  refine ⟨201122498996093557907009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8581226623833325137365717 201122498996093557907009)
                  ·
                    rfl

theorem cell23_3525162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_3525162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525162 prefixEnd_3525162 := by exact prefixLift 3525162
  have htrace : WordTrace (prefixWord ++ tailWord_3525162) baseStart_3525162 baseEnd_3525162 := by
    simpa [prefixWord, tailWord_3525162, baseEnd_3525162] using wordTrace_append hprefix tailTrace_3525162
  have hstable : (prefixWord ++ tailWord_3525162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525162).length < 2 ^ (prefixWord ++ tailWord_3525162).sum := by decide
  have hdescent : baseEnd_3525162 < baseStart_3525162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525175 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 4, 5]
def baseStart_3525175 : Nat := 118140960795 + 3525175 * 2 ^ 59
def prefixEnd_3525175 : Nat := 4983230072969 + 3 ^ 40 * 3525175 * 2
def baseEnd_3525175 : Nat := 603369722071116823433507

theorem tailTrace_3525175 : CollatzResearch.WordTrace tailWord_3525175 prefixEnd_3525175 603369722071116823433507 := by
  unfold tailWord_3525175
  simp only [CollatzResearch.WordTrace]
  refine ⟨128573695003900501803304979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85715796669267001202203319 128573695003900501803304979)
  ·
    refine ⟨192860542505850752704957469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128573695003900501803304979 192860542505850752704957469)
    ·
      refine ⟨72322703439694032264359051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192860542505850752704957469 72322703439694032264359051)
      ·
        refine ⟨108484055159541048396538577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72322703439694032264359051 108484055159541048396538577)
        ·
          refine ⟨81363041369655786297403933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108484055159541048396538577 81363041369655786297403933)
          ·
            refine ⟨30511140513620919861526475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81363041369655786297403933 30511140513620919861526475)
            ·
              refine ⟨45766710770431379792289713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30511140513620919861526475 45766710770431379792289713)
              ·
                refine ⟨34325033077823534844217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45766710770431379792289713 34325033077823534844217285)
                ·
                  refine ⟨6435943702091912783290741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34325033077823534844217285 6435943702091912783290741)
                  ·
                    refine ⟨603369722071116823433507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6435943702091912783290741 603369722071116823433507)
                    ·
                      rfl

theorem cell23_3525175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_3525175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525175 prefixEnd_3525175 := by exact prefixLift 3525175
  have htrace : WordTrace (prefixWord ++ tailWord_3525175) baseStart_3525175 baseEnd_3525175 := by
    simpa [prefixWord, tailWord_3525175, baseEnd_3525175] using wordTrace_append hprefix tailTrace_3525175
  have hstable : (prefixWord ++ tailWord_3525175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525175).length < 2 ^ (prefixWord ++ tailWord_3525175).sum := by decide
  have hdescent : baseEnd_3525175 < baseStart_3525175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525195 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_3525195 : Nat := 118140960795 + 3525195 * 2 ^ 59
def prefixEnd_3525195 : Nat := 4983230072969 + 3 ^ 40 * 3525195 * 2
def baseEnd_3525195 : Nat := 1810119435826440392050429

theorem tailTrace_3525195 : CollatzResearch.WordTrace tailWord_3525195 prefixEnd_3525195 1810119435826440392050429 := by
  unfold tailWord_3525195
  simp only [CollatzResearch.WordTrace]
  refine ⟨128574424463828045219033039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85716282975885363479355359 128574424463828045219033039)
  ·
    refine ⟨192861636695742067828549559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128574424463828045219033039 192861636695742067828549559)
    ·
      refine ⟨289292455043613101742824339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192861636695742067828549559 289292455043613101742824339)
      ·
        refine ⟨433938682565419652614236509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289292455043613101742824339 433938682565419652614236509)
        ·
          refine ⟨162727005962032369730338691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433938682565419652614236509 162727005962032369730338691)
          ·
            refine ⟨244090508943048554595508037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162727005962032369730338691 244090508943048554595508037)
            ·
              refine ⟨45766970426821603986657757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244090508943048554595508037 45766970426821603986657757)
              ·
                refine ⟨17162613910058101494996659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45766970426821603986657757 17162613910058101494996659)
                ·
                  refine ⟨25743920865087152242494989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17162613910058101494996659 25743920865087152242494989)
                  ·
                    refine ⟨9653970324407682090935621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25743920865087152242494989 9653970324407682090935621)
                    ·
                      refine ⟨1810119435826440392050429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9653970324407682090935621 1810119435826440392050429)
                      ·
                        rfl

theorem cell23_3525195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_3525195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525195 prefixEnd_3525195 := by exact prefixLift 3525195
  have htrace : WordTrace (prefixWord ++ tailWord_3525195) baseStart_3525195 baseEnd_3525195 := by
    simpa [prefixWord, tailWord_3525195, baseEnd_3525195] using wordTrace_append hprefix tailTrace_3525195
  have hstable : (prefixWord ++ tailWord_3525195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525195).length < 2 ^ (prefixWord ++ tailWord_3525195).sum := by decide
  have hdescent : baseEnd_3525195 < baseStart_3525195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525225 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3525225 : Nat := 118140960795 + 3525225 * 2 ^ 59
def prefixEnd_3525225 : Nat := 4983230072969 + 3 ^ 40 * 3525225 * 2
def baseEnd_3525225 : Nat := 1810134840246075274675291

theorem tailTrace_3525225 : CollatzResearch.WordTrace tailWord_3525225 prefixEnd_3525225 1810134840246075274675291 := by
  unfold tailWord_3525225
  simp only [CollatzResearch.WordTrace]
  refine ⟨128575518653719360342625129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85717012435812906895083419 128575518653719360342625129)
  ·
    refine ⟨96431638990289520256968847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128575518653719360342625129 96431638990289520256968847)
    ·
      refine ⟨144647458485434280385453271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96431638990289520256968847 144647458485434280385453271)
      ·
        refine ⟨216971187728151420578179907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144647458485434280385453271 216971187728151420578179907)
        ·
          refine ⟨325456781592227130867269861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216971187728151420578179907 325456781592227130867269861)
          ·
            refine ⟨61023146548542587037613099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325456781592227130867269861 61023146548542587037613099)
            ·
              refine ⟨91534719822813880556419649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61023146548542587037613099 91534719822813880556419649)
              ·
                refine ⟨68651039867110410417314737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91534719822813880556419649 68651039867110410417314737)
                ·
                  refine ⟨51488279900332807812986053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68651039867110410417314737 51488279900332807812986053)
                  ·
                    refine ⟨9654052481312401464934885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51488279900332807812986053 9654052481312401464934885)
                    ·
                      refine ⟨1810134840246075274675291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9654052481312401464934885 1810134840246075274675291)
                      ·
                        rfl

theorem cell23_3525225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3525225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525225 prefixEnd_3525225 := by exact prefixLift 3525225
  have htrace : WordTrace (prefixWord ++ tailWord_3525225) baseStart_3525225 baseEnd_3525225 := by
    simpa [prefixWord, tailWord_3525225, baseEnd_3525225] using wordTrace_append hprefix tailTrace_3525225
  have hstable : (prefixWord ++ tailWord_3525225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525225).length < 2 ^ (prefixWord ++ tailWord_3525225).sum := by decide
  have hdescent : baseEnd_3525225 < baseStart_3525225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525229 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3525229 : Nat := 118140960795 + 3525229 * 2 ^ 59
def prefixEnd_3525229 : Nat := 4983230072969 + 3 ^ 40 * 3525229 * 2
def baseEnd_3525229 : Nat := 1810136894168693259025273

theorem tailTrace_3525229 : CollatzResearch.WordTrace tailWord_3525229 prefixEnd_3525229 1810136894168693259025273 := by
  unfold tailWord_3525229
  simp only [CollatzResearch.WordTrace]
  refine ⟨128575664545704869025770741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85717109697136579350513827 128575664545704869025770741)
  ·
    refine ⟨12053968551159831471166007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128575664545704869025770741 12053968551159831471166007)
    ·
      refine ⟨18080952826739747206749011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12053968551159831471166007 18080952826739747206749011)
      ·
        refine ⟨27121429240109620810123517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18080952826739747206749011 27121429240109620810123517)
        ·
          refine ⟨10170535965041107803796319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27121429240109620810123517 10170535965041107803796319)
          ·
            refine ⟨15255803947561661705694479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170535965041107803796319 15255803947561661705694479)
            ·
              refine ⟨22883705921342492558541719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15255803947561661705694479 22883705921342492558541719)
              ·
                refine ⟨34325558882013738837812579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22883705921342492558541719 34325558882013738837812579)
                ·
                  refine ⟨51488338323020608256718869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34325558882013738837812579 51488338323020608256718869)
                  ·
                    refine ⟨2413515858891591012033697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51488338323020608256718869 2413515858891591012033697)
                    ·
                      refine ⟨1810136894168693259025273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413515858891591012033697 1810136894168693259025273)
                      ·
                        rfl

theorem cell23_3525229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3525229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525229 prefixEnd_3525229 := by exact prefixLift 3525229
  have htrace : WordTrace (prefixWord ++ tailWord_3525229) baseStart_3525229 baseEnd_3525229 := by
    simpa [prefixWord, tailWord_3525229, baseEnd_3525229] using wordTrace_append hprefix tailTrace_3525229
  have hstable : (prefixWord ++ tailWord_3525229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525229).length < 2 ^ (prefixWord ++ tailWord_3525229).sum := by decide
  have hdescent : baseEnd_3525229 < baseStart_3525229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525299 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 1, 5]
def baseStart_3525299 : Nat := 118140960795 + 3525299 * 2 ^ 59
def prefixEnd_3525299 : Nat := 4983230072969 + 3 ^ 40 * 3525299 * 2
def baseEnd_3525299 : Nat := 603390945938169328383317

theorem tailTrace_3525299 : CollatzResearch.WordTrace tailWord_3525299 prefixEnd_3525299 603390945938169328383317 := by
  unfold tailWord_3525299
  simp only [CollatzResearch.WordTrace]
  refine ⟨128578217655451270980818951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85718811770300847320545967 128578217655451270980818951)
  ·
    refine ⟨192867326483176906471228427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128578217655451270980818951 192867326483176906471228427)
    ·
      refine ⟨289300989724765359706842641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192867326483176906471228427 289300989724765359706842641)
      ·
        refine ⟨216975742293574019780131981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289300989724765359706842641 216975742293574019780131981)
        ·
          refine ⟨81365903360090257417549493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216975742293574019780131981 81365903360090257417549493)
          ·
            refine ⟨7628053440008461632895265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81365903360090257417549493 7628053440008461632895265)
            ·
              refine ⟨5721040080006346224671449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628053440008461632895265 5721040080006346224671449)
              ·
                refine ⟨4290780060004759668503587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5721040080006346224671449 4290780060004759668503587)
                ·
                  refine ⟨6436170090007139502755381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290780060004759668503587 6436170090007139502755381)
                  ·
                    refine ⟨603390945938169328383317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6436170090007139502755381 603390945938169328383317)
                    ·
                      rfl

theorem cell23_3525299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 5].length) (baseStart_3525299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525299 prefixEnd_3525299 := by exact prefixLift 3525299
  have htrace : WordTrace (prefixWord ++ tailWord_3525299) baseStart_3525299 baseEnd_3525299 := by
    simpa [prefixWord, tailWord_3525299, baseEnd_3525299] using wordTrace_append hprefix tailTrace_3525299
  have hstable : (prefixWord ++ tailWord_3525299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525299).length < 2 ^ (prefixWord ++ tailWord_3525299).sum := by decide
  have hdescent : baseEnd_3525299 < baseStart_3525299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525329 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3525329 : Nat := 118140960795 + 3525329 * 2 ^ 59
def prefixEnd_3525329 : Nat := 4983230072969 + 3 ^ 40 * 3525329 * 2
def baseEnd_3525329 : Nat := 603396080744714289258271

theorem tailTrace_3525329 : CollatzResearch.WordTrace tailWord_3525329 prefixEnd_3525329 603396080744714289258271 := by
  unfold tailWord_3525329
  simp only [CollatzResearch.WordTrace]
  refine ⟨128579311845342586104411041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85719541230228390736274027 128579311845342586104411041)
  ·
    refine ⟨96434483884006939578308281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128579311845342586104411041 96434483884006939578308281)
    ·
      refine ⟨72325862913005204683731211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96434483884006939578308281 72325862913005204683731211)
      ·
        refine ⟨108488794369507807025596817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72325862913005204683731211 108488794369507807025596817)
        ·
          refine ⟨81366595777130855269197613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108488794369507807025596817 81366595777130855269197613)
          ·
            refine ⟨30512473416424070725949105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81366595777130855269197613 30512473416424070725949105)
            ·
              refine ⟨22884355062318053044461829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30512473416424070725949105 22884355062318053044461829)
              ·
                refine ⟨4290816574184634945836593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22884355062318053044461829 4290816574184634945836593)
                ·
                  refine ⟨3218112430638476209377445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290816574184634945836593 3218112430638476209377445)
                  ·
                    refine ⟨603396080744714289258271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218112430638476209377445 603396080744714289258271)
                    ·
                      rfl

theorem cell23_3525329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3525329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525329 prefixEnd_3525329 := by exact prefixLift 3525329
  have htrace : WordTrace (prefixWord ++ tailWord_3525329) baseStart_3525329 baseEnd_3525329 := by
    simpa [prefixWord, tailWord_3525329, baseEnd_3525329] using wordTrace_append hprefix tailTrace_3525329
  have hstable : (prefixWord ++ tailWord_3525329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525329).length < 2 ^ (prefixWord ++ tailWord_3525329).sum := by decide
  have hdescent : baseEnd_3525329 < baseStart_3525329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525330 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3525330 : Nat := 118140960795 + 3525330 * 2 ^ 59
def prefixEnd_3525330 : Nat := 4983230072969 + 3 ^ 40 * 3525330 * 2
def baseEnd_3525330 : Nat := 1810188755714797363862309

theorem tailTrace_3525330 : CollatzResearch.WordTrace tailWord_3525330 prefixEnd_3525330 1810188755714797363862309 := by
  unfold tailWord_3525330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144837079584740818799361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85719565545559308850131629 32144837079584740818799361)
  ·
    refine ⟨24108627809688555614099521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32144837079584740818799361 24108627809688555614099521)
    ·
      refine ⟨18081470857266416710574641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24108627809688555614099521 18081470857266416710574641)
      ·
        refine ⟨13561103142949812532930981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18081470857266416710574641 13561103142949812532930981)
        ·
          refine ⟨2542706839303089849924559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13561103142949812532930981 2542706839303089849924559)
          ·
            refine ⟨3814060258954634774886839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542706839303089849924559 3814060258954634774886839)
            ·
              refine ⟨5721090388431952162330259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814060258954634774886839 5721090388431952162330259)
              ·
                refine ⟨8581635582647928243495389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721090388431952162330259 8581635582647928243495389)
                ·
                  refine ⟨3218113343492973091310771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8581635582647928243495389 3218113343492973091310771)
                  ·
                    refine ⟨4827170015239459636966157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218113343492973091310771 4827170015239459636966157)
                    ·
                      refine ⟨1810188755714797363862309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827170015239459636966157 1810188755714797363862309)
                      ·
                        rfl

theorem cell23_3525330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3525330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525330 prefixEnd_3525330 := by exact prefixLift 3525330
  have htrace : WordTrace (prefixWord ++ tailWord_3525330) baseStart_3525330 baseEnd_3525330 := by
    simpa [prefixWord, tailWord_3525330, baseEnd_3525330] using wordTrace_append hprefix tailTrace_3525330
  have hstable : (prefixWord ++ tailWord_3525330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525330).length < 2 ^ (prefixWord ++ tailWord_3525330).sum := by decide
  have hdescent : baseEnd_3525330 < baseStart_3525330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525369 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3525369 : Nat := 118140960795 + 3525369 * 2 ^ 59
def prefixEnd_3525369 : Nat := 4983230072969 + 3 ^ 40 * 3525369 * 2
def baseEnd_3525369 : Nat := 1810208781460322711274629

theorem tailTrace_3525369 : CollatzResearch.WordTrace tailWord_3525369 prefixEnd_3525369 1810208781460322711274629 := by
  unfold tailWord_3525369
  simp only [CollatzResearch.WordTrace]
  refine ⟨128580770765197672935867161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85720513843465115290578107 128580770765197672935867161)
  ·
    refine ⟨96435578073898254701900371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128580770765197672935867161 96435578073898254701900371)
    ·
      refine ⟨144653367110847382052850557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96435578073898254701900371 144653367110847382052850557)
      ·
        refine ⟨54245012666567768269818959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144653367110847382052850557 54245012666567768269818959)
        ·
          refine ⟨81367518999851652404728439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54245012666567768269818959 81367518999851652404728439)
          ·
            refine ⟨122051278499777478607092659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81367518999851652404728439 122051278499777478607092659)
            ·
              refine ⟨183076917749666217910638989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122051278499777478607092659 183076917749666217910638989)
              ·
                refine ⟨68653844156124831716489621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183076917749666217910638989 68653844156124831716489621)
                ·
                  refine ⟨3218148944818351486710451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68653844156124831716489621 3218148944818351486710451)
                  ·
                    refine ⟨4827223417227527230065677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218148944818351486710451 4827223417227527230065677)
                    ·
                      refine ⟨1810208781460322711274629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827223417227527230065677 1810208781460322711274629)
                      ·
                        rfl

theorem cell23_3525369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3525369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525369 prefixEnd_3525369 := by exact prefixLift 3525369
  have htrace : WordTrace (prefixWord ++ tailWord_3525369) baseStart_3525369 baseEnd_3525369 := by
    simpa [prefixWord, tailWord_3525369, baseEnd_3525369] using wordTrace_append hprefix tailTrace_3525369
  have hstable : (prefixWord ++ tailWord_3525369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525369).length < 2 ^ (prefixWord ++ tailWord_3525369).sum := by decide
  have hdescent : baseEnd_3525369 < baseStart_3525369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525426 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_3525426 : Nat := 118140960795 + 3525426 * 2 ^ 59
def prefixEnd_3525426 : Nat := 4983230072969 + 3 ^ 40 * 3525426 * 2
def baseEnd_3525426 : Nat := 1810238049857628988261867

theorem tailTrace_3525426 : CollatzResearch.WordTrace tailWord_3525426 prefixEnd_3525426 1810238049857628988261867 := by
  unfold tailWord_3525426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32145712431497792917673033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85721899817327447780461421 32145712431497792917673033)
  ·
    refine ⟨24109284323623344688254775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32145712431497792917673033 24109284323623344688254775)
    ·
      refine ⟨36163926485435017032382163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24109284323623344688254775 36163926485435017032382163)
      ·
        refine ⟨54245889728152525548573245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36163926485435017032382163 54245889728152525548573245)
        ·
          refine ⟨20342208648057197080714967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54245889728152525548573245 20342208648057197080714967)
          ·
            refine ⟨30513312972085795621072451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20342208648057197080714967 30513312972085795621072451)
            ·
              refine ⟨45769969458128693431608677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30513312972085795621072451 45769969458128693431608677)
              ·
                refine ⟨8581869273399130018426627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45769969458128693431608677 8581869273399130018426627)
                ·
                  refine ⟨12872803910098695027639941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581869273399130018426627 12872803910098695027639941)
                  ·
                    refine ⟨2413650733143505317682489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12872803910098695027639941 2413650733143505317682489)
                    ·
                      refine ⟨1810238049857628988261867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413650733143505317682489 1810238049857628988261867)
                      ·
                        rfl

theorem cell23_3525426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_3525426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525426 prefixEnd_3525426 := by exact prefixLift 3525426
  have htrace : WordTrace (prefixWord ++ tailWord_3525426) baseStart_3525426 baseEnd_3525426 := by
    simpa [prefixWord, tailWord_3525426, baseEnd_3525426] using wordTrace_append hprefix tailTrace_3525426
  have hstable : (prefixWord ++ tailWord_3525426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525426).length < 2 ^ (prefixWord ++ tailWord_3525426).sum := by decide
  have hdescent : baseEnd_3525426 < baseStart_3525426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525432 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 9]
def baseStart_3525432 : Nat := 118140960795 + 3525432 * 2 ^ 59
def prefixEnd_3525432 : Nat := 4983230072969 + 3 ^ 40 * 3525432 * 2
def baseEnd_3525432 : Nat := 201137903415728440531871

theorem tailTrace_3525432 : CollatzResearch.WordTrace tailWord_3525432 prefixEnd_3525432 201137903415728440531871 := by
  unfold tailWord_3525432
  simp only [CollatzResearch.WordTrace]
  refine ⟨64291534281984717347705275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85722045709312956463607033 64291534281984717347705275)
  ·
    refine ⟨96437301422977076021557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64291534281984717347705275 96437301422977076021557913)
    ·
      refine ⟨72327976067232807016168435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96437301422977076021557913 72327976067232807016168435)
      ·
        refine ⟨108491964100849210524252653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72327976067232807016168435 108491964100849210524252653)
        ·
          refine ⟨40684486537818453946594745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108491964100849210524252653 40684486537818453946594745)
          ·
            refine ⟨30513364903363840459946059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40684486537818453946594745 30513364903363840459946059)
            ·
              refine ⟨45770047355045760689919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30513364903363840459946059 45770047355045760689919089)
              ·
                refine ⟨34327535516284320517439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45770047355045760689919089 34327535516284320517439317)
                ·
                  refine ⟨201137903415728440531871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34327535516284320517439317 201137903415728440531871)
                  ·
                    rfl

theorem cell23_3525432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_3525432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525432 prefixEnd_3525432 := by exact prefixLift 3525432
  have htrace : WordTrace (prefixWord ++ tailWord_3525432) baseStart_3525432 baseEnd_3525432 := by
    simpa [prefixWord, tailWord_3525432, baseEnd_3525432] using wordTrace_append hprefix tailTrace_3525432
  have hstable : (prefixWord ++ tailWord_3525432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525432).length < 2 ^ (prefixWord ++ tailWord_3525432).sum := by decide
  have hdescent : baseEnd_3525432 < baseStart_3525432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525437 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3525437 : Nat := 118140960795 + 3525437 * 2 ^ 59
def prefixEnd_3525437 : Nat := 4983230072969 + 3 ^ 40 * 3525437 * 2
def baseEnd_3525437 : Nat := 1810243698144828445224317

theorem tailTrace_3525437 : CollatzResearch.WordTrace tailWord_3525437 prefixEnd_3525437 1810243698144828445224317 := by
  unfold tailWord_3525437
  simp only [CollatzResearch.WordTrace]
  refine ⟨128583250928951320549342565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85722167285967547032895043 128583250928951320549342565)
  ·
    refine ⟨24109359549178372603001731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128583250928951320549342565 24109359549178372603001731)
    ·
      refine ⟨36164039323767558904502597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24109359549178372603001731 36164039323767558904502597)
      ·
        refine ⟨6780757373206417294594237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36164039323767558904502597 6780757373206417294594237)
        ·
          refine ⟨2542784014952406485472839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6780757373206417294594237 2542784014952406485472839)
          ·
            refine ⟨3814176022428609728209259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542784014952406485472839 3814176022428609728209259)
            ·
              refine ⟨5721264033642914592313889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814176022428609728209259 5721264033642914592313889)
              ·
                refine ⟨4290948025232185944235417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5721264033642914592313889 4290948025232185944235417)
                ·
                  refine ⟨3218211018924139458176563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290948025232185944235417 3218211018924139458176563)
                  ·
                    refine ⟨4827316528386209187264845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218211018924139458176563 4827316528386209187264845)
                    ·
                      refine ⟨1810243698144828445224317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827316528386209187264845 1810243698144828445224317)
                      ·
                        rfl

theorem cell23_3525437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3525437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525437 prefixEnd_3525437 := by exact prefixLift 3525437
  have htrace : WordTrace (prefixWord ++ tailWord_3525437) baseStart_3525437 baseEnd_3525437 := by
    simpa [prefixWord, tailWord_3525437, baseEnd_3525437] using wordTrace_append hprefix tailTrace_3525437
  have hstable : (prefixWord ++ tailWord_3525437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525437).length < 2 ^ (prefixWord ++ tailWord_3525437).sum := by decide
  have hdescent : baseEnd_3525437 < baseStart_3525437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525439 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3525439 : Nat := 118140960795 + 3525439 * 2 ^ 59
def prefixEnd_3525439 : Nat := 4983230072969 + 3 ^ 40 * 3525439 * 2
def baseEnd_3525439 : Nat := 1810244725106137437399307

theorem tailTrace_3525439 : CollatzResearch.WordTrace tailWord_3525439 prefixEnd_3525439 1810244725106137437399307 := by
  unfold tailWord_3525439
  simp only [CollatzResearch.WordTrace]
  refine ⟨128583323874944074890915371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85722215916629383260610247 128583323874944074890915371)
  ·
    refine ⟨192874985812416112336373057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128583323874944074890915371 192874985812416112336373057)
    ·
      refine ⟨144656239359312084252279793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192874985812416112336373057 144656239359312084252279793)
      ·
        refine ⟨108492179519484063189209845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144656239359312084252279793 108492179519484063189209845)
        ·
          refine ⟨10171141829951630923988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108492179519484063189209845 10171141829951630923988423)
          ·
            refine ⟨15256712744927446385982635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171141829951630923988423 15256712744927446385982635)
            ·
              refine ⟨22885069117391169578973953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15256712744927446385982635 22885069117391169578973953)
              ·
                refine ⟨17163801838043377184230465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22885069117391169578973953 17163801838043377184230465)
                ·
                  refine ⟨12872851378532532888172849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17163801838043377184230465 12872851378532532888172849)
                  ·
                    refine ⟨9654638533899399666129637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12872851378532532888172849 9654638533899399666129637)
                    ·
                      refine ⟨1810244725106137437399307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9654638533899399666129637 1810244725106137437399307)
                      ·
                        rfl

theorem cell23_3525439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3525439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525439 prefixEnd_3525439 := by exact prefixLift 3525439
  have htrace : WordTrace (prefixWord ++ tailWord_3525439) baseStart_3525439 baseEnd_3525439 := by
    simpa [prefixWord, tailWord_3525439, baseEnd_3525439] using wordTrace_append hprefix tailTrace_3525439
  have hstable : (prefixWord ++ tailWord_3525439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525439).length < 2 ^ (prefixWord ++ tailWord_3525439).sum := by decide
  have hdescent : baseEnd_3525439 < baseStart_3525439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525449 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 7]
def baseStart_3525449 : Nat := 118140960795 + 3525449 * 2 ^ 59
def prefixEnd_3525449 : Nat := 4983230072969 + 3 ^ 40 * 3525449 * 2
def baseEnd_3525449 : Nat := 201138873323631377586029

theorem tailTrace_3525449 : CollatzResearch.WordTrace tailWord_3525449 prefixEnd_3525449 201138873323631377586029 := by
  unfold tailWord_3525449
  simp only [CollatzResearch.WordTrace]
  refine ⟨128583688604907846598779401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85722459069938564399186267 128583688604907846598779401)
  ·
    refine ⟨96437766453680884949084551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128583688604907846598779401 96437766453680884949084551)
    ·
      refine ⟨144656649680521327423626827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96437766453680884949084551 144656649680521327423626827)
      ·
        refine ⟨216984974520781991135440241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144656649680521327423626827 216984974520781991135440241)
        ·
          refine ⟨162738730890586493351580181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216984974520781991135440241 162738730890586493351580181)
          ·
            refine ⟨7628378010496241875855321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162738730890586493351580181 7628378010496241875855321)
            ·
              refine ⟨5721283507872181406891491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628378010496241875855321 5721283507872181406891491)
              ·
                refine ⟨8581925261808272110337237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721283507872181406891491 8581925261808272110337237)
                ·
                  refine ⟨201138873323631377586029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8581925261808272110337237 201138873323631377586029)
                  ·
                    rfl

theorem cell23_3525449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_3525449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525449 prefixEnd_3525449 := by exact prefixLift 3525449
  have htrace : WordTrace (prefixWord ++ tailWord_3525449) baseStart_3525449 baseEnd_3525449 := by
    simpa [prefixWord, tailWord_3525449, baseEnd_3525449] using wordTrace_append hprefix tailTrace_3525449
  have hstable : (prefixWord ++ tailWord_3525449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525449).length < 2 ^ (prefixWord ++ tailWord_3525449).sum := by decide
  have hdescent : baseEnd_3525449 < baseStart_3525449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525460 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_3525460 : Nat := 118140960795 + 3525460 * 2 ^ 59
def prefixEnd_3525460 : Nat := 4983230072969 + 3 ^ 40 * 3525460 * 2
def baseEnd_3525460 : Nat := 1810255508199881855236711

theorem tailTrace_3525460 : CollatzResearch.WordTrace tailWord_3525460 prefixEnd_3525460 1810255508199881855236711 := by
  unfold tailWord_3525460
  simp only [CollatzResearch.WordTrace]
  refine ⟨64292044903933997738714917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85722726538578663651619889 64292044903933997738714917)
  ·
    refine ⟨12054758419487624576009047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64292044903933997738714917 12054758419487624576009047)
    ·
      refine ⟨18082137629231436864013571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12054758419487624576009047 18082137629231436864013571)
      ·
        refine ⟨27123206443847155296020357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18082137629231436864013571 27123206443847155296020357)
        ·
          refine ⟨5085601208221341618003817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27123206443847155296020357 5085601208221341618003817)
          ·
            refine ⟨3814200906166006213502863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085601208221341618003817 3814200906166006213502863)
            ·
              refine ⟨5721301359249009320254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814200906166006213502863 5721301359249009320254295)
              ·
                refine ⟨8581952038873513980381443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721301359249009320254295 8581952038873513980381443)
                ·
                  refine ⟨12872928058310270970572165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581952038873513980381443 12872928058310270970572165)
                  ·
                    refine ⟨2413674010933175806982281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12872928058310270970572165 2413674010933175806982281)
                    ·
                      refine ⟨1810255508199881855236711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413674010933175806982281 1810255508199881855236711)
                      ·
                        rfl

theorem cell23_3525460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_3525460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525460 prefixEnd_3525460 := by exact prefixLift 3525460
  have htrace : WordTrace (prefixWord ++ tailWord_3525460) baseStart_3525460 baseEnd_3525460 := by
    simpa [prefixWord, tailWord_3525460, baseEnd_3525460] using wordTrace_append hprefix tailTrace_3525460
  have hstable : (prefixWord ++ tailWord_3525460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525460).length < 2 ^ (prefixWord ++ tailWord_3525460).sum := by decide
  have hdescent : baseEnd_3525460 < baseStart_3525460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525479 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3525479 : Nat := 118140960795 + 3525479 * 2 ^ 59
def prefixEnd_3525479 : Nat := 4983230072969 + 3 ^ 40 * 3525479 * 2
def baseEnd_3525479 : Nat := 603421754777439093633041

theorem tailTrace_3525479 : CollatzResearch.WordTrace tailWord_3525479 prefixEnd_3525479 603421754777439093633041 := by
  unfold tailWord_3525479
  simp only [CollatzResearch.WordTrace]
  refine ⟨128584782794799161722371491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85723188529866107814914327 128584782794799161722371491)
  ·
    refine ⟨192877174192198742583557237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128584782794799161722371491 192877174192198742583557237)
    ·
      refine ⟨18082235080518632117208491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192877174192198742583557237 18082235080518632117208491)
      ·
        refine ⟨27123352620777948175812737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18082235080518632117208491 27123352620777948175812737)
        ·
          refine ⟨20342514465583461131859553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27123352620777948175812737 20342514465583461131859553)
          ·
            refine ⟨15256885849187595848894665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20342514465583461131859553 15256885849187595848894665)
            ·
              refine ⟨11442664386890696886670999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15256885849187595848894665 11442664386890696886670999)
              ·
                refine ⟨17163996580336045330006499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11442664386890696886670999 17163996580336045330006499)
                ·
                  refine ⟨25745994870504067995009749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17163996580336045330006499 25745994870504067995009749)
                  ·
                    refine ⟨603421754777439093633041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25745994870504067995009749 603421754777439093633041)
                    ·
                      rfl

theorem cell23_3525479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3525479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525479 prefixEnd_3525479 := by exact prefixLift 3525479
  have htrace : WordTrace (prefixWord ++ tailWord_3525479) baseStart_3525479 baseEnd_3525479 := by
    simpa [prefixWord, tailWord_3525479, baseEnd_3525479] using wordTrace_append hprefix tailTrace_3525479
  have hstable : (prefixWord ++ tailWord_3525479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525479).length < 2 ^ (prefixWord ++ tailWord_3525479).sum := by decide
  have hdescent : baseEnd_3525479 < baseStart_3525479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525499 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4]
def baseStart_3525499 : Nat := 118140960795 + 3525499 * 2 ^ 59
def prefixEnd_3525499 : Nat := 4983230072969 + 3 ^ 40 * 3525499 * 2
def baseEnd_3525499 : Nat := 1810275533945407202649031

theorem tailTrace_3525499 : CollatzResearch.WordTrace tailWord_3525499 prefixEnd_3525499 1810275533945407202649031 := by
  unfold tailWord_3525499
  simp only [CollatzResearch.WordTrace]
  refine ⟨128585512254726705138099551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85723674836484470092066367 128585512254726705138099551)
  ·
    refine ⟨192878268382090057707149327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128585512254726705138099551 192878268382090057707149327)
    ·
      refine ⟨289317402573135086560723991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192878268382090057707149327 289317402573135086560723991)
      ·
        refine ⟨433976103859702629841085987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289317402573135086560723991 433976103859702629841085987)
        ·
          refine ⟨650964155789553944761628981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433976103859702629841085987 650964155789553944761628981)
          ·
            refine ⟨61027889605270682321402717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 650964155789553944761628981 61027889605270682321402717)
            ·
              refine ⟨22885458601976505870526019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61027889605270682321402717 22885458601976505870526019)
              ·
                refine ⟨34328187902964758805789029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885458601976505870526019 34328187902964758805789029)
                ·
                  refine ⟨6436535231805892276085443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34328187902964758805789029 6436535231805892276085443)
                  ·
                    refine ⟨9654802847708838414128165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436535231805892276085443 9654802847708838414128165)
                    ·
                      refine ⟨1810275533945407202649031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9654802847708838414128165 1810275533945407202649031)
                      ·
                        rfl

theorem cell23_3525499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_3525499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525499 prefixEnd_3525499 := by exact prefixLift 3525499
  have htrace : WordTrace (prefixWord ++ tailWord_3525499) baseStart_3525499 baseEnd_3525499 := by
    simpa [prefixWord, tailWord_3525499, baseEnd_3525499] using wordTrace_append hprefix tailTrace_3525499
  have hstable : (prefixWord ++ tailWord_3525499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525499).length < 2 ^ (prefixWord ++ tailWord_3525499).sum := by decide
  have hdescent : baseEnd_3525499 < baseStart_3525499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525516 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_3525516 : Nat := 118140960795 + 3525516 * 2 ^ 59
def prefixEnd_3525516 : Nat := 4983230072969 + 3 ^ 40 * 3525516 * 2
def baseEnd_3525516 : Nat := 1810284263116533636136453

theorem tailTrace_3525516 : CollatzResearch.WordTrace tailWord_3525516 prefixEnd_3525516 1810284263116533636136453 := by
  unfold tailWord_3525516
  simp only [CollatzResearch.WordTrace]
  refine ⟨64293066147832558520734201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85724088197110078027645601 64293066147832558520734201)
  ·
    refine ⟨48219799610874418890550651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64293066147832558520734201 48219799610874418890550651)
    ·
      refine ⟨72329699416311628335825977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48219799610874418890550651 72329699416311628335825977)
      ·
        refine ⟨54247274562233721251869483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72329699416311628335825977 54247274562233721251869483)
        ·
          refine ⟨81370911843350581877804225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54247274562233721251869483 81370911843350581877804225)
          ·
            refine ⟨61028183882512936408353169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81370911843350581877804225 61028183882512936408353169)
            ·
              refine ⟨45771137911884702306264877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61028183882512936408353169 45771137911884702306264877)
              ·
                refine ⟨17164176716956763364849329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45771137911884702306264877 17164176716956763364849329)
                ·
                  refine ⟨12873132537717572523636997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17164176716956763364849329 12873132537717572523636997)
                  ·
                    refine ⟨2413712350822044848181937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12873132537717572523636997 2413712350822044848181937)
                    ·
                      refine ⟨1810284263116533636136453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413712350822044848181937 1810284263116533636136453)
                      ·
                        rfl

theorem cell23_3525516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_3525516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525516 prefixEnd_3525516 := by exact prefixLift 3525516
  have htrace : WordTrace (prefixWord ++ tailWord_3525516) baseStart_3525516 baseEnd_3525516 := by
    simpa [prefixWord, tailWord_3525516, baseEnd_3525516] using wordTrace_append hprefix tailTrace_3525516
  have hstable : (prefixWord ++ tailWord_3525516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525516).length < 2 ^ (prefixWord ++ tailWord_3525516).sum := by decide
  have hdescent : baseEnd_3525516 < baseStart_3525516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525536 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3525536 : Nat := 118140960795 + 3525536 * 2 ^ 59
def prefixEnd_3525536 : Nat := 4983230072969 + 3 ^ 40 * 3525536 * 2
def baseEnd_3525536 : Nat := 1810294532729623557886361

theorem tailTrace_3525536 : CollatzResearch.WordTrace tailWord_3525536 prefixEnd_3525536 1810294532729623557886361 := by
  unfold tailWord_3525536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64293430877796330228598231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85724574503728440304797641 64293430877796330228598231)
  ·
    refine ⟨96440146316694495342897347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64293430877796330228598231 96440146316694495342897347)
    ·
      refine ⟨144660219475041743014346021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96440146316694495342897347 144660219475041743014346021)
      ·
        refine ⟨27123791151570326815189879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144660219475041743014346021 27123791151570326815189879)
        ·
          refine ⟨40685686727355490222784819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27123791151570326815189879 40685686727355490222784819)
          ·
            refine ⟨61028530091033235334177229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40685686727355490222784819 61028530091033235334177229)
            ·
              refine ⟨22885698784137463250316461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61028530091033235334177229 22885698784137463250316461)
              ·
                refine ⟨8582137044051548718868673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22885698784137463250316461 8582137044051548718868673)
                ·
                  refine ⟨6436602783038661539151505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8582137044051548718868673 6436602783038661539151505)
                  ·
                    refine ⟨4827452087278996154363629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6436602783038661539151505 4827452087278996154363629)
                    ·
                      refine ⟨1810294532729623557886361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827452087278996154363629 1810294532729623557886361)
                      ·
                        rfl

theorem cell23_3525536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3525536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525536 prefixEnd_3525536 := by exact prefixLift 3525536
  have htrace : WordTrace (prefixWord ++ tailWord_3525536) baseStart_3525536 baseEnd_3525536 := by
    simpa [prefixWord, tailWord_3525536, baseEnd_3525536] using wordTrace_append hprefix tailTrace_3525536
  have hstable : (prefixWord ++ tailWord_3525536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525536).length < 2 ^ (prefixWord ++ tailWord_3525536).sum := by decide
  have hdescent : baseEnd_3525536 < baseStart_3525536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525560 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 1, 4]
def baseStart_3525560 : Nat := 118140960795 + 3525560 * 2 ^ 59
def prefixEnd_3525560 : Nat := 4983230072969 + 3 ^ 40 * 3525560 * 2
def baseEnd_3525560 : Nat := 603435618755110487995417

theorem tailTrace_3525560 : CollatzResearch.WordTrace tailWord_3525560 prefixEnd_3525560 603435618755110487995417 := by
  unfold tailWord_3525560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64293868553752856278035067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85725158071670475037380089 64293868553752856278035067)
  ·
    refine ⟨96440802830629284417052601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64293868553752856278035067 96440802830629284417052601)
    ·
      refine ⟨72330602122971963312789451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96440802830629284417052601 72330602122971963312789451)
      ·
        refine ⟨108495903184457944969184177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72330602122971963312789451 108495903184457944969184177)
        ·
          refine ⟨81371927388343458726888133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108495903184457944969184177 81371927388343458726888133)
          ·
            refine ⟨15257236385314398511291525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81371927388343458726888133 15257236385314398511291525)
            ·
              refine ⟨2860731822246449720867161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15257236385314398511291525 2860731822246449720867161)
              ·
                refine ⟨2145548866684837290650371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860731822246449720867161 2145548866684837290650371)
                ·
                  refine ⟨3218323300027255935975557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145548866684837290650371 3218323300027255935975557)
                  ·
                    refine ⟨603435618755110487995417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218323300027255935975557 603435618755110487995417)
                    ·
                      rfl

theorem cell23_3525560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_3525560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525560 prefixEnd_3525560 := by exact prefixLift 3525560
  have htrace : WordTrace (prefixWord ++ tailWord_3525560) baseStart_3525560 baseEnd_3525560 := by
    simpa [prefixWord, tailWord_3525560, baseEnd_3525560] using wordTrace_append hprefix tailTrace_3525560
  have hstable : (prefixWord ++ tailWord_3525560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525560).length < 2 ^ (prefixWord ++ tailWord_3525560).sum := by decide
  have hdescent : baseEnd_3525560 < baseStart_3525560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525583 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_3525583 : Nat := 118140960795 + 3525583 * 2 ^ 59
def prefixEnd_3525583 : Nat := 4983230072969 + 3 ^ 40 * 3525583 * 2
def baseEnd_3525583 : Nat := 1810318666320384873998645

theorem tailTrace_3525583 : CollatzResearch.WordTrace tailWord_3525583 prefixEnd_3525583 1810318666320384873998645 := by
  unfold tailWord_3525583
  simp only [CollatzResearch.WordTrace]
  refine ⟨128588575986422387484157403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85725717324281591656104935 128588575986422387484157403)
  ·
    refine ⟨192882863979633581226236105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128588575986422387484157403 192882863979633581226236105)
    ·
      refine ⟨144662147984725185919677079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192882863979633581226236105 144662147984725185919677079)
      ·
        refine ⟨216993221977087778879515619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144662147984725185919677079 216993221977087778879515619)
        ·
          refine ⟨325489832965631668319273429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216993221977087778879515619 325489832965631668319273429)
          ·
            refine ⟨7628667960131992226232971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 325489832965631668319273429 7628667960131992226232971)
            ·
              refine ⟨11443001940197988339349457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628667960131992226232971 11443001940197988339349457)
              ·
                refine ⟨8582251455148491254512093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443001940197988339349457 8582251455148491254512093)
                ·
                  refine ⟨3218344295680684220442035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8582251455148491254512093 3218344295680684220442035)
                  ·
                    refine ⟨4827516443521026330663053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218344295680684220442035 4827516443521026330663053)
                    ·
                      refine ⟨1810318666320384873998645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827516443521026330663053 1810318666320384873998645)
                      ·
                        rfl

theorem cell23_3525583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_3525583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525583 prefixEnd_3525583 := by exact prefixLift 3525583
  have htrace : WordTrace (prefixWord ++ tailWord_3525583) baseStart_3525583 baseEnd_3525583 := by
    simpa [prefixWord, tailWord_3525583, baseEnd_3525583] using wordTrace_append hprefix tailTrace_3525583
  have hstable : (prefixWord ++ tailWord_3525583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525583).length < 2 ^ (prefixWord ++ tailWord_3525583).sum := by decide
  have hdescent : baseEnd_3525583 < baseStart_3525583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525593 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 5, 2]
def baseStart_3525593 : Nat := 118140960795 + 3525593 * 2 ^ 59
def prefixEnd_3525593 : Nat := 4983230072969 + 3 ^ 40 * 3525593 * 2
def baseEnd_3525593 : Nat := 1810323801126929834873599

theorem tailTrace_3525593 : CollatzResearch.WordTrace tailWord_3525593 prefixEnd_3525593 1810323801126929834873599 := by
  unfold tailWord_3525593
  simp only [CollatzResearch.WordTrace]
  refine ⟨128588940716386159192021433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85725960477590772794680955 128588940716386159192021433)
  ·
    refine ⟨96441705537289619394016075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128588940716386159192021433 96441705537289619394016075)
    ·
      refine ⟨144662558305934429091024113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96441705537289619394016075 144662558305934429091024113)
      ·
        refine ⟨108496918729450821818268085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144662558305934429091024113 108496918729450821818268085)
        ·
          refine ⟨10171586130886014545462633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108496918729450821818268085 10171586130886014545462633)
          ·
            refine ⟨7628689598164510909096975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10171586130886014545462633 7628689598164510909096975)
            ·
              refine ⟨11443034397246766363645463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628689598164510909096975 11443034397246766363645463)
              ·
                refine ⟨17164551595870149545468195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443034397246766363645463 17164551595870149545468195)
                ·
                  refine ⟨25746827393805224318202293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17164551595870149545468195 25746827393805224318202293)
                  ·
                    refine ⟨2413765068169239779831465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25746827393805224318202293 2413765068169239779831465)
                    ·
                      refine ⟨1810323801126929834873599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413765068169239779831465 1810323801126929834873599)
                      ·
                        rfl

theorem cell23_3525593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_3525593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525593 prefixEnd_3525593 := by exact prefixLift 3525593
  have htrace : WordTrace (prefixWord ++ tailWord_3525593) baseStart_3525593 baseEnd_3525593 := by
    simpa [prefixWord, tailWord_3525593, baseEnd_3525593] using wordTrace_append hprefix tailTrace_3525593
  have hstable : (prefixWord ++ tailWord_3525593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525593).length < 2 ^ (prefixWord ++ tailWord_3525593).sum := by decide
  have hdescent : baseEnd_3525593 < baseStart_3525593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525609 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3525609 : Nat := 118140960795 + 3525609 * 2 ^ 59
def prefixEnd_3525609 : Nat := 4983230072969 + 3 ^ 40 * 3525609 * 2
def baseEnd_3525609 : Nat := 1810332016817401772273525

theorem tailTrace_3525609 : CollatzResearch.WordTrace tailWord_3525609 prefixEnd_3525609 1810332016817401772273525 := by
  unfold tailWord_3525609
  simp only [CollatzResearch.WordTrace]
  refine ⟨128589524284328193924603881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85726349522885462616402587 128589524284328193924603881)
  ·
    refine ⟨96442143213246145443452911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128589524284328193924603881 96442143213246145443452911)
    ·
      refine ⟨144663214819869218165179367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96442143213246145443452911 144663214819869218165179367)
      ·
        refine ⟨216994822229803827247769051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144663214819869218165179367 216994822229803827247769051)
        ·
          refine ⟨325492233344705740871653577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216994822229803827247769051 325492233344705740871653577)
          ·
            refine ⟨244119175008529305653740183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325492233344705740871653577 244119175008529305653740183)
            ·
              refine ⟨366178762512793958480610275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244119175008529305653740183 366178762512793958480610275)
              ·
                refine ⟨549268143769190937720915413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366178762512793958480610275 549268143769190937720915413)
                ·
                  refine ⟨12873472119590412602833955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 549268143769190937720915413 12873472119590412602833955)
                  ·
                    refine ⟨19310208179385618904250933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12873472119590412602833955 19310208179385618904250933)
                    ·
                      refine ⟨1810332016817401772273525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19310208179385618904250933 1810332016817401772273525)
                      ·
                        rfl

theorem cell23_3525609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3525609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525609 prefixEnd_3525609 := by exact prefixLift 3525609
  have htrace : WordTrace (prefixWord ++ tailWord_3525609) baseStart_3525609 baseEnd_3525609 := by
    simpa [prefixWord, tailWord_3525609, baseEnd_3525609] using wordTrace_append hprefix tailTrace_3525609
  have hstable : (prefixWord ++ tailWord_3525609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525609).length < 2 ^ (prefixWord ++ tailWord_3525609).sum := by decide
  have hdescent : baseEnd_3525609 < baseStart_3525609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525619 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_3525619 : Nat := 118140960795 + 3525619 * 2 ^ 59
def prefixEnd_3525619 : Nat := 4983230072969 + 3 ^ 40 * 3525619 * 2
def baseEnd_3525619 : Nat := 1810337151623946733148479

theorem tailTrace_3525619 : CollatzResearch.WordTrace tailWord_3525619 prefixEnd_3525619 1810337151623946733148479 := by
  unfold tailWord_3525619
  simp only [CollatzResearch.WordTrace]
  refine ⟨128589889014291965632467911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85726592676194643754978607 128589889014291965632467911)
  ·
    refine ⟨192884833521437948448701867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128589889014291965632467911 192884833521437948448701867)
    ·
      refine ⟨289327250282156922673052801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192884833521437948448701867 289327250282156922673052801)
      ·
        refine ⟨216995437711617692004789601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289327250282156922673052801 216995437711617692004789601)
        ·
          refine ⟨162746578283713269003592201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216995437711617692004789601 162746578283713269003592201)
          ·
            refine ⟨122059933712784951752694151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162746578283713269003592201 122059933712784951752694151)
            ·
              refine ⟨183089900569177427629041227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122059933712784951752694151 183089900569177427629041227)
              ·
                refine ⟨274634850853766141443561841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183089900569177427629041227 274634850853766141443561841)
                ·
                  refine ⟨205976138140324606082671381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274634850853766141443561841 205976138140324606082671381)
                  ·
                    refine ⟨9655131475327715910125221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205976138140324606082671381 9655131475327715910125221)
                    ·
                      refine ⟨1810337151623946733148479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9655131475327715910125221 1810337151623946733148479)
                      ·
                        rfl

theorem cell23_3525619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_3525619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525619 prefixEnd_3525619 := by exact prefixLift 3525619
  have htrace : WordTrace (prefixWord ++ tailWord_3525619) baseStart_3525619 baseEnd_3525619 := by
    simpa [prefixWord, tailWord_3525619, baseEnd_3525619] using wordTrace_append hprefix tailTrace_3525619
  have hstable : (prefixWord ++ tailWord_3525619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525619).length < 2 ^ (prefixWord ++ tailWord_3525619).sum := by decide
  have hdescent : baseEnd_3525619 < baseStart_3525619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525626 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_3525626 : Nat := 118140960795 + 3525626 * 2 ^ 59
def prefixEnd_3525626 : Nat := 4983230072969 + 3 ^ 40 * 3525626 * 2
def baseEnd_3525626 : Nat := 1810340745988528205760947

theorem tailTrace_3525626 : CollatzResearch.WordTrace tailWord_3525626 prefixEnd_3525626 1810340745988528205760947 := by
  unfold tailWord_3525626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32147536081316651456993183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85726762883511070551981821 32147536081316651456993183)
  ·
    refine ⟨48221304121974977185489775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32147536081316651456993183 48221304121974977185489775)
    ·
      refine ⟨72331956182962465778234663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48221304121974977185489775 72331956182962465778234663)
      ·
        refine ⟨108497934274443698667351995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72331956182962465778234663 108497934274443698667351995)
        ·
          refine ⟨162746901411665548001027993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108497934274443698667351995 162746901411665548001027993)
          ·
            refine ⟨122060176058749161000770995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162746901411665548001027993 122060176058749161000770995)
            ·
              refine ⟨183090264088123741501156493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122060176058749161000770995 183090264088123741501156493)
              ·
                refine ⟨68658849033046403062933685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183090264088123741501156493 68658849033046403062933685)
                ·
                  refine ⟨6436767096848100287150033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68658849033046403062933685 6436767096848100287150033)
                  ·
                    refine ⟨4827575322636075215362525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6436767096848100287150033 4827575322636075215362525)
                    ·
                      refine ⟨1810340745988528205760947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827575322636075215362525 1810340745988528205760947)
                      ·
                        rfl

theorem cell23_3525626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_3525626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525626 prefixEnd_3525626 := by exact prefixLift 3525626
  have htrace : WordTrace (prefixWord ++ tailWord_3525626) baseStart_3525626 baseEnd_3525626 := by
    simpa [prefixWord, tailWord_3525626, baseEnd_3525626] using wordTrace_append hprefix tailTrace_3525626
  have hstable : (prefixWord ++ tailWord_3525626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525626).length < 2 ^ (prefixWord ++ tailWord_3525626).sum := by decide
  have hdescent : baseEnd_3525626 < baseStart_3525626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525629 : List Nat := [1, 4, 1, 1, 1, 2, 1, 12]
def baseStart_3525629 : Nat := 118140960795 + 3525629 * 2 ^ 59
def prefixEnd_3525629 : Nat := 4983230072969 + 3 ^ 40 * 3525629 * 2
def baseEnd_3525629 : Nat := 67049714312240433111979

theorem tailTrace_3525629 : CollatzResearch.WordTrace tailWord_3525629 prefixEnd_3525629 67049714312240433111979 := by
  unfold tailWord_3525629
  simp only [CollatzResearch.WordTrace]
  refine ⟨128590253744255737340331941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85726835829503824893554627 128590253744255737340331941)
  ·
    refine ⟨24110672577047950751312239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128590253744255737340331941 24110672577047950751312239)
    ·
      refine ⟨36166008865571926126968359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24110672577047950751312239 36166008865571926126968359)
      ·
        refine ⟨54249013298357889190452539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36166008865571926126968359 54249013298357889190452539)
        ·
          refine ⟨81373519947536833785678809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54249013298357889190452539 81373519947536833785678809)
          ·
            refine ⟨61030139960652625339259107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81373519947536833785678809 61030139960652625339259107)
            ·
              refine ⟨91545209940978938008888661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61030139960652625339259107 91545209940978938008888661)
              ·
                refine ⟨67049714312240433111979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 91545209940978938008888661 67049714312240433111979)
                ·
                  rfl

theorem cell23_3525629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 12].length) (baseStart_3525629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525629 prefixEnd_3525629 := by exact prefixLift 3525629
  have htrace : WordTrace (prefixWord ++ tailWord_3525629) baseStart_3525629 baseEnd_3525629 := by
    simpa [prefixWord, tailWord_3525629, baseEnd_3525629] using wordTrace_append hprefix tailTrace_3525629
  have hstable : (prefixWord ++ tailWord_3525629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525629).length < 2 ^ (prefixWord ++ tailWord_3525629).sum := by decide
  have hdescent : baseEnd_3525629 < baseStart_3525629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525633 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3525633 : Nat := 118140960795 + 3525633 * 2 ^ 59
def prefixEnd_3525633 : Nat := 4983230072969 + 3 ^ 40 * 3525633 * 2
def baseEnd_3525633 : Nat := 603448113451036559457805

theorem tailTrace_3525633 : CollatzResearch.WordTrace tailWord_3525633 prefixEnd_3525633 603448113451036559457805 := by
  unfold tailWord_3525633
  simp only [CollatzResearch.WordTrace]
  refine ⟨128590399636241246023477553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85726933090827497348985035 128590399636241246023477553)
  ·
    refine ⟨96442799727180934517608165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128590399636241246023477553 96442799727180934517608165)
    ·
      refine ⟨18083024948846425222051531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96442799727180934517608165 18083024948846425222051531)
      ·
        refine ⟨27124537423269637833077297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18083024948846425222051531 27124537423269637833077297)
        ·
          refine ⟨20343403067452228374807973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27124537423269637833077297 20343403067452228374807973)
          ·
            refine ⟨3814388075147292820276495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20343403067452228374807973 3814388075147292820276495)
            ·
              refine ⟨5721582112720939230414743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814388075147292820276495 5721582112720939230414743)
              ·
                refine ⟨8582373169081408845622115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721582112720939230414743 8582373169081408845622115)
                ·
                  refine ⟨12873559753622113268433173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8582373169081408845622115 12873559753622113268433173)
                  ·
                    refine ⟨603448113451036559457805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12873559753622113268433173 603448113451036559457805)
                    ·
                      rfl

theorem cell23_3525633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3525633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525633 prefixEnd_3525633 := by exact prefixLift 3525633
  have htrace : WordTrace (prefixWord ++ tailWord_3525633) baseStart_3525633 baseEnd_3525633 := by
    simpa [prefixWord, tailWord_3525633, baseEnd_3525633] using wordTrace_append hprefix tailTrace_3525633
  have hstable : (prefixWord ++ tailWord_3525633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525633).length < 2 ^ (prefixWord ++ tailWord_3525633).sum := by decide
  have hdescent : baseEnd_3525633 < baseStart_3525633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525640 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_3525640 : Nat := 118140960795 + 3525640 * 2 ^ 59
def prefixEnd_3525640 : Nat := 4983230072969 + 3 ^ 40 * 3525640 * 2
def baseEnd_3525640 : Nat := 1810347934717691150985883

theorem tailTrace_3525640 : CollatzResearch.WordTrace tailWord_3525640 prefixEnd_3525640 1810347934717691150985883 := by
  unfold tailWord_3525640
  simp only [CollatzResearch.WordTrace]
  refine ⟨64295327473607943109491187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85727103298143924145988249 64295327473607943109491187)
  ·
    refine ⟨96442991210411914664236781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64295327473607943109491187 96442991210411914664236781)
    ·
      refine ⟨36166121703904467999088793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96442991210411914664236781 36166121703904467999088793)
      ·
        refine ⟨27124591277928350999316595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36166121703904467999088793 27124591277928350999316595)
        ·
          refine ⟨40686886916892526498974893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27124591277928350999316595 40686886916892526498974893)
          ·
            refine ⟨15257582593834697437115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40686886916892526498974893 15257582593834697437115585)
            ·
              refine ⟨11443186945376023077836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15257582593834697437115585 11443186945376023077836689)
              ·
                refine ⟨8582390209032017308377517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443186945376023077836689 8582390209032017308377517)
                ·
                  refine ⟨3218396328387006490641569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8582390209032017308377517 3218396328387006490641569)
                  ·
                    refine ⟨2413797246290254867981177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218396328387006490641569 2413797246290254867981177)
                    ·
                      refine ⟨1810347934717691150985883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413797246290254867981177 1810347934717691150985883)
                      ·
                        rfl

theorem cell23_3525640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_3525640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525640 prefixEnd_3525640 := by exact prefixLift 3525640
  have htrace : WordTrace (prefixWord ++ tailWord_3525640) baseStart_3525640 baseEnd_3525640 := by
    simpa [prefixWord, tailWord_3525640, baseEnd_3525640] using wordTrace_append hprefix tailTrace_3525640
  have hstable : (prefixWord ++ tailWord_3525640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525640).length < 2 ^ (prefixWord ++ tailWord_3525640).sum := by decide
  have hdescent : baseEnd_3525640 < baseStart_3525640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525643 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 3]
def baseStart_3525643 : Nat := 118140960795 + 3525643 * 2 ^ 59
def prefixEnd_3525643 : Nat := 4983230072969 + 3 ^ 40 * 3525643 * 2
def baseEnd_3525643 : Nat := 1810349475159654639248369

theorem tailTrace_3525643 : CollatzResearch.WordTrace tailWord_3525643 prefixEnd_3525643 1810349475159654639248369 := by
  unfold tailWord_3525643
  simp only [CollatzResearch.WordTrace]
  refine ⟨128590764366205017731341583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85727176244136678487561055 128590764366205017731341583)
  ·
    refine ⟨192886146549307526597012375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128590764366205017731341583 192886146549307526597012375)
    ·
      refine ⟨289329219823961289895518563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192886146549307526597012375 289329219823961289895518563)
      ·
        refine ⟨433993829735941934843277845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289329219823961289895518563 433993829735941934843277845)
        ·
          refine ⟨20343460768872278195778649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 433993829735941934843277845 20343460768872278195778649)
          ·
            refine ⟨15257595576654208646833987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20343460768872278195778649 15257595576654208646833987)
            ·
              refine ⟨22886393364981312970250981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257595576654208646833987 22886393364981312970250981)
              ·
                refine ⟨4291198755933996181922059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22886393364981312970250981 4291198755933996181922059)
                ·
                  refine ⟨6436798133900994272883089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291198755933996181922059 6436798133900994272883089)
                  ·
                    refine ⟨4827598600425745704662317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6436798133900994272883089 4827598600425745704662317)
                    ·
                      refine ⟨1810349475159654639248369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827598600425745704662317 1810349475159654639248369)
                      ·
                        rfl

theorem cell23_3525643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 3].length) (baseStart_3525643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525643 prefixEnd_3525643 := by exact prefixLift 3525643
  have htrace : WordTrace (prefixWord ++ tailWord_3525643) baseStart_3525643 baseEnd_3525643 := by
    simpa [prefixWord, tailWord_3525643, baseEnd_3525643] using wordTrace_append hprefix tailTrace_3525643
  have hstable : (prefixWord ++ tailWord_3525643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525643).length < 2 ^ (prefixWord ++ tailWord_3525643).sum := by decide
  have hdescent : baseEnd_3525643 < baseStart_3525643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525646 : List Nat := [4, 1, 1, 2, 2, 3, 1, 9]
def baseStart_3525646 : Nat := 118140960795 + 3525646 * 2 ^ 59
def prefixEnd_3525646 : Nat := 4983230072969 + 3 ^ 40 * 3525646 * 2
def baseEnd_3525646 : Nat := 67050037614874745463365

theorem tailTrace_3525646 : CollatzResearch.WordTrace tailWord_3525646 prefixEnd_3525646 67050037614874745463365 := by
  unfold tailWord_3525646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16073859223149268655462599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85727249190129432829133861 16073859223149268655462599)
  ·
    refine ⟨24110788834723902983193899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16073859223149268655462599 24110788834723902983193899)
    ·
      refine ⟨36166183252085854474790849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24110788834723902983193899 36166183252085854474790849)
      ·
        refine ⟨27124637439064390856093137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36166183252085854474790849 27124637439064390856093137)
        ·
          refine ⟨20343478079298293142069853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27124637439064390856093137 20343478079298293142069853)
          ·
            refine ⟨7628804279736859928276195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20343478079298293142069853 7628804279736859928276195)
            ·
              refine ⟨11443206419605289892414293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628804279736859928276195 11443206419605289892414293)
              ·
                refine ⟨67050037614874745463365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11443206419605289892414293 67050037614874745463365)
                ·
                  rfl

theorem cell23_3525646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_3525646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525646 prefixEnd_3525646 := by exact prefixLift 3525646
  have htrace : WordTrace (prefixWord ++ tailWord_3525646) baseStart_3525646 baseEnd_3525646 := by
    simpa [prefixWord, tailWord_3525646, baseEnd_3525646] using wordTrace_append hprefix tailTrace_3525646
  have hstable : (prefixWord ++ tailWord_3525646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525646).length < 2 ^ (prefixWord ++ tailWord_3525646).sum := by decide
  have hdescent : baseEnd_3525646 < baseStart_3525646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3525649 : Nat := 118140960795 + 3525649 * 2 ^ 59
def prefixEnd_3525649 : Nat := 4983230072969 + 3 ^ 40 * 3525649 * 2
def baseEnd_3525649 : Nat := 1810352556043581615773341

theorem tailTrace_3525649 : CollatzResearch.WordTrace tailWord_3525649 prefixEnd_3525649 1810352556043581615773341 := by
  unfold tailWord_3525649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128590983204183280756060001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85727322136122187170706667 128590983204183280756060001)
  ·
    refine ⟨96443237403137460567045001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128590983204183280756060001 96443237403137460567045001)
    ·
      refine ⟨72332428052353095425283751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96443237403137460567045001 72332428052353095425283751)
      ·
        refine ⟨108498642078529643137925627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72332428052353095425283751 108498642078529643137925627)
        ·
          refine ⟨162747963117794464706888441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108498642078529643137925627 162747963117794464706888441)
          ·
            refine ⟨122060972338345848530166331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162747963117794464706888441 122060972338345848530166331)
            ·
              refine ⟨183091458507518772795249497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122060972338345848530166331 183091458507518772795249497)
              ·
                refine ⟨137318593880639079596437123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183091458507518772795249497 137318593880639079596437123)
                ·
                  refine ⟨205977890820958619394655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137318593880639079596437123 205977890820958619394655685)
                  ·
                    refine ⟨38620854528929741136497941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205977890820958619394655685 38620854528929741136497941)
                    ·
                      refine ⟨1810352556043581615773341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38620854528929741136497941 1810352556043581615773341)
                      ·
                        rfl

theorem cell23_3525649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3525649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525649 prefixEnd_3525649 := by exact prefixLift 3525649
  have htrace : WordTrace (prefixWord ++ tailWord_3525649) baseStart_3525649 baseEnd_3525649 := by
    simpa [prefixWord, tailWord_3525649, baseEnd_3525649] using wordTrace_append hprefix tailTrace_3525649
  have hstable : (prefixWord ++ tailWord_3525649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525649).length < 2 ^ (prefixWord ++ tailWord_3525649).sum := by decide
  have hdescent : baseEnd_3525649 < baseStart_3525649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525657 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 1, 2, 2]
def baseStart_3525657 : Nat := 118140960795 + 3525657 * 2 ^ 59
def prefixEnd_3525657 : Nat := 4983230072969 + 3 ^ 40 * 3525657 * 2
def baseEnd_3525657 : Nat := 1810356663888817584473305

theorem tailTrace_3525657 : CollatzResearch.WordTrace tailWord_3525657 prefixEnd_3525657 1810356663888817584473305 := by
  unfold tailWord_3525657
  simp only [CollatzResearch.WordTrace]
  refine ⟨128591274988154298122351225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85727516658769532081567483 128591274988154298122351225)
  ·
    refine ⟨96443456241115723591763419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128591274988154298122351225 96443456241115723591763419)
    ·
      refine ⟨144665184361673585387645129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96443456241115723591763419 144665184361673585387645129)
      ·
        refine ⟨108498888271255189040733847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144665184361673585387645129 108498888271255189040733847)
        ·
          refine ⟨162748332406882783561100771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108498888271255189040733847 162748332406882783561100771)
          ·
            refine ⟨244122498610324175341651157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162748332406882783561100771 244122498610324175341651157)
            ·
              refine ⟨5721621061179472859569949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244122498610324175341651157 5721621061179472859569949)
              ·
                refine ⟨2145607897942302322338731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5721621061179472859569949 2145607897942302322338731)
                ·
                  refine ⟨3218411846913453483508097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145607897942302322338731 3218411846913453483508097)
                  ·
                    refine ⟨2413808885185090112631073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218411846913453483508097 2413808885185090112631073)
                    ·
                      refine ⟨1810356663888817584473305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413808885185090112631073 1810356663888817584473305)
                      ·
                        rfl

theorem cell23_3525657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_3525657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525657 prefixEnd_3525657 := by exact prefixLift 3525657
  have htrace : WordTrace (prefixWord ++ tailWord_3525657) baseStart_3525657 baseEnd_3525657 := by
    simpa [prefixWord, tailWord_3525657, baseEnd_3525657] using wordTrace_append hprefix tailTrace_3525657
  have hstable : (prefixWord ++ tailWord_3525657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525657).length < 2 ^ (prefixWord ++ tailWord_3525657).sum := by decide
  have hdescent : baseEnd_3525657 < baseStart_3525657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525674 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3525674 : Nat := 118140960795 + 3525674 * 2 ^ 59
def prefixEnd_3525674 : Nat := 4983230072969 + 3 ^ 40 * 3525674 * 2
def baseEnd_3525674 : Nat := 1810365393059944017960727

theorem tailTrace_3525674 : CollatzResearch.WordTrace tailWord_3525674 prefixEnd_3525674 1810365393059944017960727 := by
  unfold tailWord_3525674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32147973757273177506430019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85727930019395140017146717 32147973757273177506430019)
  ·
    refine ⟨48221960635909766259645029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32147973757273177506430019 48221960635909766259645029)
    ·
      refine ⟨9041617619233081173683443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48221960635909766259645029 9041617619233081173683443)
      ·
        refine ⟨13562426428849621760525165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041617619233081173683443 13562426428849621760525165)
        ·
          refine ⟨5085909910818608160196937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13562426428849621760525165 5085909910818608160196937)
          ·
            refine ⟨3814432433113956120147703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085909910818608160196937 3814432433113956120147703)
            ·
              refine ⟨5721648649670934180221555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814432433113956120147703 5721648649670934180221555)
              ·
                refine ⟨8582472974506401270332333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721648649670934180221555 8582472974506401270332333)
                ·
                  refine ⟨3218427365439900476374625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8582472974506401270332333 3218427365439900476374625)
                  ·
                    refine ⟨2413820524079925357280969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218427365439900476374625 2413820524079925357280969)
                    ·
                      refine ⟨1810365393059944017960727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413820524079925357280969 1810365393059944017960727)
                      ·
                        rfl

theorem cell23_3525674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3525674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525674 prefixEnd_3525674 := by exact prefixLift 3525674
  have htrace : WordTrace (prefixWord ++ tailWord_3525674) baseStart_3525674 baseEnd_3525674 := by
    simpa [prefixWord, tailWord_3525674, baseEnd_3525674] using wordTrace_append hprefix tailTrace_3525674
  have hstable : (prefixWord ++ tailWord_3525674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525674).length < 2 ^ (prefixWord ++ tailWord_3525674).sum := by decide
  have hdescent : baseEnd_3525674 < baseStart_3525674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_3525679 : Nat := 118140960795 + 3525679 * 2 ^ 59
def prefixEnd_3525679 : Nat := 4983230072969 + 3 ^ 40 * 3525679 * 2
def baseEnd_3525679 : Nat := 1810367960463216498398203

theorem tailTrace_3525679 : CollatzResearch.WordTrace tailWord_3525679 prefixEnd_3525679 1810367960463216498398203 := by
  unfold tailWord_3525679
  simp only [CollatzResearch.WordTrace]
  refine ⟨128592077394074595879652091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85728051596049730586434727 128592077394074595879652091)
  ·
    refine ⟨192888116091111893819478137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128592077394074595879652091 192888116091111893819478137)
    ·
      refine ⟨144666087068333920364608603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192888116091111893819478137 144666087068333920364608603)
      ·
        refine ⟨216999130602500880546912905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144666087068333920364608603 216999130602500880546912905)
        ·
          refine ⟨162749347951875660410184679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216999130602500880546912905 162749347951875660410184679)
          ·
            refine ⟨244124021927813490615277019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162749347951875660410184679 244124021927813490615277019)
            ·
              refine ⟨366186032891720235922915529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244124021927813490615277019 366186032891720235922915529)
              ·
                refine ⟨274639524668790176942186647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366186032891720235922915529 274639524668790176942186647)
                ·
                  refine ⟨411959287003185265413279971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274639524668790176942186647 411959287003185265413279971)
                  ·
                    refine ⟨617938930504777898119919957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411959287003185265413279971 617938930504777898119919957)
                    ·
                      refine ⟨1810367960463216498398203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 617938930504777898119919957 1810367960463216498398203)
                      ·
                        rfl

theorem cell23_3525679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_3525679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525679 prefixEnd_3525679 := by exact prefixLift 3525679
  have htrace : WordTrace (prefixWord ++ tailWord_3525679) baseStart_3525679 baseEnd_3525679 := by
    simpa [prefixWord, tailWord_3525679, baseEnd_3525679] using wordTrace_append hprefix tailTrace_3525679
  have hstable : (prefixWord ++ tailWord_3525679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525679).length < 2 ^ (prefixWord ++ tailWord_3525679).sum := by decide
  have hdescent : baseEnd_3525679 < baseStart_3525679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 3, 3, 2]
def baseStart_3525683 : Nat := 118140960795 + 3525683 * 2 ^ 59
def prefixEnd_3525683 : Nat := 4983230072969 + 3 ^ 40 * 3525683 * 2
def baseEnd_3525683 : Nat := 1810370014385834482748185

theorem tailTrace_3525683 : CollatzResearch.WordTrace tailWord_3525683 prefixEnd_3525683 1810370014385834482748185 := by
  unfold tailWord_3525683
  simp only [CollatzResearch.WordTrace]
  refine ⟨128592223286060104562797703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85728148857373403041865135 128592223286060104562797703)
  ·
    refine ⟨192888334929090156844196555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128592223286060104562797703 192888334929090156844196555)
    ·
      refine ⟨289332502393635235266294833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192888334929090156844196555 289332502393635235266294833)
      ·
        refine ⟨216999376795226426449721125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289332502393635235266294833 216999376795226426449721125)
        ·
          refine ⟨40687383149104954959322711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216999376795226426449721125 40687383149104954959322711)
          ·
            refine ⟨61031074723657432438984067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40687383149104954959322711 61031074723657432438984067)
            ·
              refine ⟨91546612085486148658476101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61031074723657432438984067 91546612085486148658476101)
              ·
                refine ⟨17164989766028652873464269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91546612085486148658476101 17164989766028652873464269)
                ·
                  refine ⟨6436871162260744827549101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17164989766028652873464269 6436871162260744827549101)
                  ·
                    refine ⟨2413826685847779310330913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6436871162260744827549101 2413826685847779310330913)
                    ·
                      refine ⟨1810370014385834482748185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413826685847779310330913 1810370014385834482748185)
                      ·
                        rfl

theorem cell23_3525683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3, 2].length) (baseStart_3525683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525683 prefixEnd_3525683 := by exact prefixLift 3525683
  have htrace : WordTrace (prefixWord ++ tailWord_3525683) baseStart_3525683 baseEnd_3525683 := by
    simpa [prefixWord, tailWord_3525683, baseEnd_3525683] using wordTrace_append hprefix tailTrace_3525683
  have hstable : (prefixWord ++ tailWord_3525683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525683).length < 2 ^ (prefixWord ++ tailWord_3525683).sum := by decide
  have hdescent : baseEnd_3525683 < baseStart_3525683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525684 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3525684 : Nat := 118140960795 + 3525684 * 2 ^ 59
def prefixEnd_3525684 : Nat := 4983230072969 + 3 ^ 40 * 3525684 * 2
def baseEnd_3525684 : Nat := 603456842622162992945227

theorem tailTrace_3525684 : CollatzResearch.WordTrace tailWord_3525684 prefixEnd_3525684 603456842622162992945227 := by
  unfold tailWord_3525684
  simp only [CollatzResearch.WordTrace]
  refine ⟨64296129879528240866792053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85728173172704321155722737 64296129879528240866792053)
  ·
    refine ⟨6027762176205772581261755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64296129879528240866792053 6027762176205772581261755)
    ·
      refine ⟨9041643264308658871892633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027762176205772581261755 9041643264308658871892633)
      ·
        refine ⟨6781232448231494153919475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9041643264308658871892633 6781232448231494153919475)
        ·
          refine ⟨10171848672347241230879213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781232448231494153919475 10171848672347241230879213)
          ·
            refine ⟨3814443252130215461579705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10171848672347241230879213 3814443252130215461579705)
            ·
              refine ⟨2860832439097661596184779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814443252130215461579705 2860832439097661596184779)
              ·
                refine ⟨4291248658646492394277169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860832439097661596184779 4291248658646492394277169)
                ·
                  refine ⟨3218436493984869295707877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291248658646492394277169 3218436493984869295707877)
                  ·
                    refine ⟨603456842622162992945227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218436493984869295707877 603456842622162992945227)
                    ·
                      rfl

theorem cell23_3525684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3525684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525684 prefixEnd_3525684 := by exact prefixLift 3525684
  have htrace : WordTrace (prefixWord ++ tailWord_3525684) baseStart_3525684 baseEnd_3525684 := by
    simpa [prefixWord, tailWord_3525684, baseEnd_3525684] using wordTrace_append hprefix tailTrace_3525684
  have hstable : (prefixWord ++ tailWord_3525684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525684).length < 2 ^ (prefixWord ++ tailWord_3525684).sum := by decide
  have hdescent : baseEnd_3525684 < baseStart_3525684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525713 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_3525713 : Nat := 118140960795 + 3525713 * 2 ^ 59
def prefixEnd_3525713 : Nat := 4983230072969 + 3 ^ 40 * 3525713 * 2
def baseEnd_3525713 : Nat := 1810385418805469365373047

theorem tailTrace_3525713 : CollatzResearch.WordTrace tailWord_3525713 prefixEnd_3525713 1810385418805469365373047 := by
  unfold tailWord_3525713
  simp only [CollatzResearch.WordTrace]
  refine ⟨128593317475951419686389793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85728878317300946457593195 128593317475951419686389793)
  ·
    refine ⟨96444988106963564764792345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128593317475951419686389793 96444988106963564764792345)
    ·
      refine ⟨72333741080222673573594259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96444988106963564764792345 72333741080222673573594259)
      ·
        refine ⟨108500611620334010360391389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72333741080222673573594259 108500611620334010360391389)
        ·
          refine ⟨40687729357625253885146771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108500611620334010360391389 40687729357625253885146771)
          ·
            refine ⟨61031594036437880827720157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40687729357625253885146771 61031594036437880827720157)
            ·
              refine ⟨22886847763664205310395059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61031594036437880827720157 22886847763664205310395059)
              ·
                refine ⟨34330271645496307965592589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22886847763664205310395059 34330271645496307965592589)
                ·
                  refine ⟨12873851867061115487097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34330271645496307965592589 12873851867061115487097221)
                  ·
                    refine ⟨2413847225073959153830729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12873851867061115487097221 2413847225073959153830729)
                    ·
                      refine ⟨1810385418805469365373047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413847225073959153830729 1810385418805469365373047)
                      ·
                        rfl

theorem cell23_3525713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_3525713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525713 prefixEnd_3525713 := by exact prefixLift 3525713
  have htrace : WordTrace (prefixWord ++ tailWord_3525713) baseStart_3525713 baseEnd_3525713 := by
    simpa [prefixWord, tailWord_3525713, baseEnd_3525713] using wordTrace_append hprefix tailTrace_3525713
  have hstable : (prefixWord ++ tailWord_3525713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525713).length < 2 ^ (prefixWord ++ tailWord_3525713).sum := by decide
  have hdescent : baseEnd_3525713 < baseStart_3525713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525717 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3525717 : Nat := 118140960795 + 3525717 * 2 ^ 59
def prefixEnd_3525717 : Nat := 4983230072969 + 3 ^ 40 * 3525717 * 2
def baseEnd_3525717 : Nat := 1810387472728087349723029

theorem tailTrace_3525717 : CollatzResearch.WordTrace tailWord_3525717 prefixEnd_3525717 1810387472728087349723029 := by
  unfold tailWord_3525717
  simp only [CollatzResearch.WordTrace]
  refine ⟨128593463367936928369535405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85728975578624618913023603 128593463367936928369535405)
  ·
    refine ⟨48222548762976348138575777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128593463367936928369535405 48222548762976348138575777)
    ·
      refine ⟨36166911572232261103931833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48222548762976348138575777 36166911572232261103931833)
      ·
        refine ⟨27125183679174195827948875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36166911572232261103931833 27125183679174195827948875)
        ·
          refine ⟨40687775518761293741923313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27125183679174195827948875 40687775518761293741923313)
          ·
            refine ⟨30515831639070970306442485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40687775518761293741923313 30515831639070970306442485)
            ·
              refine ⟨2860859216162903466228983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30515831639070970306442485 2860859216162903466228983)
              ·
                refine ⟨4291288824244355199343475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860859216162903466228983 4291288824244355199343475)
                ·
                  refine ⟨6436933236366532799015213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291288824244355199343475 6436933236366532799015213)
                  ·
                    refine ⟨2413849963637449799630705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6436933236366532799015213 2413849963637449799630705)
                    ·
                      refine ⟨1810387472728087349723029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413849963637449799630705 1810387472728087349723029)
                      ·
                        rfl

theorem cell23_3525717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3525717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525717 prefixEnd_3525717 := by exact prefixLift 3525717
  have htrace : WordTrace (prefixWord ++ tailWord_3525717) baseStart_3525717 baseEnd_3525717 := by
    simpa [prefixWord, tailWord_3525717, baseEnd_3525717] using wordTrace_append hprefix tailTrace_3525717
  have hstable : (prefixWord ++ tailWord_3525717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525717).length < 2 ^ (prefixWord ++ tailWord_3525717).sum := by decide
  have hdescent : baseEnd_3525717 < baseStart_3525717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525725 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3525725 : Nat := 118140960795 + 3525725 * 2 ^ 59
def prefixEnd_3525725 : Nat := 4983230072969 + 3 ^ 40 * 3525725 * 2
def baseEnd_3525725 : Nat := 1810391580573323318422993

theorem tailTrace_3525725 : CollatzResearch.WordTrace tailWord_3525725 prefixEnd_3525725 1810391580573323318422993 := by
  unfold tailWord_3525725
  simp only [CollatzResearch.WordTrace]
  refine ⟨128593755151907945735826629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85729170101271963823884419 128593755151907945735826629)
  ·
    refine ⟨24111329090982739825467493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128593755151907945735826629 24111329090982739825467493)
    ·
      refine ⟨4520874204559263717275155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24111329090982739825467493 4520874204559263717275155)
      ·
        refine ⟨6781311306838895575912733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520874204559263717275155 6781311306838895575912733)
        ·
          refine ⟨2542991740064585840967275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6781311306838895575912733 2542991740064585840967275)
          ·
            refine ⟨3814487610096878761450913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542991740064585840967275 3814487610096878761450913)
            ·
              refine ⟨2860865707572659071088185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814487610096878761450913 2860865707572659071088185)
              ·
                refine ⟨2145649280679494303316139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860865707572659071088185 2145649280679494303316139)
                ·
                  refine ⟨3218473921019241454974209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145649280679494303316139 3218473921019241454974209)
                  ·
                    refine ⟨2413855440764431091230657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218473921019241454974209 2413855440764431091230657)
                    ·
                      refine ⟨1810391580573323318422993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2413855440764431091230657 1810391580573323318422993)
                      ·
                        rfl

theorem cell23_3525725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3525725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525725 prefixEnd_3525725 := by exact prefixLift 3525725
  have htrace : WordTrace (prefixWord ++ tailWord_3525725) baseStart_3525725 baseEnd_3525725 := by
    simpa [prefixWord, tailWord_3525725, baseEnd_3525725] using wordTrace_append hprefix tailTrace_3525725
  have hstable : (prefixWord ++ tailWord_3525725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525725).length < 2 ^ (prefixWord ++ tailWord_3525725).sum := by decide
  have hdescent : baseEnd_3525725 < baseStart_3525725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525753 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 7]
def baseStart_3525753 : Nat := 118140960795 + 3525753 * 2 ^ 59
def prefixEnd_3525753 : Nat := 4983230072969 + 3 ^ 40 * 3525753 * 2
def baseEnd_3525753 : Nat := 201156217559072134319207

theorem tailTrace_3525753 : CollatzResearch.WordTrace tailWord_3525753 prefixEnd_3525753 201156217559072134319207 := by
  unfold tailWord_3525753
  simp only [CollatzResearch.WordTrace]
  refine ⟨128594776395806506517845913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85729850930537671011897275 128594776395806506517845913)
  ·
    refine ⟨96446082296854879888384435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128594776395806506517845913 96446082296854879888384435)
    ·
      refine ⟨144669123445282319832576653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96446082296854879888384435 144669123445282319832576653)
      ·
        refine ⟨54250921291980869937216245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144669123445282319832576653 54250921291980869937216245)
        ·
          refine ⟨5086023871123206556614023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54250921291980869937216245 5086023871123206556614023)
          ·
            refine ⟨7629035806684809834921035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086023871123206556614023 7629035806684809834921035)
            ·
              refine ⟨11443553710027214752381553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629035806684809834921035 11443553710027214752381553)
              ·
                refine ⟨8582665282520411064286165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443553710027214752381553 8582665282520411064286165)
                ·
                  refine ⟨201156217559072134319207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8582665282520411064286165 201156217559072134319207)
                  ·
                    rfl

theorem cell23_3525753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_3525753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525753 prefixEnd_3525753 := by exact prefixLift 3525753
  have htrace : WordTrace (prefixWord ++ tailWord_3525753) baseStart_3525753 baseEnd_3525753 := by
    simpa [prefixWord, tailWord_3525753, baseEnd_3525753] using wordTrace_append hprefix tailTrace_3525753
  have hstable : (prefixWord ++ tailWord_3525753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525753).length < 2 ^ (prefixWord ++ tailWord_3525753).sum := by decide
  have hdescent : baseEnd_3525753 < baseStart_3525753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525770 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_3525770 : Nat := 118140960795 + 3525770 * 2 ^ 59
def prefixEnd_3525770 : Nat := 4983230072969 + 3 ^ 40 * 3525770 * 2
def baseEnd_3525770 : Nat := 201157187466975071373365

theorem tailTrace_3525770 : CollatzResearch.WordTrace tailWord_3525770 prefixEnd_3525770 201157187466975071373365 := by
  unfold tailWord_3525770
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148849109186229605303691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85730264291163278947476509 32148849109186229605303691)
  ·
    refine ⟨48223273663779344407955537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32148849109186229605303691 48223273663779344407955537)
    ·
      refine ⟨36167455247834508305966653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48223273663779344407955537 36167455247834508305966653)
      ·
        refine ⟨13562795717937940614737495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36167455247834508305966653 13562795717937940614737495)
        ·
          refine ⟨20344193576906910922106243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13562795717937940614737495 20344193576906910922106243)
          ·
            refine ⟨30516290365360366383159365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20344193576906910922106243 30516290365360366383159365)
            ·
              refine ⟨5721804443505068696842381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30516290365360366383159365 5721804443505068696842381)
              ·
                refine ⟨2145676666314400761315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5721804443505068696842381 2145676666314400761315893)
                ·
                  refine ⟨201157187466975071373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2145676666314400761315893 201157187466975071373365)
                  ·
                    rfl

theorem cell23_3525770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_3525770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525770 prefixEnd_3525770 := by exact prefixLift 3525770
  have htrace : WordTrace (prefixWord ++ tailWord_3525770) baseStart_3525770 baseEnd_3525770 := by
    simpa [prefixWord, tailWord_3525770, baseEnd_3525770] using wordTrace_append hprefix tailTrace_3525770
  have hstable : (prefixWord ++ tailWord_3525770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525770).length < 2 ^ (prefixWord ++ tailWord_3525770).sum := by decide
  have hdescent : baseEnd_3525770 < baseStart_3525770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525776 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_3525776 : Nat := 118140960795 + 3525776 * 2 ^ 59
def prefixEnd_3525776 : Nat := 4983230072969 + 3 ^ 40 * 3525776 * 2
def baseEnd_3525776 : Nat := 1810417768086702618885257

theorem tailTrace_3525776 : CollatzResearch.WordTrace tailWord_3525776 prefixEnd_3525776 1810417768086702618885257 := by
  unfold tailWord_3525776
  simp only [CollatzResearch.WordTrace]
  refine ⟨64297807637361590722966591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85730410183148787630622121 64297807637361590722966591)
  ·
    refine ⟨96446711456042386084449887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64297807637361590722966591 96446711456042386084449887)
    ·
      refine ⟨144670067184063579126674831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96446711456042386084449887 144670067184063579126674831)
      ·
        refine ⟨217005100776095368690012247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144670067184063579126674831 217005100776095368690012247)
        ·
          refine ⟨325507651164143053035018371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217005100776095368690012247 325507651164143053035018371)
          ·
            refine ⟨488261476746214579552527557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325507651164143053035018371 488261476746214579552527557)
            ·
              refine ⟨91549026889915233666098917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488261476746214579552527557 91549026889915233666098917)
              ·
                refine ⟨17165442541859106312393547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91549026889915233666098917 17165442541859106312393547)
                ·
                  refine ⟨25748163812788659468590321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17165442541859106312393547 25748163812788659468590321)
                  ·
                    refine ⟨19311122859591494601442741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25748163812788659468590321 19311122859591494601442741)
                    ·
                      refine ⟨1810417768086702618885257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19311122859591494601442741 1810417768086702618885257)
                      ·
                        rfl

theorem cell23_3525776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_3525776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525776 prefixEnd_3525776 := by exact prefixLift 3525776
  have htrace : WordTrace (prefixWord ++ tailWord_3525776) baseStart_3525776 baseEnd_3525776 := by
    simpa [prefixWord, tailWord_3525776, baseEnd_3525776] using wordTrace_append hprefix tailTrace_3525776
  have hstable : (prefixWord ++ tailWord_3525776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525776).length < 2 ^ (prefixWord ++ tailWord_3525776).sum := by decide
  have hdescent : baseEnd_3525776 < baseStart_3525776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525816 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_3525816 : Nat := 118140960795 + 3525816 * 2 ^ 59
def prefixEnd_3525816 : Nat := 4983230072969 + 3 ^ 40 * 3525816 * 2
def baseEnd_3525816 : Nat := 1810438307312882462385073

theorem tailTrace_3525816 : CollatzResearch.WordTrace tailWord_3525816 prefixEnd_3525816 1810438307312882462385073 := by
  unfold tailWord_3525816
  simp only [CollatzResearch.WordTrace]
  refine ⟨64298537097289134138694651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85731382796385512184926201 64298537097289134138694651)
  ·
    refine ⟨96447805645933701208041977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64298537097289134138694651 96447805645933701208041977)
    ·
      refine ⟨72335854234450275906031483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96447805645933701208041977 72335854234450275906031483)
      ·
        refine ⟨108503781351675413859047225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72335854234450275906031483 108503781351675413859047225)
        ·
          refine ⟨81377836013756560394285419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108503781351675413859047225 81377836013756560394285419)
          ·
            refine ⟨122066754020634840591428129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81377836013756560394285419 122066754020634840591428129)
            ·
              refine ⟨91550065515476130443571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122066754020634840591428129 91550065515476130443571097)
              ·
                refine ⟨68662549136607097832678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91550065515476130443571097 68662549136607097832678323)
                ·
                  refine ⟨102993823704910646749017485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68662549136607097832678323 102993823704910646749017485)
                  ·
                    refine ⟨38622683889341492530881557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102993823704910646749017485 38622683889341492530881557)
                    ·
                      refine ⟨1810438307312882462385073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38622683889341492530881557 1810438307312882462385073)
                      ·
                        rfl

theorem cell23_3525816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_3525816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525816 prefixEnd_3525816 := by exact prefixLift 3525816
  have htrace : WordTrace (prefixWord ++ tailWord_3525816) baseStart_3525816 baseEnd_3525816 := by
    simpa [prefixWord, tailWord_3525816, baseEnd_3525816] using wordTrace_append hprefix tailTrace_3525816
  have hstable : (prefixWord ++ tailWord_3525816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525816).length < 2 ^ (prefixWord ++ tailWord_3525816).sum := by decide
  have hdescent : baseEnd_3525816 < baseStart_3525816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525823 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_3525823 : Nat := 118140960795 + 3525823 * 2 ^ 59
def prefixEnd_3525823 : Nat := 4983230072969 + 3 ^ 40 * 3525823 * 2
def baseEnd_3525823 : Nat := 1810441901677463934997541

theorem tailTrace_3525823 : CollatzResearch.WordTrace tailWord_3525823 prefixEnd_3525823 1810441901677463934997541 := by
  unfold tailWord_3525823
  simp only [CollatzResearch.WordTrace]
  refine ⟨128597329505552908472894123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85731553003701938981929415 128597329505552908472894123)
  ·
    refine ⟨192895994258329362709341185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128597329505552908472894123 192895994258329362709341185)
    ·
      refine ⟨144671995693747022032005889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192895994258329362709341185 144671995693747022032005889)
      ·
        refine ⟨108503996770310266524004417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144671995693747022032005889 108503996770310266524004417)
        ·
          refine ⟨81377997577732699893003313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108503996770310266524004417 81377997577732699893003313)
          ·
            refine ⟨61033498183299524919752485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81377997577732699893003313 61033498183299524919752485)
            ·
              refine ⟨11443780909368660922453591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61033498183299524919752485 11443780909368660922453591)
              ·
                refine ⟨17165671364052991383680387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443780909368660922453591 17165671364052991383680387)
                ·
                  refine ⟨25748507046079487075520581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17165671364052991383680387 25748507046079487075520581)
                  ·
                    refine ⟨4827845071139903826660109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25748507046079487075520581 4827845071139903826660109)
                    ·
                      refine ⟨1810441901677463934997541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4827845071139903826660109 1810441901677463934997541)
                      ·
                        rfl

theorem cell23_3525823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_3525823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525823 prefixEnd_3525823 := by exact prefixLift 3525823
  have htrace : WordTrace (prefixWord ++ tailWord_3525823) baseStart_3525823 baseEnd_3525823 := by
    simpa [prefixWord, tailWord_3525823, baseEnd_3525823] using wordTrace_append hprefix tailTrace_3525823
  have hstable : (prefixWord ++ tailWord_3525823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525823).length < 2 ^ (prefixWord ++ tailWord_3525823).sum := by decide
  have hdescent : baseEnd_3525823 < baseStart_3525823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525860 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 6]
def baseStart_3525860 : Nat := 118140960795 + 3525860 * 2 ^ 59
def prefixEnd_3525860 : Nat := 4983230072969 + 3 ^ 40 * 3525860 * 2
def baseEnd_3525860 : Nat := 201162322273520032248319

theorem tailTrace_3525860 : CollatzResearch.WordTrace tailWord_3525860 prefixEnd_3525860 201162322273520032248319 := by
  unfold tailWord_3525860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64299339503209431895995517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85732452670945909194660689 64299339503209431895995517)
  ·
    refine ⟨24112252313703536960998319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64299339503209431895995517 24112252313703536960998319)
    ·
      refine ⟨36168378470555305441497479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24112252313703536960998319 36168378470555305441497479)
      ·
        refine ⟨54252567705832958162246219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36168378470555305441497479 54252567705832958162246219)
        ·
          refine ⟨81378851558749437243369329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54252567705832958162246219 81378851558749437243369329)
          ·
            refine ⟨61034138669062077932526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81378851558749437243369329 61034138669062077932526997)
            ·
              refine ⟨2860975250112284903087203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61034138669062077932526997 2860975250112284903087203)
              ·
                refine ⟨4291462875168427354630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860975250112284903087203 4291462875168427354630805)
                ·
                  refine ⟨201162322273520032248319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4291462875168427354630805 201162322273520032248319)
                  ·
                    rfl

theorem cell23_3525860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_3525860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525860 prefixEnd_3525860 := by exact prefixLift 3525860
  have htrace : WordTrace (prefixWord ++ tailWord_3525860) baseStart_3525860 baseEnd_3525860 := by
    simpa [prefixWord, tailWord_3525860, baseEnd_3525860] using wordTrace_append hprefix tailTrace_3525860
  have hstable : (prefixWord ++ tailWord_3525860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525860).length < 2 ^ (prefixWord ++ tailWord_3525860).sum := by decide
  have hdescent : baseEnd_3525860 < baseStart_3525860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525977 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3525977 : Nat := 118140960795 + 3525977 * 2 ^ 59
def prefixEnd_3525977 : Nat := 4983230072969 + 3 ^ 40 * 3525977 * 2
def baseEnd_3525977 : Nat := 1810520977698256332471833

theorem tailTrace_3525977 : CollatzResearch.WordTrace tailWord_3525977 prefixEnd_3525977 1810520977698256332471833 := by
  unfold tailWord_3525977
  simp only [CollatzResearch.WordTrace]
  refine ⟨128602946346994992774000185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85735297564663328516000123 128602946346994992774000185)
  ·
    refine ⟨96452209760246244580500139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128602946346994992774000185 96452209760246244580500139)
    ·
      refine ⟨144678314640369366870750209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96452209760246244580500139 144678314640369366870750209)
      ·
        refine ⟨108508735980277025153062657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144678314640369366870750209 108508735980277025153062657)
        ·
          refine ⟨81381551985207768864796993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108508735980277025153062657 81381551985207768864796993)
          ·
            refine ⟨61036163988905826648597745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81381551985207768864796993 61036163988905826648597745)
            ·
              refine ⟨45777122991679369986448309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61036163988905826648597745 45777122991679369986448309)
              ·
                refine ⟨4291605280469940936229529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45777122991679369986448309 4291605280469940936229529)
                ·
                  refine ⟨3218703960352455702172147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291605280469940936229529 3218703960352455702172147)
                  ·
                    refine ⟨4828055940528683553258221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218703960352455702172147 4828055940528683553258221)
                    ·
                      refine ⟨1810520977698256332471833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828055940528683553258221 1810520977698256332471833)
                      ·
                        rfl

theorem cell23_3525977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3525977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525977 prefixEnd_3525977 := by exact prefixLift 3525977
  have htrace : WordTrace (prefixWord ++ tailWord_3525977) baseStart_3525977 baseEnd_3525977 := by
    simpa [prefixWord, tailWord_3525977, baseEnd_3525977] using wordTrace_append hprefix tailTrace_3525977
  have hstable : (prefixWord ++ tailWord_3525977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525977).length < 2 ^ (prefixWord ++ tailWord_3525977).sum := by decide
  have hdescent : baseEnd_3525977 < baseStart_3525977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525993 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_3525993 : Nat := 118140960795 + 3525993 * 2 ^ 59
def prefixEnd_3525993 : Nat := 4983230072969 + 3 ^ 40 * 3525993 * 2
def baseEnd_3525993 : Nat := 603509731129576089957253

theorem tailTrace_3525993 : CollatzResearch.WordTrace tailWord_3525993 prefixEnd_3525993 603509731129576089957253 := by
  unfold tailWord_3525993
  simp only [CollatzResearch.WordTrace]
  refine ⟨128603529914937027506582633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85735686609958018337721755 128603529914937027506582633)
  ·
    refine ⟨96452647436202770629936975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128603529914937027506582633 96452647436202770629936975)
    ·
      refine ⟨144678971154304155944905463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96452647436202770629936975 144678971154304155944905463)
      ·
        refine ⟨217018456731456233917358195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144678971154304155944905463 217018456731456233917358195)
        ·
          refine ⟨325527685097184350876037293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217018456731456233917358195 325527685097184350876037293)
          ·
            refine ⟨122072881911444131578513985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325527685097184350876037293 122072881911444131578513985)
            ·
              refine ⟨91554661433583098683885489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122072881911444131578513985 91554661433583098683885489)
              ·
                refine ⟨68665996075187324012914117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91554661433583098683885489 68665996075187324012914117)
                ·
                  refine ⟨12874874264097623252421397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68665996075187324012914117 12874874264097623252421397)
                  ·
                    refine ⟨603509731129576089957253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12874874264097623252421397 603509731129576089957253)
                    ·
                      rfl

theorem cell23_3525993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_3525993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3525993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3525993 prefixEnd_3525993 := by exact prefixLift 3525993
  have htrace : WordTrace (prefixWord ++ tailWord_3525993) baseStart_3525993 baseEnd_3525993 := by
    simpa [prefixWord, tailWord_3525993, baseEnd_3525993] using wordTrace_append hprefix tailTrace_3525993
  have hstable : (prefixWord ++ tailWord_3525993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525993).length < 2 ^ (prefixWord ++ tailWord_3525993).sum := by decide
  have hdescent : baseEnd_3525993 < baseStart_3525993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526033 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3526033 : Nat := 118140960795 + 3526033 * 2 ^ 59
def prefixEnd_3526033 : Nat := 4983230072969 + 3 ^ 40 * 3526033 * 2
def baseEnd_3526033 : Nat := 1810549732614908113371575

theorem tailTrace_3526033 : CollatzResearch.WordTrace tailWord_3526033 prefixEnd_3526033 1810549732614908113371575 := by
  unfold tailWord_3526033
  simp only [CollatzResearch.WordTrace]
  refine ⟨128604988834792114338038753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85736659223194742892025835 128604988834792114338038753)
  ·
    refine ⟨96453741626094085753529065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128604988834792114338038753 96453741626094085753529065)
    ·
      refine ⟨72340306219570564315146799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96453741626094085753529065 72340306219570564315146799)
      ·
        refine ⟨108510459329355846472720199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72340306219570564315146799 108510459329355846472720199)
        ·
          refine ⟨162765688994033769709080299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108510459329355846472720199 162765688994033769709080299)
          ·
            refine ⟨244148533491050654563620449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162765688994033769709080299 244148533491050654563620449)
            ·
              refine ⟨183111400118287990922715337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244148533491050654563620449 183111400118287990922715337)
              ·
                refine ⟨137333550088715993192036503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183111400118287990922715337 137333550088715993192036503)
                ·
                  refine ⟨206000325133073989788054755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137333550088715993192036503 206000325133073989788054755)
                  ·
                    refine ⟨309000487699610984682082133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206000325133073989788054755 309000487699610984682082133)
                    ·
                      refine ⟨1810549732614908113371575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 309000487699610984682082133 1810549732614908113371575)
                      ·
                        rfl

theorem cell23_3526033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3526033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526033 prefixEnd_3526033 := by exact prefixLift 3526033
  have htrace : WordTrace (prefixWord ++ tailWord_3526033) baseStart_3526033 baseEnd_3526033 := by
    simpa [prefixWord, tailWord_3526033, baseEnd_3526033] using wordTrace_append hprefix tailTrace_3526033
  have hstable : (prefixWord ++ tailWord_3526033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526033).length < 2 ^ (prefixWord ++ tailWord_3526033).sum := by decide
  have hdescent : baseEnd_3526033 < baseStart_3526033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526043 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_3526043 : Nat := 118140960795 + 3526043 * 2 ^ 59
def prefixEnd_3526043 : Nat := 4983230072969 + 3 ^ 40 * 3526043 * 2
def baseEnd_3526043 : Nat := 1810554867421453074246529

theorem tailTrace_3526043 : CollatzResearch.WordTrace tailWord_3526043 prefixEnd_3526043 1810554867421453074246529 := by
  unfold tailWord_3526043
  simp only [CollatzResearch.WordTrace]
  refine ⟨128605353564755886045902783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85736902376503924030601855 128605353564755886045902783)
  ·
    refine ⟨192908030347133829068854175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128605353564755886045902783 192908030347133829068854175)
    ·
      refine ⟨289362045520700743603281263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192908030347133829068854175 289362045520700743603281263)
      ·
        refine ⟨434043068281051115404921895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289362045520700743603281263 434043068281051115404921895)
        ·
          refine ⟨651064602421576673107382843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434043068281051115404921895 651064602421576673107382843)
          ·
            refine ⟨976596903632365009661074265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651064602421576673107382843 976596903632365009661074265)
            ·
              refine ⟨732447677724273757245805699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976596903632365009661074265 732447677724273757245805699)
              ·
                refine ⟨1098671516586410635868708549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732447677724273757245805699 1098671516586410635868708549)
                ·
                  refine ⟨206000909359951994225382853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098671516586410635868708549 206000909359951994225382853)
                  ·
                    refine ⟨38625170504990998917259285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206000909359951994225382853 38625170504990998917259285)
                    ·
                      refine ⟨1810554867421453074246529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38625170504990998917259285 1810554867421453074246529)
                      ·
                        rfl

theorem cell23_3526043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_3526043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526043 prefixEnd_3526043 := by exact prefixLift 3526043
  have htrace : WordTrace (prefixWord ++ tailWord_3526043) baseStart_3526043 baseEnd_3526043 := by
    simpa [prefixWord, tailWord_3526043, baseEnd_3526043] using wordTrace_append hprefix tailTrace_3526043
  have hstable : (prefixWord ++ tailWord_3526043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526043).length < 2 ^ (prefixWord ++ tailWord_3526043).sum := by decide
  have hdescent : baseEnd_3526043 < baseStart_3526043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526077 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3526077 : Nat := 118140960795 + 3526077 * 2 ^ 59
def prefixEnd_3526077 : Nat := 4983230072969 + 3 ^ 40 * 3526077 * 2
def baseEnd_3526077 : Nat := 1810572325763705941221373

theorem tailTrace_3526077 : CollatzResearch.WordTrace tailWord_3526077 prefixEnd_3526077 1810572325763705941221373 := by
  unfold tailWord_3526077
  simp only [CollatzResearch.WordTrace]
  refine ⟨128606593646632709852640485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85737729097755139901760323 128606593646632709852640485)
  ·
    refine ⟨24113736308743633097370091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128606593646632709852640485 24113736308743633097370091)
    ·
      refine ⟨36170604463115449646055137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24113736308743633097370091 36170604463115449646055137)
      ·
        refine ⟨27127953347336587234541353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36170604463115449646055137 27127953347336587234541353)
        ·
          refine ⟨20345965010502440425906015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27127953347336587234541353 20345965010502440425906015)
          ·
            refine ⟨30518947515753660638859023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20345965010502440425906015 30518947515753660638859023)
            ·
              refine ⟨45778421273630490958288535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30518947515753660638859023 45778421273630490958288535)
              ·
                refine ⟨68667631910445736437432803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45778421273630490958288535 68667631910445736437432803)
                ·
                  refine ⟨103001447865668604656149205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68667631910445736437432803 103001447865668604656149205)
                  ·
                    refine ⟨2414096434351607921628497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103001447865668604656149205 2414096434351607921628497)
                    ·
                      refine ⟨1810572325763705941221373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414096434351607921628497 1810572325763705941221373)
                      ·
                        rfl

theorem cell23_3526077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3526077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526077 prefixEnd_3526077 := by exact prefixLift 3526077
  have htrace : WordTrace (prefixWord ++ tailWord_3526077) baseStart_3526077 baseEnd_3526077 := by
    simpa [prefixWord, tailWord_3526077, baseEnd_3526077] using wordTrace_append hprefix tailTrace_3526077
  have hstable : (prefixWord ++ tailWord_3526077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526077).length < 2 ^ (prefixWord ++ tailWord_3526077).sum := by decide
  have hdescent : baseEnd_3526077 < baseStart_3526077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526080 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_3526080 : Nat := 118140960795 + 3526080 * 2 ^ 59
def prefixEnd_3526080 : Nat := 4983230072969 + 3 ^ 40 * 3526080 * 2
def baseEnd_3526080 : Nat := 1810573866205669429483859

theorem tailTrace_3526080 : CollatzResearch.WordTrace tailWord_3526080 prefixEnd_3526080 1810573866205669429483859 := by
  unfold tailWord_3526080
  simp only [CollatzResearch.WordTrace]
  refine ⟨64303351532810920682499847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85737802043747894243333129 64303351532810920682499847)
  ·
    refine ⟨96455027299216381023749771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64303351532810920682499847 96455027299216381023749771)
    ·
      refine ⟨144682540948824571535624657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96455027299216381023749771 144682540948824571535624657)
      ·
        refine ⟨108511905711618428651718493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144682540948824571535624657 108511905711618428651718493)
        ·
          refine ⟨40691964641856910744394435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108511905711618428651718493 40691964641856910744394435)
          ·
            refine ⟨61037946962785366116591653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40691964641856910744394435 61037946962785366116591653)
            ·
              refine ⟨11444615055522256146860935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61037946962785366116591653 11444615055522256146860935)
              ·
                refine ⟨17166922583283384220291403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11444615055522256146860935 17166922583283384220291403)
                ·
                  refine ⟨25750383874925076330437105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17166922583283384220291403 25750383874925076330437105)
                  ·
                    refine ⟨19312787906193807247827829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25750383874925076330437105 19312787906193807247827829)
                    ·
                      refine ⟨1810573866205669429483859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19312787906193807247827829 1810573866205669429483859)
                      ·
                        rfl

theorem cell23_3526080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_3526080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526080 prefixEnd_3526080 := by exact prefixLift 3526080
  have htrace : WordTrace (prefixWord ++ tailWord_3526080) baseStart_3526080 baseEnd_3526080 := by
    simpa [prefixWord, tailWord_3526080, baseEnd_3526080] using wordTrace_append hprefix tailTrace_3526080
  have hstable : (prefixWord ++ tailWord_3526080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526080).length < 2 ^ (prefixWord ++ tailWord_3526080).sum := by decide
  have hdescent : baseEnd_3526080 < baseStart_3526080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526084 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3526084 : Nat := 118140960795 + 3526084 * 2 ^ 59
def prefixEnd_3526084 : Nat := 4983230072969 + 3 ^ 40 * 3526084 * 2
def baseEnd_3526084 : Nat := 1810575920128287413833841

theorem tailTrace_3526084 : CollatzResearch.WordTrace tailWord_3526084 prefixEnd_3526084 1810575920128287413833841 := by
  unfold tailWord_3526084
  simp only [CollatzResearch.WordTrace]
  refine ⟨64303424478803675024072653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85737899305071566698763537 64303424478803675024072653)
  ·
    refine ⟨24113784179551378134027245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64303424478803675024072653 24113784179551378134027245)
    ·
      refine ⟨9042669067331766800260217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24113784179551378134027245 9042669067331766800260217)
      ·
        refine ⟨6782001800498825100195163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042669067331766800260217 6782001800498825100195163)
        ·
          refine ⟨10173002700748237650292745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782001800498825100195163 10173002700748237650292745)
          ·
            refine ⟨7629752025561178237719559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173002700748237650292745 7629752025561178237719559)
            ·
              refine ⟨11444628038341767356579339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629752025561178237719559 11444628038341767356579339)
              ·
                refine ⟨17166942057512651034869009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11444628038341767356579339 17166942057512651034869009)
                ·
                  refine ⟨12875206543134488276151757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17166942057512651034869009 12875206543134488276151757)
                  ·
                    refine ⟨4828202453675433103556909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12875206543134488276151757 4828202453675433103556909)
                    ·
                      refine ⟨1810575920128287413833841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828202453675433103556909 1810575920128287413833841)
                      ·
                        rfl

theorem cell23_3526084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3526084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526084 prefixEnd_3526084 := by exact prefixLift 3526084
  have htrace : WordTrace (prefixWord ++ tailWord_3526084) baseStart_3526084 baseEnd_3526084 := by
    simpa [prefixWord, tailWord_3526084, baseEnd_3526084] using wordTrace_append hprefix tailTrace_3526084
  have hstable : (prefixWord ++ tailWord_3526084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526084).length < 2 ^ (prefixWord ++ tailWord_3526084).sum := by decide
  have hdescent : baseEnd_3526084 < baseStart_3526084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526120 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3526120 : Nat := 118140960795 + 3526120 * 2 ^ 59
def prefixEnd_3526120 : Nat := 4983230072969 + 3 ^ 40 * 3526120 * 2
def baseEnd_3526120 : Nat := 1810594405431849272983675

theorem tailTrace_3526120 : CollatzResearch.WordTrace tailWord_3526120 prefixEnd_3526120 1810594405431849272983675 := by
  unfold tailWord_3526120
  simp only [CollatzResearch.WordTrace]
  refine ⟨64304080992738464098227907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85738774656984618797637209 64304080992738464098227907)
  ·
    refine ⟨96456121489107696147341861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64304080992738464098227907 96456121489107696147341861)
    ·
      refine ⟨18085522779207693027626599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96456121489107696147341861 18085522779207693027626599)
      ·
        refine ⟨27128284168811539541439899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085522779207693027626599 27128284168811539541439899)
        ·
          refine ⟨40692426253217309312159849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27128284168811539541439899 40692426253217309312159849)
          ·
            refine ⟨30519319689912981984119887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40692426253217309312159849 30519319689912981984119887)
            ·
              refine ⟨45778979534869472976179831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30519319689912981984119887 45778979534869472976179831)
              ·
                refine ⟨68668469302304209464269747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45778979534869472976179831 68668469302304209464269747)
                ·
                  refine ⟨103002703953456314196404621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68668469302304209464269747 103002703953456314196404621)
                  ·
                    refine ⟨38626013982546117823651733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103002703953456314196404621 38626013982546117823651733)
                    ·
                      refine ⟨1810594405431849272983675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38626013982546117823651733 1810594405431849272983675)
                      ·
                        rfl

theorem cell23_3526120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3526120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526120 prefixEnd_3526120 := by exact prefixLift 3526120
  have htrace : WordTrace (prefixWord ++ tailWord_3526120) baseStart_3526120 baseEnd_3526120 := by
    simpa [prefixWord, tailWord_3526120, baseEnd_3526120] using wordTrace_append hprefix tailTrace_3526120
  have hstable : (prefixWord ++ tailWord_3526120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526120).length < 2 ^ (prefixWord ++ tailWord_3526120).sum := by decide
  have hdescent : baseEnd_3526120 < baseStart_3526120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526127 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_3526127 : Nat := 118140960795 + 3526127 * 2 ^ 59
def prefixEnd_3526127 : Nat := 4983230072969 + 3 ^ 40 * 3526127 * 2
def baseEnd_3526127 : Nat := 1810597999796430745596143

theorem tailTrace_3526127 : CollatzResearch.WordTrace tailWord_3526127 prefixEnd_3526127 1810597999796430745596143 := by
  unfold tailWord_3526127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128608417296451568391960635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85738944864301045594640423 128608417296451568391960635)
  ·
    refine ⟨192912625944677352587940953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128608417296451568391960635 192912625944677352587940953)
    ·
      refine ⟨144684469458508014440955715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192912625944677352587940953 144684469458508014440955715)
      ·
        refine ⟨217026704187762021661433573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144684469458508014440955715 217026704187762021661433573)
        ·
          refine ⟨40692507035205379061518795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217026704187762021661433573 40692507035205379061518795)
          ·
            refine ⟨61038760552808068592278193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40692507035205379061518795 61038760552808068592278193)
            ·
              refine ⟨45779070414606051444208645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61038760552808068592278193 45779070414606051444208645)
              ·
                refine ⟨8583575702738634645789121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45779070414606051444208645 8583575702738634645789121)
                ·
                  refine ⟨6437681777053975984341841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8583575702738634645789121 6437681777053975984341841)
                  ·
                    refine ⟨4828261332790481988256381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6437681777053975984341841 4828261332790481988256381)
                    ·
                      refine ⟨1810597999796430745596143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828261332790481988256381 1810597999796430745596143)
                      ·
                        rfl

theorem cell23_3526127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_3526127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526127 prefixEnd_3526127 := by exact prefixLift 3526127
  have htrace : WordTrace (prefixWord ++ tailWord_3526127) baseStart_3526127 baseEnd_3526127 := by
    simpa [prefixWord, tailWord_3526127, baseEnd_3526127] using wordTrace_append hprefix tailTrace_3526127
  have hstable : (prefixWord ++ tailWord_3526127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526127).length < 2 ^ (prefixWord ++ tailWord_3526127).sum := by decide
  have hdescent : baseEnd_3526127 < baseStart_3526127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526134 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3526134 : Nat := 118140960795 + 3526134 * 2 ^ 59
def prefixEnd_3526134 : Nat := 4983230072969 + 3 ^ 40 * 3526134 * 2
def baseEnd_3526134 : Nat := 603533864720337406069537

theorem tailTrace_3526134 : CollatzResearch.WordTrace tailWord_3526134 prefixEnd_3526134 603533864720337406069537 := by
  unfold tailWord_3526134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038042037964138036716591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85739115071617472391643637 8038042037964138036716591)
  ·
    refine ⟨12057063056946207055074887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038042037964138036716591 12057063056946207055074887)
    ·
      refine ⟨18085594585419310582612331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12057063056946207055074887 18085594585419310582612331)
      ·
        refine ⟨27128391878128965873918497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085594585419310582612331 27128391878128965873918497)
        ·
          refine ⟨20346293908596724405438873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27128391878128965873918497 20346293908596724405438873)
          ·
            refine ⟨15259720431447543304079155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20346293908596724405438873 15259720431447543304079155)
            ·
              refine ⟨22889580647171314956118733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259720431447543304079155 22889580647171314956118733)
              ·
                refine ⟨8583592742689243108544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22889580647171314956118733 8583592742689243108544525)
                ·
                  refine ⟨3218847278508466165704197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8583592742689243108544525 3218847278508466165704197)
                  ·
                    refine ⟨603533864720337406069537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218847278508466165704197 603533864720337406069537)
                    ·
                      rfl

theorem cell23_3526134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3526134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526134 prefixEnd_3526134 := by exact prefixLift 3526134
  have htrace : WordTrace (prefixWord ++ tailWord_3526134) baseStart_3526134 baseEnd_3526134 := by
    simpa [prefixWord, tailWord_3526134, baseEnd_3526134] using wordTrace_append hprefix tailTrace_3526134
  have hstable : (prefixWord ++ tailWord_3526134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526134).length < 2 ^ (prefixWord ++ tailWord_3526134).sum := by decide
  have hdescent : baseEnd_3526134 < baseStart_3526134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526168 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 1, 4]
def baseStart_3526168 : Nat := 118140960795 + 3526168 * 2 ^ 59
def prefixEnd_3526168 : Nat := 4983230072969 + 3 ^ 40 * 3526168 * 2
def baseEnd_3526168 : Nat := 603539684167755028394485

theorem tailTrace_3526168 : CollatzResearch.WordTrace tailWord_3526168 prefixEnd_3526168 603539684167755028394485 := by
  unfold tailWord_3526168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64304956344651516197101579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85739941792868688262802105 64304956344651516197101579)
  ·
    refine ⟨96457434516977274295652369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64304956344651516197101579 96457434516977274295652369)
    ·
      refine ⟨72343075887732955721739277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96457434516977274295652369 72343075887732955721739277)
      ·
        refine ⟨27128653457899858395652229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72343075887732955721739277 27128653457899858395652229)
        ·
          refine ⟨5086622523356223449184793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27128653457899858395652229 5086622523356223449184793)
          ·
            refine ⟨3814966892517167586888595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086622523356223449184793 3814966892517167586888595)
            ·
              refine ⟨5722450338775751380332893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814966892517167586888595 5722450338775751380332893)
              ·
                refine ⟨2145918877040906767624835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5722450338775751380332893 2145918877040906767624835)
                ·
                  refine ⟨3218878315561360151437253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145918877040906767624835 3218878315561360151437253)
                  ·
                    refine ⟨603539684167755028394485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218878315561360151437253 603539684167755028394485)
                    ·
                      rfl

theorem cell23_3526168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_3526168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526168 prefixEnd_3526168 := by exact prefixLift 3526168
  have htrace : WordTrace (prefixWord ++ tailWord_3526168) baseStart_3526168 baseEnd_3526168 := by
    simpa [prefixWord, tailWord_3526168, baseEnd_3526168] using wordTrace_append hprefix tailTrace_3526168
  have hstable : (prefixWord ++ tailWord_3526168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526168).length < 2 ^ (prefixWord ++ tailWord_3526168).sum := by decide
  have hdescent : baseEnd_3526168 < baseStart_3526168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526198 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3526198 : Nat := 118140960795 + 3526198 * 2 ^ 59
def prefixEnd_3526198 : Nat := 4983230072969 + 3 ^ 40 * 3526198 * 2
def baseEnd_3526198 : Nat := 201181606324766663089813

theorem tailTrace_3526198 : CollatzResearch.WordTrace tailWord_3526198 prefixEnd_3526198 201181606324766663089813 := by
  unfold tailWord_3526198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038187929949646719862203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85740671252796231678530165 8038187929949646719862203)
  ·
    refine ⟨12057281894924470079793305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038187929949646719862203 12057281894924470079793305)
    ·
      refine ⟨9042961421193352559844979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12057281894924470079793305 9042961421193352559844979)
      ·
        refine ⟨13564442131790028839767469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042961421193352559844979 13564442131790028839767469)
        ·
          refine ⟨5086665799421260814912801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13564442131790028839767469 5086665799421260814912801)
          ·
            refine ⟨3814999349565945611184601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086665799421260814912801 3814999349565945611184601)
            ·
              refine ⟨2861249512174459208388451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814999349565945611184601 2861249512174459208388451)
              ·
                refine ⟨4291874268261688812582677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861249512174459208388451 4291874268261688812582677)
                ·
                  refine ⟨201181606324766663089813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4291874268261688812582677 201181606324766663089813)
                  ·
                    rfl

theorem cell23_3526198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3526198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526198 prefixEnd_3526198 := by exact prefixLift 3526198
  have htrace : WordTrace (prefixWord ++ tailWord_3526198) baseStart_3526198 baseEnd_3526198 := by
    simpa [prefixWord, tailWord_3526198, baseEnd_3526198] using wordTrace_append hprefix tailTrace_3526198
  have hstable : (prefixWord ++ tailWord_3526198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526198).length < 2 ^ (prefixWord ++ tailWord_3526198).sum := by decide
  have hdescent : baseEnd_3526198 < baseStart_3526198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526231 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_3526231 : Nat := 118140960795 + 3526231 * 2 ^ 59
def prefixEnd_3526231 : Nat := 4983230072969 + 3 ^ 40 * 3526231 * 2
def baseEnd_3526231 : Nat := 1810651401784498338695665

theorem tailTrace_3526231 : CollatzResearch.WordTrace tailWord_3526231 prefixEnd_3526231 1810651401784498338695665 := by
  unfold tailWord_3526231
  simp only [CollatzResearch.WordTrace]
  refine ⟨128612210488074794153746547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85741473658716529435831031 128612210488074794153746547)
  ·
    refine ⟨192918315732112191230619821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128612210488074794153746547 192918315732112191230619821)
    ·
      refine ⟨72344368399542071711482433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192918315732112191230619821 72344368399542071711482433)
      ·
        refine ⟨54258276299656553783611825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72344368399542071711482433 54258276299656553783611825)
        ·
          refine ⟨40693707224742415337708869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54258276299656553783611825 40693707224742415337708869)
          ·
            refine ⟨7630070104639202875820413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40693707224742415337708869 7630070104639202875820413)
            ·
              refine ⟨2861276289239701078432655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7630070104639202875820413 2861276289239701078432655)
              ·
                refine ⟨4291914433859551617648983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861276289239701078432655 4291914433859551617648983)
                ·
                  refine ⟨6437871650789327426473475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291914433859551617648983 6437871650789327426473475)
                  ·
                    refine ⟨9656807476183991139710213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6437871650789327426473475 9656807476183991139710213)
                    ·
                      refine ⟨1810651401784498338695665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9656807476183991139710213 1810651401784498338695665)
                      ·
                        rfl

theorem cell23_3526231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_3526231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526231 prefixEnd_3526231 := by exact prefixLift 3526231
  have htrace : WordTrace (prefixWord ++ tailWord_3526231) baseStart_3526231 baseEnd_3526231 := by
    simpa [prefixWord, tailWord_3526231, baseEnd_3526231] using wordTrace_append hprefix tailTrace_3526231
  have hstable : (prefixWord ++ tailWord_3526231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526231).length < 2 ^ (prefixWord ++ tailWord_3526231).sum := by decide
  have hdescent : baseEnd_3526231 < baseStart_3526231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526234 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_3526234 : Nat := 118140960795 + 3526234 * 2 ^ 59
def prefixEnd_3526234 : Nat := 4983230072969 + 3 ^ 40 * 3526234 * 2
def baseEnd_3526234 : Nat := 1810652942226461826958151

theorem tailTrace_3526234 : CollatzResearch.WordTrace tailWord_3526234 prefixEnd_3526234 1810652942226461826958151 := by
  unfold tailWord_3526234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32153079976765981416526439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85741546604709283777403837 32153079976765981416526439)
  ·
    refine ⟨48229619965148972124789659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32153079976765981416526439 48229619965148972124789659)
    ·
      refine ⟨72344429947723458187184489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48229619965148972124789659 72344429947723458187184489)
      ·
        refine ⟨54258322460792593640388367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72344429947723458187184489 54258322460792593640388367)
        ·
          refine ⟨81387483691188890460582551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54258322460792593640388367 81387483691188890460582551)
          ·
            refine ⟨122081225536783335690873827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81387483691188890460582551 122081225536783335690873827)
            ·
              refine ⟨183121838305175003536310741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122081225536783335690873827 183121838305175003536310741)
              ·
                refine ⟨4291918085277539145382283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183121838305175003536310741 4291918085277539145382283)
                ·
                  refine ⟨6437877127916308718073425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291918085277539145382283 6437877127916308718073425)
                  ·
                    refine ⟨4828407845937231538555069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6437877127916308718073425 4828407845937231538555069)
                    ·
                      refine ⟨1810652942226461826958151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828407845937231538555069 1810652942226461826958151)
                      ·
                        rfl

theorem cell23_3526234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_3526234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526234 prefixEnd_3526234 := by exact prefixLift 3526234
  have htrace : WordTrace (prefixWord ++ tailWord_3526234) baseStart_3526234 baseEnd_3526234 := by
    simpa [prefixWord, tailWord_3526234, baseEnd_3526234] using wordTrace_append hprefix tailTrace_3526234
  have hstable : (prefixWord ++ tailWord_3526234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526234).length < 2 ^ (prefixWord ++ tailWord_3526234).sum := by decide
  have hdescent : baseEnd_3526234 < baseStart_3526234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526261 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3526261 : Nat := 118140960795 + 3526261 * 2 ^ 59
def prefixEnd_3526261 : Nat := 4983230072969 + 3 ^ 40 * 3526261 * 2
def baseEnd_3526261 : Nat := 1810666806204133221320527

theorem tailTrace_3526261 : CollatzResearch.WordTrace tailWord_3526261 prefixEnd_3526261 1810666806204133221320527 := by
  unfold tailWord_3526261
  simp only [CollatzResearch.WordTrace]
  refine ⟨128613304677966109277338637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85742203118644072851559091 128613304677966109277338637)
  ·
    refine ⟨48229989254237290979001989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128613304677966109277338637 48229989254237290979001989)
    ·
      refine ⟨9043122985169492058562873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48229989254237290979001989 9043122985169492058562873)
      ·
        refine ⟨6782342238877119043922155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9043122985169492058562873 6782342238877119043922155)
        ·
          refine ⟨10173513358315678565883233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782342238877119043922155 10173513358315678565883233)
          ·
            refine ⟨7630135018736758924412425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173513358315678565883233 7630135018736758924412425)
            ·
              refine ⟨5722601264052569193309319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7630135018736758924412425 5722601264052569193309319)
              ·
                refine ⟨8583901896078853789963979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722601264052569193309319 8583901896078853789963979)
                ·
                  refine ⟨12875852844118280684945969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8583901896078853789963979 12875852844118280684945969)
                  ·
                    refine ⟨9656889633088710513709477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12875852844118280684945969 9656889633088710513709477)
                    ·
                      refine ⟨1810666806204133221320527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9656889633088710513709477 1810666806204133221320527)
                      ·
                        rfl

theorem cell23_3526261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3526261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526261 prefixEnd_3526261 := by exact prefixLift 3526261
  have htrace : WordTrace (prefixWord ++ tailWord_3526261) baseStart_3526261 baseEnd_3526261 := by
    simpa [prefixWord, tailWord_3526261, baseEnd_3526261] using wordTrace_append hprefix tailTrace_3526261
  have hstable : (prefixWord ++ tailWord_3526261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526261).length < 2 ^ (prefixWord ++ tailWord_3526261).sum := by decide
  have hdescent : baseEnd_3526261 < baseStart_3526261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526277 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3526277 : Nat := 118140960795 + 3526277 * 2 ^ 59
def prefixEnd_3526277 : Nat := 4983230072969 + 3 ^ 40 * 3526277 * 2
def baseEnd_3526277 : Nat := 1810675021894605158720453

theorem tailTrace_3526277 : CollatzResearch.WordTrace tailWord_3526277 prefixEnd_3526277 1810675021894605158720453 := by
  unfold tailWord_3526277
  simp only [CollatzResearch.WordTrace]
  refine ⟨128613888245908144009921085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85742592163938762673280723 128613888245908144009921085)
  ·
    refine ⟨48230208092215554003720407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128613888245908144009921085 48230208092215554003720407)
    ·
      refine ⟨72345312138323331005580611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48230208092215554003720407 72345312138323331005580611)
      ·
        refine ⟨108517968207484996508370917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72345312138323331005580611 108517968207484996508370917)
        ·
          refine ⟨20347119038903436845319547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108517968207484996508370917 20347119038903436845319547)
          ·
            refine ⟨30520678558355155267979321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20347119038903436845319547 30520678558355155267979321)
            ·
              refine ⟨22890508918766366450984491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30520678558355155267979321 22890508918766366450984491)
              ·
                refine ⟨34335763378149549676476737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22890508918766366450984491 34335763378149549676476737)
                ·
                  refine ⟨25751822533612162257357553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34335763378149549676476737 25751822533612162257357553)
                  ·
                    refine ⟨19313866900209121693018165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25751822533612162257357553 19313866900209121693018165)
                    ·
                      refine ⟨1810675021894605158720453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19313866900209121693018165 1810675021894605158720453)
                      ·
                        rfl

theorem cell23_3526277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3526277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526277 prefixEnd_3526277 := by exact prefixLift 3526277
  have htrace : WordTrace (prefixWord ++ tailWord_3526277) baseStart_3526277 baseEnd_3526277 := by
    simpa [prefixWord, tailWord_3526277, baseEnd_3526277] using wordTrace_append hprefix tailTrace_3526277
  have hstable : (prefixWord ++ tailWord_3526277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526277).length < 2 ^ (prefixWord ++ tailWord_3526277).sum := by decide
  have hdescent : baseEnd_3526277 < baseStart_3526277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526312 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3526312 : Nat := 118140960795 + 3526312 * 2 ^ 59
def prefixEnd_3526312 : Nat := 4983230072969 + 3 ^ 40 * 3526312 * 2
def baseEnd_3526312 : Nat := 1810692993717512521782793

theorem tailTrace_3526312 : CollatzResearch.WordTrace tailWord_3526312 prefixEnd_3526312 1810692993717512521782793 := by
  unfold tailWord_3526312
  simp only [CollatzResearch.WordTrace]
  refine ⟨64307582400390672493722595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85743443200520896658296793 64307582400390672493722595)
  ·
    refine ⟨96461373600586008740583893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64307582400390672493722595 96461373600586008740583893)
    ·
      refine ⟨2260813443763734579857435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96461373600586008740583893 2260813443763734579857435)
      ·
        refine ⟨3391220165645601869786153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260813443763734579857435 3391220165645601869786153)
        ·
          refine ⟨2543415124234201402339615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391220165645601869786153 2543415124234201402339615)
          ·
            refine ⟨3815122686351302103509423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543415124234201402339615 3815122686351302103509423)
            ·
              refine ⟨5722684029526953155264135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815122686351302103509423 5722684029526953155264135)
              ·
                refine ⟨8584026044290429732896203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722684029526953155264135 8584026044290429732896203)
                ·
                  refine ⟨12876039066435644599344305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584026044290429732896203 12876039066435644599344305)
                  ·
                    refine ⟨9657029299826733449508229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12876039066435644599344305 9657029299826733449508229)
                    ·
                      refine ⟨1810692993717512521782793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9657029299826733449508229 1810692993717512521782793)
                      ·
                        rfl

theorem cell23_3526312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3526312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526312 prefixEnd_3526312 := by exact prefixLift 3526312
  have htrace : WordTrace (prefixWord ++ tailWord_3526312) baseStart_3526312 baseEnd_3526312 := by
    simpa [prefixWord, tailWord_3526312, baseEnd_3526312] using wordTrace_append hprefix tailTrace_3526312
  have hstable : (prefixWord ++ tailWord_3526312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526312).length < 2 ^ (prefixWord ++ tailWord_3526312).sum := by decide
  have hdescent : baseEnd_3526312 < baseStart_3526312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526325 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3526325 : Nat := 118140960795 + 3526325 * 2 ^ 59
def prefixEnd_3526325 : Nat := 4983230072969 + 3 ^ 40 * 3526325 * 2
def baseEnd_3526325 : Nat := 1810699668966020970920233

theorem tailTrace_3526325 : CollatzResearch.WordTrace tailWord_3526325 prefixEnd_3526325 1810699668966020970920233 := by
  unfold tailWord_3526325
  simp only [CollatzResearch.WordTrace]
  refine ⟨128615638949734248207668429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85743759299822832138445619 128615638949734248207668429)
  ·
    refine ⟨48230864606150343077875661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128615638949734248207668429 48230864606150343077875661)
    ·
      refine ⟨18086574227306378654203373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48230864606150343077875661 18086574227306378654203373)
      ·
        refine ⟨6782465335239891995326265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18086574227306378654203373 6782465335239891995326265)
        ·
          refine ⟨5086849001429918996494699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6782465335239891995326265 5086849001429918996494699)
          ·
            refine ⟨7630273502144878494742049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086849001429918996494699 7630273502144878494742049)
            ·
              refine ⟨5722705126608658871056537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7630273502144878494742049 5722705126608658871056537)
              ·
                refine ⟨4292028844956494153292403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722705126608658871056537 4292028844956494153292403)
                ·
                  refine ⟨6438043267434741229938605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292028844956494153292403 6438043267434741229938605)
                  ·
                    refine ⟨2414266225288027961226977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6438043267434741229938605 2414266225288027961226977)
                    ·
                      refine ⟨1810699668966020970920233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414266225288027961226977 1810699668966020970920233)
                      ·
                        rfl

theorem cell23_3526325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3526325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526325 prefixEnd_3526325 := by exact prefixLift 3526325
  have htrace : WordTrace (prefixWord ++ tailWord_3526325) baseStart_3526325 baseEnd_3526325 := by
    simpa [prefixWord, tailWord_3526325, baseEnd_3526325] using wordTrace_append hprefix tailTrace_3526325
  have hstable : (prefixWord ++ tailWord_3526325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526325).length < 2 ^ (prefixWord ++ tailWord_3526325).sum := by decide
  have hdescent : baseEnd_3526325 < baseStart_3526325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526342 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3526342 : Nat := 118140960795 + 3526342 * 2 ^ 59
def prefixEnd_3526342 : Nat := 4983230072969 + 3 ^ 40 * 3526342 * 2
def baseEnd_3526342 : Nat := 1810708398137147404407655

theorem tailTrace_3526342 : CollatzResearch.WordTrace tailWord_3526342 prefixEnd_3526342 1810708398137147404407655 := by
  unfold tailWord_3526342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019258093458520628469915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85744172660448440074024853 4019258093458520628469915)
  ·
    refine ⟨6028887140187780942704873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019258093458520628469915 6028887140187780942704873)
    ·
      refine ⟨4521665355140835707028655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028887140187780942704873 4521665355140835707028655)
      ·
        refine ⟨6782498032711253560542983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521665355140835707028655 6782498032711253560542983)
        ·
          refine ⟨10173747049066880340814475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782498032711253560542983 10173747049066880340814475)
          ·
            refine ⟨15260620573600320511221713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173747049066880340814475 15260620573600320511221713)
            ·
              refine ⟨11445465430200240383416285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15260620573600320511221713 11445465430200240383416285)
              ·
                refine ⟨4292049536325090143781107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11445465430200240383416285 4292049536325090143781107)
                ·
                  refine ⟨6438074304487635215671661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292049536325090143781107 6438074304487635215671661)
                  ·
                    refine ⟨2414277864182863205876873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6438074304487635215671661 2414277864182863205876873)
                    ·
                      refine ⟨1810708398137147404407655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414277864182863205876873 1810708398137147404407655)
                      ·
                        rfl

theorem cell23_3526342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3526342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526342 prefixEnd_3526342 := by exact prefixLift 3526342
  have htrace : WordTrace (prefixWord ++ tailWord_3526342) baseStart_3526342 baseEnd_3526342 := by
    simpa [prefixWord, tailWord_3526342, baseEnd_3526342] using wordTrace_append hprefix tailTrace_3526342
  have hstable : (prefixWord ++ tailWord_3526342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526342).length < 2 ^ (prefixWord ++ tailWord_3526342).sum := by decide
  have hdescent : baseEnd_3526342 < baseStart_3526342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526387 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 8]
def baseStart_3526387 : Nat := 118140960795 + 3526387 * 2 ^ 59
def prefixEnd_3526387 : Nat := 4983230072969 + 3 ^ 40 * 3526387 * 2
def baseEnd_3526387 : Nat := 603577168255533242781649

theorem tailTrace_3526387 : CollatzResearch.WordTrace tailWord_3526387 prefixEnd_3526387 603577168255533242781649 := by
  unfold tailWord_3526387
  simp only [CollatzResearch.WordTrace]
  refine ⟨128617900275509632796425415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85745266850339755197616943 128617900275509632796425415)
  ·
    refine ⟨192926850413264449194638123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128617900275509632796425415 192926850413264449194638123)
    ·
      refine ⟨289390275619896673791957185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192926850413264449194638123 289390275619896673791957185)
      ·
        refine ⟨217042706714922505343967889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289390275619896673791957185 217042706714922505343967889)
        ·
          refine ⟨162782030036191879007975917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217042706714922505343967889 162782030036191879007975917)
          ·
            refine ⟨61043261263571954627990969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162782030036191879007975917 61043261263571954627990969)
            ·
              refine ⟨45782445947678965970993227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61043261263571954627990969 45782445947678965970993227)
              ·
                refine ⟨68673668921518448956489841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45782445947678965970993227 68673668921518448956489841)
                ·
                  refine ⟨51505251691138836717367381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68673668921518448956489841 51505251691138836717367381)
                  ·
                    refine ⟨603577168255533242781649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51505251691138836717367381 603577168255533242781649)
                    ·
                      rfl

theorem cell23_3526387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_3526387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526387 prefixEnd_3526387 := by exact prefixLift 3526387
  have htrace : WordTrace (prefixWord ++ tailWord_3526387) baseStart_3526387 baseEnd_3526387 := by
    simpa [prefixWord, tailWord_3526387, baseEnd_3526387] using wordTrace_append hprefix tailTrace_3526387
  have hstable : (prefixWord ++ tailWord_3526387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526387).length < 2 ^ (prefixWord ++ tailWord_3526387).sum := by decide
  have hdescent : baseEnd_3526387 < baseStart_3526387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526498 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3526498 : Nat := 118140960795 + 3526498 * 2 ^ 59
def prefixEnd_3526498 : Nat := 4983230072969 + 3 ^ 40 * 3526498 * 2
def baseEnd_3526498 : Nat := 603596167039749598018979

theorem tailTrace_3526498 : CollatzResearch.WordTrace tailWord_3526498 prefixEnd_3526498 603596167039749598018979 := by
  unfold tailWord_3526498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32155487194526874688429037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85747965852071665835810765 32155487194526874688429037)
  ·
    refine ⟨12058307697947578008160889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32155487194526874688429037 12058307697947578008160889)
    ·
      refine ⟨9043730773460683506120667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12058307697947578008160889 9043730773460683506120667)
      ·
        refine ⟨13565596160191025259181001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043730773460683506120667 13565596160191025259181001)
        ·
          refine ⟨10174197120143268944385751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13565596160191025259181001 10174197120143268944385751)
          ·
            refine ⟨15261295680214903416578627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174197120143268944385751 15261295680214903416578627)
            ·
              refine ⟨22891943520322355124867941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261295680214903416578627 22891943520322355124867941)
              ·
                refine ⟨4292239410060441585912739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22891943520322355124867941 4292239410060441585912739)
                ·
                  refine ⟨6438359115090662378869109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292239410060441585912739 6438359115090662378869109)
                  ·
                    refine ⟨603596167039749598018979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6438359115090662378869109 603596167039749598018979)
                    ·
                      rfl

theorem cell23_3526498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3526498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526498 prefixEnd_3526498 := by exact prefixLift 3526498
  have htrace : WordTrace (prefixWord ++ tailWord_3526498) baseStart_3526498 baseEnd_3526498 := by
    simpa [prefixWord, tailWord_3526498, baseEnd_3526498] using wordTrace_append hprefix tailTrace_3526498
  have hstable : (prefixWord ++ tailWord_3526498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526498).length < 2 ^ (prefixWord ++ tailWord_3526498).sum := by decide
  have hdescent : baseEnd_3526498 < baseStart_3526498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526501 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_3526501 : Nat := 118140960795 + 3526501 * 2 ^ 59
def prefixEnd_3526501 : Nat := 4983230072969 + 3 ^ 40 * 3526501 * 2
def baseEnd_3526501 : Nat := 1810790041561212282319423

theorem tailTrace_3526501 : CollatzResearch.WordTrace tailWord_3526501 prefixEnd_3526501 1810790041561212282319423 := by
  unfold tailWord_3526501
  simp only [CollatzResearch.WordTrace]
  refine ⟨128622058197096630266075357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85748038798064420177383571 128622058197096630266075357)
  ·
    refine ⟨48233271823911236349778259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128622058197096630266075357 48233271823911236349778259)
    ·
      refine ⟨72349907735866854524667389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48233271823911236349778259 72349907735866854524667389)
      ·
        refine ⟨27131215400950070446750271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72349907735866854524667389 27131215400950070446750271)
        ·
          refine ⟨40696823101425105670125407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27131215400950070446750271 40696823101425105670125407)
          ·
            refine ⟨61045234652137658505188111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40696823101425105670125407 61045234652137658505188111)
            ·
              refine ⟨91567851978206487757782167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61045234652137658505188111 91567851978206487757782167)
              ·
                refine ⟨137351777967309731636673251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91567851978206487757782167 137351777967309731636673251)
                ·
                  refine ⟨206027666950964597455009877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137351777967309731636673251 206027666950964597455009877)
                  ·
                    refine ⟨2414386722081616376425897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 206027666950964597455009877 2414386722081616376425897)
                    ·
                      refine ⟨1810790041561212282319423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414386722081616376425897 1810790041561212282319423)
                      ·
                        rfl

theorem cell23_3526501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_3526501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526501 prefixEnd_3526501 := by exact prefixLift 3526501
  have htrace : WordTrace (prefixWord ++ tailWord_3526501) baseStart_3526501 baseEnd_3526501 := by
    simpa [prefixWord, tailWord_3526501, baseEnd_3526501] using wordTrace_append hprefix tailTrace_3526501
  have hstable : (prefixWord ++ tailWord_3526501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526501).length < 2 ^ (prefixWord ++ tailWord_3526501).sum := by decide
  have hdescent : baseEnd_3526501 < baseStart_3526501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526521 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3526521 : Nat := 118140960795 + 3526521 * 2 ^ 59
def prefixEnd_3526521 : Nat := 4983230072969 + 3 ^ 40 * 3526521 * 2
def baseEnd_3526521 : Nat := 1810800311174302204069331

theorem tailTrace_3526521 : CollatzResearch.WordTrace tailWord_3526521 prefixEnd_3526521 1810800311174302204069331 := by
  unfold tailWord_3526521
  simp only [CollatzResearch.WordTrace]
  refine ⟨128622787657024173681803417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85748525104682782454535611 128622787657024173681803417)
  ·
    refine ⟨96467090742768130261352563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128622787657024173681803417 96467090742768130261352563)
    ·
      refine ⟨144700636114152195392028845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96467090742768130261352563 144700636114152195392028845)
      ·
        refine ⟨54262738542807073272010817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144700636114152195392028845 54262738542807073272010817)
        ·
          refine ⟨40697053907105304954008113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54262738542807073272010817 40697053907105304954008113)
          ·
            refine ⟨30522790430328978715506085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40697053907105304954008113 30522790430328978715506085)
            ·
              refine ⟨5723023205686683509157391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30522790430328978715506085 5723023205686683509157391)
              ·
                refine ⟨8584534808530025263736087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723023205686683509157391 8584534808530025263736087)
                ·
                  refine ⟨12876802212795037895604131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584534808530025263736087 12876802212795037895604131)
                  ·
                    refine ⟨19315203319192556843406197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12876802212795037895604131 19315203319192556843406197)
                    ·
                      refine ⟨1810800311174302204069331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19315203319192556843406197 1810800311174302204069331)
                      ·
                        rfl

theorem cell23_3526521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3526521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526521 prefixEnd_3526521 := by exact prefixLift 3526521
  have htrace : WordTrace (prefixWord ++ tailWord_3526521) baseStart_3526521 baseEnd_3526521 := by
    simpa [prefixWord, tailWord_3526521, baseEnd_3526521] using wordTrace_append hprefix tailTrace_3526521
  have hstable : (prefixWord ++ tailWord_3526521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526521).length < 2 ^ (prefixWord ++ tailWord_3526521).sum := by decide
  have hdescent : baseEnd_3526521 < baseStart_3526521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526529 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3526529 : Nat := 118140960795 + 3526529 * 2 ^ 59
def prefixEnd_3526529 : Nat := 4983230072969 + 3 ^ 40 * 3526529 * 2
def baseEnd_3526529 : Nat := 1810804419019538172769295

theorem tailTrace_3526529 : CollatzResearch.WordTrace tailWord_3526529 prefixEnd_3526529 1810804419019538172769295 := by
  unfold tailWord_3526529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128623079440995191048094641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85748719627330127365396427 128623079440995191048094641)
  ·
    refine ⟨96467309580746393286070981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128623079440995191048094641 96467309580746393286070981)
    ·
      refine ⟨18087620546389948741138309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96467309580746393286070981 18087620546389948741138309)
      ·
        refine ⟨3391428852448115388963433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18087620546389948741138309 3391428852448115388963433)
        ·
          refine ⟨2543571639336086541722575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391428852448115388963433 2543571639336086541722575)
          ·
            refine ⟨3815357459004129812583863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543571639336086541722575 3815357459004129812583863)
            ·
              refine ⟨5723036188506194718875795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815357459004129812583863 5723036188506194718875795)
              ·
                refine ⟨8584554282759292078313693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723036188506194718875795 8584554282759292078313693)
                ·
                  refine ⟨3219207856034734529367635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8584554282759292078313693 3219207856034734529367635)
                  ·
                    refine ⟨4828811784052101794051453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219207856034734529367635 4828811784052101794051453)
                    ·
                      refine ⟨1810804419019538172769295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828811784052101794051453 1810804419019538172769295)
                      ·
                        rfl

theorem cell23_3526529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3526529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526529 prefixEnd_3526529 := by exact prefixLift 3526529
  have htrace : WordTrace (prefixWord ++ tailWord_3526529) baseStart_3526529 baseEnd_3526529 := by
    simpa [prefixWord, tailWord_3526529, baseEnd_3526529] using wordTrace_append hprefix tailTrace_3526529
  have hstable : (prefixWord ++ tailWord_3526529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526529).length < 2 ^ (prefixWord ++ tailWord_3526529).sum := by decide
  have hdescent : baseEnd_3526529 < baseStart_3526529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526552 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3526552 : Nat := 118140960795 + 3526552 * 2 ^ 59
def prefixEnd_3526552 : Nat := 4983230072969 + 3 ^ 40 * 3526552 * 2
def baseEnd_3526552 : Nat := 1810816229074591582781689

theorem tailTrace_3526552 : CollatzResearch.WordTrace tailWord_3526552 prefixEnd_3526552 1810816229074591582781689 := by
  unfold tailWord_3526552
  simp only [CollatzResearch.WordTrace]
  refine ⟨64311959159955932988090955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85749278879941243984121273 64311959159955932988090955)
  ·
    refine ⟨96467938739933899482136433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64311959159955932988090955 96467938739933899482136433)
    ·
      refine ⟨72350954054950424611602325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96467938739933899482136433 72350954054950424611602325)
      ·
        refine ⟨3391450971325801153668859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72350954054950424611602325 3391450971325801153668859)
        ·
          refine ⟨5087176456988701730503289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391450971325801153668859 5087176456988701730503289)
          ·
            refine ⟨3815382342741526297877467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5087176456988701730503289 3815382342741526297877467)
            ·
              refine ⟨5723073514112289446816201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815382342741526297877467 5723073514112289446816201)
              ·
                refine ⟨4292305135584217085112151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723073514112289446816201 4292305135584217085112151)
                ·
                  refine ⟨6438457703376325627668227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292305135584217085112151 6438457703376325627668227)
                  ·
                    refine ⟨9657686555064488441502341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438457703376325627668227 9657686555064488441502341)
                    ·
                      refine ⟨1810816229074591582781689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9657686555064488441502341 1810816229074591582781689)
                      ·
                        rfl

theorem cell23_3526552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3526552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526552 prefixEnd_3526552 := by exact prefixLift 3526552
  have htrace : WordTrace (prefixWord ++ tailWord_3526552) baseStart_3526552 baseEnd_3526552 := by
    simpa [prefixWord, tailWord_3526552, baseEnd_3526552] using wordTrace_append hprefix tailTrace_3526552
  have hstable : (prefixWord ++ tailWord_3526552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526552).length < 2 ^ (prefixWord ++ tailWord_3526552).sum := by decide
  have hdescent : baseEnd_3526552 < baseStart_3526552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526585 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3526585 : Nat := 118140960795 + 3526585 * 2 ^ 59
def prefixEnd_3526585 : Nat := 4983230072969 + 3 ^ 40 * 3526585 * 2
def baseEnd_3526585 : Nat := 1810833173936189953669037

theorem tailTrace_3526585 : CollatzResearch.WordTrace tailWord_3526585 prefixEnd_3526585 1810833173936189953669037 := by
  unfold tailWord_3526585
  simp only [CollatzResearch.WordTrace]
  refine ⟨128625121928792312612133209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85750081285861541741422139 128625121928792312612133209)
  ·
    refine ⟨96468841446594234459099907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128625121928792312612133209 96468841446594234459099907)
    ·
      refine ⟨144703262169891351688649861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96468841446594234459099907 144703262169891351688649861)
      ·
        refine ⟨27131861656854628441621849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144703262169891351688649861 27131861656854628441621849)
        ·
          refine ⟨20348896242640971331216387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27131861656854628441621849 20348896242640971331216387)
          ·
            refine ⟨30523344363961456996824581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20348896242640971331216387 30523344363961456996824581)
            ·
              refine ⟨5723127068242773186904609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30523344363961456996824581 5723127068242773186904609)
              ·
                refine ⟨4292345301182079890178457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723127068242773186904609 4292345301182079890178457)
                ·
                  refine ⟨3219258975886559917633843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292345301182079890178457 3219258975886559917633843)
                  ·
                    refine ⟨4828888463829839876450765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219258975886559917633843 4828888463829839876450765)
                    ·
                      refine ⟨1810833173936189953669037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4828888463829839876450765 1810833173936189953669037)
                      ·
                        rfl

theorem cell23_3526585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3526585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526585 prefixEnd_3526585 := by exact prefixLift 3526585
  have htrace : WordTrace (prefixWord ++ tailWord_3526585) baseStart_3526585 baseEnd_3526585 := by
    simpa [prefixWord, tailWord_3526585, baseEnd_3526585] using wordTrace_append hprefix tailTrace_3526585
  have hstable : (prefixWord ++ tailWord_3526585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526585).length < 2 ^ (prefixWord ++ tailWord_3526585).sum := by decide
  have hdescent : baseEnd_3526585 < baseStart_3526585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526608 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2]
def baseStart_3526608 : Nat := 118140960795 + 3526608 * 2 ^ 59
def prefixEnd_3526608 : Nat := 4983230072969 + 3 ^ 40 * 3526608 * 2
def baseEnd_3526608 : Nat := 1810844983991243363681431

theorem tailTrace_3526608 : CollatzResearch.WordTrace tailWord_3526608 prefixEnd_3526608 1810844983991243363681431 := by
  unfold tailWord_3526608
  simp only [CollatzResearch.WordTrace]
  refine ⟨64312980403854493770110239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85750640538472658360146985 64312980403854493770110239)
  ·
    refine ⟨96469470605781740655165359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64312980403854493770110239 96469470605781740655165359)
    ·
      refine ⟨144704205908672610982748039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96469470605781740655165359 144704205908672610982748039)
      ·
        refine ⟨217056308863008916474122059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144704205908672610982748039 217056308863008916474122059)
        ·
          refine ⟨325584463294513374711183089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217056308863008916474122059 325584463294513374711183089)
          ·
            refine ⟨244188347470885031033387317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325584463294513374711183089 244188347470885031033387317)
            ·
              refine ⟨22892657575395471659380061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244188347470885031033387317 22892657575395471659380061)
              ·
                refine ⟨8584746590773301872267523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22892657575395471659380061 8584746590773301872267523)
                ·
                  refine ⟨12877119886159952808401285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584746590773301872267523 12877119886159952808401285)
                  ·
                    refine ⟨2414459978654991151575241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12877119886159952808401285 2414459978654991151575241)
                    ·
                      refine ⟨1810844983991243363681431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414459978654991151575241 1810844983991243363681431)
                      ·
                        rfl

theorem cell23_3526608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2].length) (baseStart_3526608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526608 prefixEnd_3526608 := by exact prefixLift 3526608
  have htrace : WordTrace (prefixWord ++ tailWord_3526608) baseStart_3526608 baseEnd_3526608 := by
    simpa [prefixWord, tailWord_3526608, baseEnd_3526608] using wordTrace_append hprefix tailTrace_3526608
  have hstable : (prefixWord ++ tailWord_3526608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526608).length < 2 ^ (prefixWord ++ tailWord_3526608).sum := by decide
  have hdescent : baseEnd_3526608 < baseStart_3526608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526638 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3526638 : Nat := 118140960795 + 3526638 * 2 ^ 59
def prefixEnd_3526638 : Nat := 4983230072969 + 3 ^ 40 * 3526638 * 2
def baseEnd_3526638 : Nat := 1810860388410878246306293

theorem tailTrace_3526638 : CollatzResearch.WordTrace tailWord_3526638 prefixEnd_3526638 1810860388410878246306293 := by
  unfold tailWord_3526638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078381874700037832976571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85751369998400201775875045 16078381874700037832976571)
  ·
    refine ⟨24117572812050056749464857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078381874700037832976571 24117572812050056749464857)
    ·
      refine ⟨18088179609037542562098643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24117572812050056749464857 18088179609037542562098643)
      ·
        refine ⟨27132269413556313843147965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18088179609037542562098643 27132269413556313843147965)
        ·
          refine ⟨10174601030083617691180487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27132269413556313843147965 10174601030083617691180487)
          ·
            refine ⟨15261901545125426536770731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174601030083617691180487 15261901545125426536770731)
            ·
              refine ⟨22892852317688139805156097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261901545125426536770731 22892852317688139805156097)
              ·
                refine ⟨17169639238266104853867073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22892852317688139805156097 17169639238266104853867073)
                ·
                  refine ⟨12877229428699578640400305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17169639238266104853867073 12877229428699578640400305)
                  ·
                    refine ⟨9657922071524683980300229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12877229428699578640400305 9657922071524683980300229)
                    ·
                      refine ⟨1810860388410878246306293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9657922071524683980300229 1810860388410878246306293)
                      ·
                        rfl

theorem cell23_3526638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3526638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526638 prefixEnd_3526638 := by exact prefixLift 3526638
  have htrace : WordTrace (prefixWord ++ tailWord_3526638) baseStart_3526638 baseEnd_3526638 := by
    simpa [prefixWord, tailWord_3526638, baseEnd_3526638] using wordTrace_append hprefix tailTrace_3526638
  have hstable : (prefixWord ++ tailWord_3526638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526638).length < 2 ^ (prefixWord ++ tailWord_3526638).sum := by decide
  have hdescent : baseEnd_3526638 < baseStart_3526638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526648 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 5]
def baseStart_3526648 : Nat := 118140960795 + 3526648 * 2 ^ 59
def prefixEnd_3526648 : Nat := 4983230072969 + 3 ^ 40 * 3526648 * 2
def baseEnd_3526648 : Nat := 201207280357491467464583

theorem tailTrace_3526648 : CollatzResearch.WordTrace tailWord_3526648 prefixEnd_3526648 201207280357491467464583 := by
  unfold tailWord_3526648
  simp only [CollatzResearch.WordTrace]
  refine ⟨64313709863782037185838299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85751613151709382914451065 64313709863782037185838299)
  ·
    refine ⟨96470564795673055778757449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64313709863782037185838299 96470564795673055778757449)
    ·
      refine ⟨72352923596754791834068087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96470564795673055778757449 72352923596754791834068087)
      ·
        refine ⟨108529385395132187751102131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72352923596754791834068087 108529385395132187751102131)
        ·
          refine ⟨162794078092698281626653197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108529385395132187751102131 162794078092698281626653197)
          ·
            refine ⟨61047779284761855609994949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162794078092698281626653197 61047779284761855609994949)
            ·
              refine ⟨11446458615892847926874053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61047779284761855609994949 11446458615892847926874053)
              ·
                refine ⟨2146210990479908986288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11446458615892847926874053 2146210990479908986288885)
                ·
                  refine ⟨201207280357491467464583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2146210990479908986288885 201207280357491467464583)
                  ·
                    rfl

theorem cell23_3526648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 5].length) (baseStart_3526648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526648 prefixEnd_3526648 := by exact prefixLift 3526648
  have htrace : WordTrace (prefixWord ++ tailWord_3526648) baseStart_3526648 baseEnd_3526648 := by
    simpa [prefixWord, tailWord_3526648, baseEnd_3526648] using wordTrace_append hprefix tailTrace_3526648
  have hstable : (prefixWord ++ tailWord_3526648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526648).length < 2 ^ (prefixWord ++ tailWord_3526648).sum := by decide
  have hdescent : baseEnd_3526648 < baseStart_3526648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526661 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_3526661 : Nat := 118140960795 + 3526661 * 2 ^ 59
def prefixEnd_3526661 : Nat := 4983230072969 + 3 ^ 40 * 3526661 * 2
def baseEnd_3526661 : Nat := 603624066155310552106229

theorem tailTrace_3526661 : CollatzResearch.WordTrace tailWord_3526661 prefixEnd_3526661 603624066155310552106229 := by
  unfold tailWord_3526661
  simp only [CollatzResearch.WordTrace]
  refine ⟨128627893876516977591899837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85751929251011318394599891 128627893876516977591899837)
  ·
    refine ⟨48235460203693866596962439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128627893876516977591899837 48235460203693866596962439)
    ·
      refine ⟨72353190305540799895443659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48235460203693866596962439 72353190305540799895443659)
      ·
        refine ⟨108529785458311199843165489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72353190305540799895443659 108529785458311199843165489)
        ·
          refine ⟨81397339093733399882374117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108529785458311199843165489 81397339093733399882374117)
          ·
            refine ⟨15262001080075012477945147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81397339093733399882374117 15262001080075012477945147)
            ·
              refine ⟨22893001620112518716917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15262001080075012477945147 22893001620112518716917721)
              ·
                refine ⟨17169751215084389037688291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22893001620112518716917721 17169751215084389037688291)
                ·
                  refine ⟨25754626822626583556532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17169751215084389037688291 25754626822626583556532437)
                  ·
                    refine ⟨603624066155310552106229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25754626822626583556532437 603624066155310552106229)
                    ·
                      rfl

theorem cell23_3526661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_3526661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526661 prefixEnd_3526661 := by exact prefixLift 3526661
  have htrace : WordTrace (prefixWord ++ tailWord_3526661) baseStart_3526661 baseEnd_3526661 := by
    simpa [prefixWord, tailWord_3526661, baseEnd_3526661] using wordTrace_append hprefix tailTrace_3526661
  have hstable : (prefixWord ++ tailWord_3526661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526661).length < 2 ^ (prefixWord ++ tailWord_3526661).sum := by decide
  have hdescent : baseEnd_3526661 < baseStart_3526661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526711 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3526711 : Nat := 118140960795 + 3526711 * 2 ^ 59
def prefixEnd_3526711 : Nat := 4983230072969 + 3 ^ 40 * 3526711 * 2
def baseEnd_3526711 : Nat := 1810897872498656460693457

theorem tailTrace_3526711 : CollatzResearch.WordTrace tailWord_3526711 prefixEnd_3526711 1810897872498656460693457 := by
  unfold tailWord_3526711
  simp only [CollatzResearch.WordTrace]
  refine ⟨128629717526335836131219987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85753145017557224087479991 128629717526335836131219987)
  ·
    refine ⟨192944576289503754196829981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128629717526335836131219987 192944576289503754196829981)
    ·
      refine ⟨72354216108563907823811243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192944576289503754196829981 72354216108563907823811243)
      ·
        refine ⟨108531324162845861735716865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72354216108563907823811243 108531324162845861735716865)
        ·
          refine ⟨81398493122134396301787649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108531324162845861735716865 81398493122134396301787649)
          ·
            refine ⟨61048869841600797226340737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81398493122134396301787649 61048869841600797226340737)
            ·
              refine ⟨45786652381200597919755553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61048869841600797226340737 45786652381200597919755553)
              ·
                refine ⟨34339989285900448439816665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45786652381200597919755553 34339989285900448439816665)
                ·
                  refine ⟨25754991964425336329862499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34339989285900448439816665 25754991964425336329862499)
                  ·
                    refine ⟨38632487946638004494793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25754991964425336329862499 38632487946638004494793749)
                    ·
                      refine ⟨1810897872498656460693457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38632487946638004494793749 1810897872498656460693457)
                      ·
                        rfl

theorem cell23_3526711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3526711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526711 prefixEnd_3526711 := by exact prefixLift 3526711
  have htrace : WordTrace (prefixWord ++ tailWord_3526711) baseStart_3526711 baseEnd_3526711 := by
    simpa [prefixWord, tailWord_3526711, baseEnd_3526711] using wordTrace_append hprefix tailTrace_3526711
  have hstable : (prefixWord ++ tailWord_3526711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526711).length < 2 ^ (prefixWord ++ tailWord_3526711).sum := by decide
  have hdescent : baseEnd_3526711 < baseStart_3526711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526768 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_3526768 : Nat := 118140960795 + 3526768 * 2 ^ 59
def prefixEnd_3526768 : Nat := 4983230072969 + 3 ^ 40 * 3526768 * 2
def baseEnd_3526768 : Nat := 603642380298654245893565

theorem tailTrace_3526768 : CollatzResearch.WordTrace tailWord_3526768 prefixEnd_3526768 603642380298654245893565 := by
  unfold tailWord_3526768
  simp only [CollatzResearch.WordTrace]
  refine ⟨64315898243564667433022479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85754530991419556577363305 64315898243564667433022479)
  ·
    refine ⟨96473847365347001149533719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64315898243564667433022479 96473847365347001149533719)
    ·
      refine ⟨144710771048020501724300579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96473847365347001149533719 144710771048020501724300579)
      ·
        refine ⟨217066156572030752586450869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144710771048020501724300579 217066156572030752586450869)
        ·
          refine ⟨20349952178627883054979769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217066156572030752586450869 20349952178627883054979769)
          ·
            refine ⟨15262464133970912291234827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20349952178627883054979769 15262464133970912291234827)
            ·
              refine ⟨22893696200956368436852241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15262464133970912291234827 22893696200956368436852241)
              ·
                refine ⟨17170272150717276327639181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22893696200956368436852241 17170272150717276327639181)
                ·
                  refine ⟨6438852056518978622864693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17170272150717276327639181 6438852056518978622864693)
                  ·
                    refine ⟨603642380298654245893565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6438852056518978622864693 603642380298654245893565)
                    ·
                      rfl

theorem cell23_3526768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_3526768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526768 prefixEnd_3526768 := by exact prefixLift 3526768
  have htrace : WordTrace (prefixWord ++ tailWord_3526768) baseStart_3526768 baseEnd_3526768 := by
    simpa [prefixWord, tailWord_3526768, baseEnd_3526768] using wordTrace_append hprefix tailTrace_3526768
  have hstable : (prefixWord ++ tailWord_3526768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526768).length < 2 ^ (prefixWord ++ tailWord_3526768).sum := by decide
  have hdescent : baseEnd_3526768 < baseStart_3526768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526792 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3526792 : Nat := 118140960795 + 3526792 * 2 ^ 59
def prefixEnd_3526792 : Nat := 4983230072969 + 3 ^ 40 * 3526792 * 2
def baseEnd_3526792 : Nat := 1810939464431670643780585

theorem tailTrace_3526792 : CollatzResearch.WordTrace tailWord_3526792 prefixEnd_3526792 1810939464431670643780585 := by
  unfold tailWord_3526792
  simp only [CollatzResearch.WordTrace]
  refine ⟨64316335919521193482459315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85755114559361591309945753 64316335919521193482459315)
  ·
    refine ⟨96474503879281790223688973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64316335919521193482459315 96474503879281790223688973)
    ·
      refine ⟨36177938954730671333883365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96474503879281790223688973 36177938954730671333883365)
      ·
        refine ⟨6783363554012000875103131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36177938954730671333883365 6783363554012000875103131)
        ·
          refine ⟨10175045331018001312654697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783363554012000875103131 10175045331018001312654697)
          ·
            refine ⟨7631283998263500984491023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175045331018001312654697 7631283998263500984491023)
            ·
              refine ⟨11446925997395251476736535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631283998263500984491023 11446925997395251476736535)
              ·
                refine ⟨17170388996092877215104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446925997395251476736535 17170388996092877215104803)
                ·
                  refine ⟨25755583494139315822657205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17170388996092877215104803 25755583494139315822657205)
                  ·
                    refine ⟨2414585952575560858374113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25755583494139315822657205 2414585952575560858374113)
                    ·
                      refine ⟨1810939464431670643780585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414585952575560858374113 1810939464431670643780585)
                      ·
                        rfl

theorem cell23_3526792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3526792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526792 prefixEnd_3526792 := by exact prefixLift 3526792
  have htrace : WordTrace (prefixWord ++ tailWord_3526792) baseStart_3526792 baseEnd_3526792 := by
    simpa [prefixWord, tailWord_3526792, baseEnd_3526792] using wordTrace_append hprefix tailTrace_3526792
  have hstable : (prefixWord ++ tailWord_3526792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526792).length < 2 ^ (prefixWord ++ tailWord_3526792).sum := by decide
  have hdescent : baseEnd_3526792 < baseStart_3526792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526805 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_3526805 : Nat := 118140960795 + 3526805 * 2 ^ 59
def prefixEnd_3526805 : Nat := 4983230072969 + 3 ^ 40 * 3526805 * 2
def baseEnd_3526805 : Nat := 1810946139680179092918025

theorem tailTrace_3526805 : CollatzResearch.WordTrace tailWord_3526805 prefixEnd_3526805 1810946139680179092918025 := by
  unfold tailWord_3526805
  simp only [CollatzResearch.WordTrace]
  refine ⟨128633145987995290185141869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85755430658663526790094579 128633145987995290185141869)
  ·
    refine ⟨48237429745498233819428201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128633145987995290185141869 48237429745498233819428201)
    ·
      refine ⟨36178072309123675364571151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48237429745498233819428201 36178072309123675364571151)
      ·
        refine ⟨54267108463685513046856727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36178072309123675364571151 54267108463685513046856727)
        ·
          refine ⟨81400662695528269570285091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54267108463685513046856727 81400662695528269570285091)
          ·
            refine ⟨122100994043292404355427637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81400662695528269570285091 122100994043292404355427637)
            ·
              refine ⟨11446968191558662908321341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122100994043292404355427637 11446968191558662908321341)
              ·
                refine ⟨4292613071834498590620503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11446968191558662908321341 4292613071834498590620503)
                ·
                  refine ⟨6438919607751747885930755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292613071834498590620503 6438919607751747885930755)
                  ·
                    refine ⟨9658379411627621828896133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438919607751747885930755 9658379411627621828896133)
                    ·
                      refine ⟨1810946139680179092918025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9658379411627621828896133 1810946139680179092918025)
                      ·
                        rfl

theorem cell23_3526805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_3526805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526805 prefixEnd_3526805 := by exact prefixLift 3526805
  have htrace : WordTrace (prefixWord ++ tailWord_3526805) baseStart_3526805 baseEnd_3526805 := by
    simpa [prefixWord, tailWord_3526805, baseEnd_3526805] using wordTrace_append hprefix tailTrace_3526805
  have hstable : (prefixWord ++ tailWord_3526805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526805).length < 2 ^ (prefixWord ++ tailWord_3526805).sum := by decide
  have hdescent : baseEnd_3526805 < baseStart_3526805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526806 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3526806 : Nat := 118140960795 + 3526806 * 2 ^ 59
def prefixEnd_3526806 : Nat := 4983230072969 + 3 ^ 40 * 3526806 * 2
def baseEnd_3526806 : Nat := 201216294795648176556169

theorem tailTrace_3526806 : CollatzResearch.WordTrace tailWord_3526806 prefixEnd_3526806 201216294795648176556169 := by
  unfold tailWord_3526806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039573903811979209745517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85755454973994444903952181 8039573903811979209745517)
  ·
    refine ⟨3014840213929492203654569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8039573903811979209745517 3014840213929492203654569)
    ·
      refine ⟨2261130160447119152740927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3014840213929492203654569 2261130160447119152740927)
      ·
        refine ⟨3391695240670678729111391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261130160447119152740927 3391695240670678729111391)
        ·
          refine ⟨5087542861006018093667087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391695240670678729111391 5087542861006018093667087)
          ·
            refine ⟨7631314291509027140500631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087542861006018093667087 7631314291509027140500631)
            ·
              refine ⟨11446971437263540710750947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631314291509027140500631 11446971437263540710750947)
              ·
                refine ⟨17170457155895311066126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446971437263540710750947 17170457155895311066126421)
                ·
                  refine ⟨201216294795648176556169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17170457155895311066126421 201216294795648176556169)
                  ·
                    rfl

theorem cell23_3526806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3526806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526806 prefixEnd_3526806 := by exact prefixLift 3526806
  have htrace : WordTrace (prefixWord ++ tailWord_3526806) baseStart_3526806 baseEnd_3526806 := by
    simpa [prefixWord, tailWord_3526806, baseEnd_3526806] using wordTrace_append hprefix tailTrace_3526806
  have hstable : (prefixWord ++ tailWord_3526806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526806).length < 2 ^ (prefixWord ++ tailWord_3526806).sum := by decide
  have hdescent : baseEnd_3526806 < baseStart_3526806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526850 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3526850 : Nat := 118140960795 + 3526850 * 2 ^ 59
def prefixEnd_3526850 : Nat := 4983230072969 + 3 ^ 40 * 3526850 * 2
def baseEnd_3526850 : Nat := 1810969246309631416855319

theorem tailTrace_3526850 : CollatzResearch.WordTrace tailWord_3526850 prefixEnd_3526850 1810969246309631416855319 := by
  unfold tailWord_3526850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32158696818208065717632501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85756524848554841913686669 32158696818208065717632501)
  ·
    refine ⟨3014877826707006161028047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32158696818208065717632501 3014877826707006161028047)
    ·
      refine ⟨4522316740060509241542071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014877826707006161028047 4522316740060509241542071)
      ·
        refine ⟨6783475110090763862313107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522316740060509241542071 6783475110090763862313107)
        ·
          refine ⟨10175212665136145793469661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783475110090763862313107 10175212665136145793469661)
          ·
            refine ⟨3815704749426054672551123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10175212665136145793469661 3815704749426054672551123)
            ·
              refine ⟨5723557124139082008826685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815704749426054672551123 5723557124139082008826685)
              ·
                refine ⟨2146333921552155753310007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723557124139082008826685 2146333921552155753310007)
                ·
                  refine ⟨3219500882328233629965011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146333921552155753310007 3219500882328233629965011)
                  ·
                    refine ⟨4829251323492350444947517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219500882328233629965011 4829251323492350444947517)
                    ·
                      refine ⟨1810969246309631416855319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4829251323492350444947517 1810969246309631416855319)
                      ·
                        rfl

theorem cell23_3526850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3526850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526850 prefixEnd_3526850 := by exact prefixLift 3526850
  have htrace : WordTrace (prefixWord ++ tailWord_3526850) baseStart_3526850 baseEnd_3526850 := by
    simpa [prefixWord, tailWord_3526850, baseEnd_3526850] using wordTrace_append hprefix tailTrace_3526850
  have hstable : (prefixWord ++ tailWord_3526850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526850).length < 2 ^ (prefixWord ++ tailWord_3526850).sum := by decide
  have hdescent : baseEnd_3526850 < baseStart_3526850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526872 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3526872 : Nat := 118140960795 + 3526872 * 2 ^ 59
def prefixEnd_3526872 : Nat := 4983230072969 + 3 ^ 40 * 3526872 * 2
def baseEnd_3526872 : Nat := 1810980542884030330780217

theorem tailTrace_3526872 : CollatzResearch.WordTrace tailWord_3526872 prefixEnd_3526872 1810980542884030330780217 := by
  unfold tailWord_3526872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64317794839376280313915435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85757059785835040418553913 64317794839376280313915435)
  ·
    refine ⟨96476692259064420470873153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64317794839376280313915435 96476692259064420470873153)
    ·
      refine ⟨72357519194298315353154865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96476692259064420470873153 72357519194298315353154865)
      ·
        refine ⟨54268139395723736514866149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72357519194298315353154865 54268139395723736514866149)
        ·
          refine ⟨10175276136698200596537403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54268139395723736514866149 10175276136698200596537403)
          ·
            refine ⟨15262914205047300894806105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175276136698200596537403 15262914205047300894806105)
            ·
              refine ⟨11447185653785475671104579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15262914205047300894806105 11447185653785475671104579)
              ·
                refine ⟨17170778480678213506656869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447185653785475671104579 17170778480678213506656869)
                ·
                  refine ⟨3219520965127165032498163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17170778480678213506656869 3219520965127165032498163)
                  ·
                    refine ⟨4829281447690747548747245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219520965127165032498163 4829281447690747548747245)
                    ·
                      refine ⟨1810980542884030330780217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4829281447690747548747245 1810980542884030330780217)
                      ·
                        rfl

theorem cell23_3526872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3526872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526872 prefixEnd_3526872 := by exact prefixLift 3526872
  have htrace : WordTrace (prefixWord ++ tailWord_3526872) baseStart_3526872 baseEnd_3526872 := by
    simpa [prefixWord, tailWord_3526872, baseEnd_3526872] using wordTrace_append hprefix tailTrace_3526872
  have hstable : (prefixWord ++ tailWord_3526872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526872).length < 2 ^ (prefixWord ++ tailWord_3526872).sum := by decide
  have hdescent : baseEnd_3526872 < baseStart_3526872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526883 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 2, 4]
def baseStart_3526883 : Nat := 118140960795 + 3526883 * 2 ^ 59
def prefixEnd_3526883 : Nat := 4983230072969 + 3 ^ 40 * 3526883 * 2
def baseEnd_3526883 : Nat := 603662063723743262580889

theorem tailTrace_3526883 : CollatzResearch.WordTrace tailWord_3526883 prefixEnd_3526883 603662063723743262580889 := by
  unfold tailWord_3526883
  simp only [CollatzResearch.WordTrace]
  refine ⟨128635990881712709506481303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85757327254475139670987535 128635990881712709506481303)
  ·
    refine ⟨192953986322569064259721955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128635990881712709506481303 192953986322569064259721955)
    ·
      refine ⟨289430979483853596389582933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192953986322569064259721955 289430979483853596389582933)
      ·
        refine ⟨3391769290826409332690425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 289430979483853596389582933 3391769290826409332690425)
        ·
          refine ⟨2543826968119806999517819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391769290826409332690425 2543826968119806999517819)
          ·
            refine ⟨3815740452179710499276729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543826968119806999517819 3815740452179710499276729)
            ·
              refine ⟨2861805339134782874457547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815740452179710499276729 2861805339134782874457547)
              ·
                refine ⟨4292708008702174311686321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861805339134782874457547 4292708008702174311686321)
                ·
                  refine ⟨3219531006526630733764741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292708008702174311686321 3219531006526630733764741)
                  ·
                    refine ⟨603662063723743262580889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219531006526630733764741 603662063723743262580889)
                    ·
                      rfl

theorem cell23_3526883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 4].length) (baseStart_3526883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526883 prefixEnd_3526883 := by exact prefixLift 3526883
  have htrace : WordTrace (prefixWord ++ tailWord_3526883) baseStart_3526883 baseEnd_3526883 := by
    simpa [prefixWord, tailWord_3526883, baseEnd_3526883] using wordTrace_append hprefix tailTrace_3526883
  have hstable : (prefixWord ++ tailWord_3526883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526883).length < 2 ^ (prefixWord ++ tailWord_3526883).sum := by decide
  have hdescent : baseEnd_3526883 < baseStart_3526883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526912 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2]
def baseStart_3526912 : Nat := 118140960795 + 3526912 * 2 ^ 59
def prefixEnd_3526912 : Nat := 4983230072969 + 3 ^ 40 * 3526912 * 2
def baseEnd_3526912 : Nat := 1811001082110210174280033

theorem tailTrace_3526912 : CollatzResearch.WordTrace tailWord_3526912 prefixEnd_3526912 1811001082110210174280033 := by
  unfold tailWord_3526912
  simp only [CollatzResearch.WordTrace]
  refine ⟨64318524299303823729643495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85758032399071764972857993 64318524299303823729643495)
  ·
    refine ⟨96477786448955735594465243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64318524299303823729643495 96477786448955735594465243)
    ·
      refine ⟨144716679673433603391697865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96477786448955735594465243 144716679673433603391697865)
      ·
        refine ⟨108537509755075202543773399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144716679673433603391697865 108537509755075202543773399)
        ·
          refine ⟨162806264632612803815660099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108537509755075202543773399 162806264632612803815660099)
          ·
            refine ⟨244209396948919205723490149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162806264632612803815660099 244209396948919205723490149)
            ·
              refine ⟨45789261927922351073154403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244209396948919205723490149 45789261927922351073154403)
              ·
                refine ⟨68683892891883526609731605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45789261927922351073154403 68683892891883526609731605)
                ·
                  refine ⟨3219557479307040309831169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68683892891883526609731605 3219557479307040309831169)
                  ·
                    refine ⟨2414668109480280232373377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219557479307040309831169 2414668109480280232373377)
                    ·
                      refine ⟨1811001082110210174280033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414668109480280232373377 1811001082110210174280033)
                      ·
                        rfl

theorem cell23_3526912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_3526912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526912 prefixEnd_3526912 := by exact prefixLift 3526912
  have htrace : WordTrace (prefixWord ++ tailWord_3526912) baseStart_3526912 baseEnd_3526912 := by
    simpa [prefixWord, tailWord_3526912, baseEnd_3526912] using wordTrace_append hprefix tailTrace_3526912
  have hstable : (prefixWord ++ tailWord_3526912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526912).length < 2 ^ (prefixWord ++ tailWord_3526912).sum := by decide
  have hdescent : baseEnd_3526912 < baseStart_3526912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526929 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_3526929 : Nat := 118140960795 + 3526929 * 2 ^ 59
def prefixEnd_3526929 : Nat := 4983230072969 + 3 ^ 40 * 3526929 * 2
def baseEnd_3526929 : Nat := 1811009811281336607767455

theorem tailTrace_3526929 : CollatzResearch.WordTrace tailWord_3526929 prefixEnd_3526929 1811009811281336607767455 := by
  unfold tailWord_3526929
  simp only [CollatzResearch.WordTrace]
  refine ⟨128637668639546059362655841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85758445759697372908437227 128637668639546059362655841)
  ·
    refine ⟨96478251479659544521991881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128637668639546059362655841 96478251479659544521991881)
    ·
      refine ⟨72358688609744658391493911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96478251479659544521991881 72358688609744658391493911)
      ·
        refine ⟨108538032914616987587240867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72358688609744658391493911 108538032914616987587240867)
        ·
          refine ⟨162807049371925481380861301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108538032914616987587240867 162807049371925481380861301)
          ·
            refine ⟨15263160878618013879455747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162807049371925481380861301 15263160878618013879455747)
            ·
              refine ⟨22894741317927020819183621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263160878618013879455747 22894741317927020819183621)
              ·
                refine ⟨4292763997111316403596929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22894741317927020819183621 4292763997111316403596929)
                ·
                  refine ⟨3219572997833487302697697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292763997111316403596929 3219572997833487302697697)
                  ·
                    refine ⟨2414679748375115477023273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219572997833487302697697 2414679748375115477023273)
                    ·
                      refine ⟨1811009811281336607767455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414679748375115477023273 1811009811281336607767455)
                      ·
                        rfl

theorem cell23_3526929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_3526929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526929 prefixEnd_3526929 := by exact prefixLift 3526929
  have htrace : WordTrace (prefixWord ++ tailWord_3526929) baseStart_3526929 baseEnd_3526929 := by
    simpa [prefixWord, tailWord_3526929, baseEnd_3526929] using wordTrace_append hprefix tailTrace_3526929
  have hstable : (prefixWord ++ tailWord_3526929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526929).length < 2 ^ (prefixWord ++ tailWord_3526929).sum := by decide
  have hdescent : baseEnd_3526929 < baseStart_3526929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526945 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3526945 : Nat := 118140960795 + 3526945 * 2 ^ 59
def prefixEnd_3526945 : Nat := 4983230072969 + 3 ^ 40 * 3526945 * 2
def baseEnd_3526945 : Nat := 1811018026971808545167381

theorem tailTrace_3526945 : CollatzResearch.WordTrace tailWord_3526945 prefixEnd_3526945 1811018026971808545167381 := by
  unfold tailWord_3526945
  simp only [CollatzResearch.WordTrace]
  refine ⟨128638252207488094095238289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85758834804992062730158859 128638252207488094095238289)
  ·
    refine ⟨96478689155616070571428717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128638252207488094095238289 96478689155616070571428717)
    ·
      refine ⟨36179508433356026464285769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96478689155616070571428717 36179508433356026464285769)
      ·
        refine ⟨27134631325017019848214327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36179508433356026464285769 27134631325017019848214327)
        ·
          refine ⟨40701946987525529772321491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134631325017019848214327 40701946987525529772321491)
          ·
            refine ⟨61052920481288294658482237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40701946987525529772321491 61052920481288294658482237)
            ·
              refine ⟨22894845180483110496930839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61052920481288294658482237 22894845180483110496930839)
              ·
                refine ⟨34342267770724665745396259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22894845180483110496930839 34342267770724665745396259)
                ·
                  refine ⟨51513401656086998618094389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34342267770724665745396259 51513401656086998618094389)
                  ·
                    refine ⟨4829381405258156120446349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51513401656086998618094389 4829381405258156120446349)
                    ·
                      refine ⟨1811018026971808545167381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4829381405258156120446349 1811018026971808545167381)
                      ·
                        rfl

theorem cell23_3526945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3526945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526945 prefixEnd_3526945 := by exact prefixLift 3526945
  have htrace : WordTrace (prefixWord ++ tailWord_3526945) baseStart_3526945 baseEnd_3526945 := by
    simpa [prefixWord, tailWord_3526945, baseEnd_3526945] using wordTrace_append hprefix tailTrace_3526945
  have hstable : (prefixWord ++ tailWord_3526945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526945).length < 2 ^ (prefixWord ++ tailWord_3526945).sum := by decide
  have hdescent : baseEnd_3526945 < baseStart_3526945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526946 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_3526946 : Nat := 118140960795 + 3526946 * 2 ^ 59
def prefixEnd_3526946 : Nat := 4983230072969 + 3 ^ 40 * 3526946 * 2
def baseEnd_3526946 : Nat := 1811018540452463041254877

theorem tailTrace_3526946 : CollatzResearch.WordTrace tailWord_3526946 prefixEnd_3526946 1811018540452463041254877 := by
  unfold tailWord_3526946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159572170121117816506173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85758859120322980844016461 32159572170121117816506173)
  ·
    refine ⟨12059839563795419181189815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32159572170121117816506173 12059839563795419181189815)
    ·
      refine ⟨18089759345693128771784723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12059839563795419181189815 18089759345693128771784723)
      ·
        refine ⟨27134639018539693157677085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18089759345693128771784723 27134639018539693157677085)
        ·
          refine ⟨10175489631952384934128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27134639018539693157677085 10175489631952384934128907)
          ·
            refine ⟨15263234447928577401193361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175489631952384934128907 15263234447928577401193361)
            ·
              refine ⟨11447425835946433050895021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15263234447928577401193361 11447425835946433050895021)
              ·
                refine ⟨4292784688479912394085633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11447425835946433050895021 4292784688479912394085633)
                ·
                  refine ⟨3219588516359934295564225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292784688479912394085633 3219588516359934295564225)
                  ·
                    refine ⟨2414691387269950721673169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219588516359934295564225 2414691387269950721673169)
                    ·
                      refine ⟨1811018540452463041254877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414691387269950721673169 1811018540452463041254877)
                      ·
                        rfl

theorem cell23_3526946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_3526946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526946 prefixEnd_3526946 := by exact prefixLift 3526946
  have htrace : WordTrace (prefixWord ++ tailWord_3526946) baseStart_3526946 baseEnd_3526946 := by
    simpa [prefixWord, tailWord_3526946, baseEnd_3526946] using wordTrace_append hprefix tailTrace_3526946
  have hstable : (prefixWord ++ tailWord_3526946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526946).length < 2 ^ (prefixWord ++ tailWord_3526946).sum := by decide
  have hdescent : baseEnd_3526946 < baseStart_3526946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526952 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 7]
def baseStart_3526952 : Nat := 118140960795 + 3526952 * 2 ^ 59
def prefixEnd_3526952 : Nat := 4983230072969 + 3 ^ 40 * 3526952 * 2
def baseEnd_3526952 : Nat := 201224624592932224197761

theorem tailTrace_3526952 : CollatzResearch.WordTrace tailWord_3526952 prefixEnd_3526952 201224624592932224197761 := by
  unfold tailWord_3526952
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319253759231367145371555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85759005012308489527162073 64319253759231367145371555)
  ·
    refine ⟨96478880638847050718057333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64319253759231367145371555 96478880638847050718057333)
    ·
      refine ⟨9044895059891911004817875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96478880638847050718057333 9044895059891911004817875)
      ·
        refine ⟨13567342589837866507226813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044895059891911004817875 13567342589837866507226813)
        ·
          refine ⟨5087753471189199940210055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13567342589837866507226813 5087753471189199940210055)
          ·
            refine ⟨7631630206783799910315083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087753471189199940210055 7631630206783799910315083)
            ·
              refine ⟨11447445310175699865472625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631630206783799910315083 11447445310175699865472625)
              ·
                refine ⟨8585583982631774899104469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447445310175699865472625 8585583982631774899104469)
                ·
                  refine ⟨201224624592932224197761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8585583982631774899104469 201224624592932224197761)
                  ·
                    rfl

theorem cell23_3526952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_3526952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526952 prefixEnd_3526952 := by exact prefixLift 3526952
  have htrace : WordTrace (prefixWord ++ tailWord_3526952) baseStart_3526952 baseEnd_3526952 := by
    simpa [prefixWord, tailWord_3526952, baseEnd_3526952] using wordTrace_append hprefix tailTrace_3526952
  have hstable : (prefixWord ++ tailWord_3526952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526952).length < 2 ^ (prefixWord ++ tailWord_3526952).sum := by decide
  have hdescent : baseEnd_3526952 < baseStart_3526952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526965 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3526965 : Nat := 118140960795 + 3526965 * 2 ^ 59
def prefixEnd_3526965 : Nat := 4983230072969 + 3 ^ 40 * 3526965 * 2
def baseEnd_3526965 : Nat := 603676098861632822305763

theorem tailTrace_3526965 : CollatzResearch.WordTrace tailWord_3526965 prefixEnd_3526965 603676098861632822305763 := by
  unfold tailWord_3526965
  simp only [CollatzResearch.WordTrace]
  refine ⟨128638981667415637510966349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85759321111610425007310899 128638981667415637510966349)
  ·
    refine ⟨48239618125280864066612381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128638981667415637510966349 48239618125280864066612381)
    ·
      refine ⟨18089856796980324024979643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48239618125280864066612381 18089856796980324024979643)
      ·
        refine ⟨27134785195470486037469465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18089856796980324024979643 27134785195470486037469465)
        ·
          refine ⟨20351088896602864528102099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27134785195470486037469465 20351088896602864528102099)
          ·
            refine ⟨30526633344904296792153149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20351088896602864528102099 30526633344904296792153149)
            ·
              refine ⟨11447487504339111297057431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30526633344904296792153149 11447487504339111297057431)
              ·
                refine ⟨17171231256508666945586147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447487504339111297057431 17171231256508666945586147)
                ·
                  refine ⟨25756846884763000418379221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17171231256508666945586147 25756846884763000418379221)
                  ·
                    refine ⟨603676098861632822305763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25756846884763000418379221 603676098861632822305763)
                    ·
                      rfl

theorem cell23_3526965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3526965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526965 prefixEnd_3526965 := by exact prefixLift 3526965
  have htrace : WordTrace (prefixWord ++ tailWord_3526965) baseStart_3526965 baseEnd_3526965 := by
    simpa [prefixWord, tailWord_3526965, baseEnd_3526965] using wordTrace_append hprefix tailTrace_3526965
  have hstable : (prefixWord ++ tailWord_3526965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526965).length < 2 ^ (prefixWord ++ tailWord_3526965).sum := by decide
  have hdescent : baseEnd_3526965 < baseStart_3526965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526969 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 5]
def baseStart_3526969 : Nat := 118140960795 + 3526969 * 2 ^ 59
def prefixEnd_3526969 : Nat := 4983230072969 + 3 ^ 40 * 3526969 * 2
def baseEnd_3526969 : Nat := 201225594500835161251919

theorem tailTrace_3526969 : CollatzResearch.WordTrace tailWord_3526969 prefixEnd_3526969 201225594500835161251919 := by
  unfold tailWord_3526969
  simp only [CollatzResearch.WordTrace]
  refine ⟨128639127559401146194111961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85759418372934097462741307 128639127559401146194111961)
  ·
    refine ⟨96479345669550859645583971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128639127559401146194111961 96479345669550859645583971)
    ·
      refine ⟨144719018504326289468375957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96479345669550859645583971 144719018504326289468375957)
      ·
        refine ⟨6783703992390294818830123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144719018504326289468375957 6783703992390294818830123)
        ·
          refine ⟨10175555988585442228245185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783703992390294818830123 10175555988585442228245185)
          ·
            refine ⟨7631666991439081671183889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175555988585442228245185 7631666991439081671183889)
            ·
              refine ⟨5723750243579311253387917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631666991439081671183889 5723750243579311253387917)
              ·
                refine ⟨2146406341342241720020469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723750243579311253387917 2146406341342241720020469)
                ·
                  refine ⟨201225594500835161251919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2146406341342241720020469 201225594500835161251919)
                  ·
                    rfl

theorem cell23_3526969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 5].length) (baseStart_3526969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526969 prefixEnd_3526969 := by exact prefixLift 3526969
  have htrace : WordTrace (prefixWord ++ tailWord_3526969) baseStart_3526969 baseEnd_3526969 := by
    simpa [prefixWord, tailWord_3526969, baseEnd_3526969] using wordTrace_append hprefix tailTrace_3526969
  have hstable : (prefixWord ++ tailWord_3526969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526969).length < 2 ^ (prefixWord ++ tailWord_3526969).sum := by decide
  have hdescent : baseEnd_3526969 < baseStart_3526969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526980 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3526980 : Nat := 118140960795 + 3526980 * 2 ^ 59
def prefixEnd_3526980 : Nat := 4983230072969 + 3 ^ 40 * 3526980 * 2
def baseEnd_3526980 : Nat := 1811035998794715908229721

theorem tailTrace_3526980 : CollatzResearch.WordTrace tailWord_3526980 prefixEnd_3526980 1811035998794715908229721 := by
  unfold tailWord_3526980
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319764381180647536381197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85759685841574196715174929 64319764381180647536381197)
  ·
    refine ⟨24119911642942742826142949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64319764381180647536381197 24119911642942742826142949)
    ·
      refine ⟨4522483433051764279901803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24119911642942742826142949 4522483433051764279901803)
      ·
        refine ⟨6783725149577646419852705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522483433051764279901803 6783725149577646419852705)
        ·
          refine ⟨5087793862183234814889529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6783725149577646419852705 5087793862183234814889529)
          ·
            refine ⟨3815845396637426111167147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5087793862183234814889529 3815845396637426111167147)
            ·
              refine ⟨5723768094956139166750721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815845396637426111167147 5723768094956139166750721)
              ·
                refine ⟨4292826071217104375063041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723768094956139166750721 4292826071217104375063041)
                ·
                  refine ⟨3219619553412828281297281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292826071217104375063041 3219619553412828281297281)
                  ·
                    refine ⟨2414714665059621210972961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219619553412828281297281 2414714665059621210972961)
                    ·
                      refine ⟨1811035998794715908229721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414714665059621210972961 1811035998794715908229721)
                      ·
                        rfl

theorem cell23_3526980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3526980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526980 prefixEnd_3526980 := by exact prefixLift 3526980
  have htrace : WordTrace (prefixWord ++ tailWord_3526980) baseStart_3526980 baseEnd_3526980 := by
    simpa [prefixWord, tailWord_3526980, baseEnd_3526980] using wordTrace_append hprefix tailTrace_3526980
  have hstable : (prefixWord ++ tailWord_3526980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526980).length < 2 ^ (prefixWord ++ tailWord_3526980).sum := by decide
  have hdescent : baseEnd_3526980 < baseStart_3526980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526985 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_3526985 : Nat := 118140960795 + 3526985 * 2 ^ 59
def prefixEnd_3526985 : Nat := 4983230072969 + 3 ^ 40 * 3526985 * 2
def baseEnd_3526985 : Nat := 1811038566197988388667197

theorem tailTrace_3526985 : CollatzResearch.WordTrace tailWord_3526985 prefixEnd_3526985 1811038566197988388667197 := by
  unfold tailWord_3526985
  simp only [CollatzResearch.WordTrace]
  refine ⟨128639711127343180926694409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85759807418228787284462939 128639711127343180926694409)
  ·
    refine ⟨96479783345507385695020807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128639711127343180926694409 96479783345507385695020807)
    ·
      refine ⟨144719675018261078542531211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96479783345507385695020807 144719675018261078542531211)
      ·
        refine ⟨217079512527391617813796817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144719675018261078542531211 217079512527391617813796817)
        ·
          refine ⟨162809634395543713360347613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217079512527391617813796817 162809634395543713360347613)
          ·
            refine ⟨61053612898328892510130355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162809634395543713360347613 61053612898328892510130355)
            ·
              refine ⟨91580419347493338765195533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61053612898328892510130355 91580419347493338765195533)
              ·
                refine ⟨34342657255310002036948325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91580419347493338765195533 34342657255310002036948325)
                ·
                  refine ⟨6439248235370625381927811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34342657255310002036948325 6439248235370625381927811)
                  ·
                    refine ⟨9658872353055938072891717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439248235370625381927811 9658872353055938072891717)
                    ·
                      refine ⟨1811038566197988388667197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9658872353055938072891717 1811038566197988388667197)
                      ·
                        rfl

theorem cell23_3526985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_3526985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3526985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3526985 prefixEnd_3526985 := by exact prefixLift 3526985
  have htrace : WordTrace (prefixWord ++ tailWord_3526985) baseStart_3526985 baseEnd_3526985 := by
    simpa [prefixWord, tailWord_3526985, baseEnd_3526985] using wordTrace_append hprefix tailTrace_3526985
  have hstable : (prefixWord ++ tailWord_3526985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526985).length < 2 ^ (prefixWord ++ tailWord_3526985).sum := by decide
  have hdescent : baseEnd_3526985 < baseStart_3526985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527012 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_3527012 : Nat := 118140960795 + 3527012 * 2 ^ 59
def prefixEnd_3527012 : Nat := 4983230072969 + 3 ^ 40 * 3527012 * 2
def baseEnd_3527012 : Nat := 603684143391886594343191

theorem tailTrace_3527012 : CollatzResearch.WordTrace tailWord_3527012 prefixEnd_3527012 603684143391886594343191 := by
  unfold tailWord_3527012
  simp only [CollatzResearch.WordTrace]
  refine ⟨64320347949122682268963645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85760463932163576358618193 64320347949122682268963645)
  ·
    refine ⟨24120130480921005850861367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64320347949122682268963645 24120130480921005850861367)
    ·
      refine ⟨36180195721381508776292051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24120130480921005850861367 36180195721381508776292051)
      ·
        refine ⟨54270293582072263164438077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36180195721381508776292051 54270293582072263164438077)
        ·
          refine ⟨20351360093277098686664279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54270293582072263164438077 20351360093277098686664279)
          ·
            refine ⟨30527040139915648029996419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20351360093277098686664279 30527040139915648029996419)
            ·
              refine ⟨45790560209873472044994629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30527040139915648029996419 45790560209873472044994629)
              ·
                refine ⟨8585730039351276008436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45790560209873472044994629 8585730039351276008436493)
                ·
                  refine ⟨3219648764756728503163685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8585730039351276008436493 3219648764756728503163685)
                  ·
                    refine ⟨603684143391886594343191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219648764756728503163685 603684143391886594343191)
                    ·
                      rfl

theorem cell23_3527012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_3527012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527012 prefixEnd_3527012 := by exact prefixLift 3527012
  have htrace : WordTrace (prefixWord ++ tailWord_3527012) baseStart_3527012 baseEnd_3527012 := by
    simpa [prefixWord, tailWord_3527012, baseEnd_3527012] using wordTrace_append hprefix tailTrace_3527012
  have hstable : (prefixWord ++ tailWord_3527012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527012).length < 2 ^ (prefixWord ++ tailWord_3527012).sum := by decide
  have hdescent : baseEnd_3527012 < baseStart_3527012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527072 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_3527072 : Nat := 118140960795 + 3527072 * 2 ^ 59
def prefixEnd_3527072 : Nat := 4983230072969 + 3 ^ 40 * 3527072 * 2
def baseEnd_3527072 : Nat := 603694413004976516093099

theorem tailTrace_3527072 : CollatzResearch.WordTrace tailWord_3527072 prefixEnd_3527072 603694413004976516093099 := by
  unfold tailWord_3527072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64321442139013997392555735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85761922852018663190074313 64321442139013997392555735)
  ·
    refine ⟨96482163208520996088833603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64321442139013997392555735 96482163208520996088833603)
    ·
      refine ⟨144723244812781494133250405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96482163208520996088833603 144723244812781494133250405)
      ·
        refine ⟨27135608402396530149984451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144723244812781494133250405 27135608402396530149984451)
        ·
          refine ⟨40703412603594795224976677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27135608402396530149984451 40703412603594795224976677)
          ·
            refine ⟨7631889863174024104683127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40703412603594795224976677 7631889863174024104683127)
            ·
              refine ⟨11447834794761036157024691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631889863174024104683127 11447834794761036157024691)
              ·
                refine ⟨17171752192141554235537037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447834794761036157024691 17171752192141554235537037)
                ·
                  refine ⟨6439407072053082838326389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17171752192141554235537037 6439407072053082838326389)
                  ·
                    refine ⟨603694413004976516093099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6439407072053082838326389 603694413004976516093099)
                    ·
                      rfl

theorem cell23_3527072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_3527072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527072 prefixEnd_3527072 := by exact prefixLift 3527072
  have htrace : WordTrace (prefixWord ++ tailWord_3527072) baseStart_3527072 baseEnd_3527072 := by
    simpa [prefixWord, tailWord_3527072, baseEnd_3527072] using wordTrace_append hprefix tailTrace_3527072
  have hstable : (prefixWord ++ tailWord_3527072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527072).length < 2 ^ (prefixWord ++ tailWord_3527072).sum := by decide
  have hdescent : baseEnd_3527072 < baseStart_3527072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527109 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_3527109 : Nat := 118140960795 + 3527109 * 2 ^ 59
def prefixEnd_3527109 : Nat := 4983230072969 + 3 ^ 40 * 3527109 * 2
def baseEnd_3527109 : Nat := 1811102237799145903516627

theorem tailTrace_3527109 : CollatzResearch.WordTrace tailWord_3527109 prefixEnd_3527109 1811102237799145903516627 := by
  unfold tailWord_3527109
  simp only [CollatzResearch.WordTrace]
  refine ⟨128644233778893950104208381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85762822519262633402805587 128644233778893950104208381)
  ·
    refine ⟨48241587667085231289078143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128644233778893950104208381 48241587667085231289078143)
    ·
      refine ⟨72362381500627846933617215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48241587667085231289078143 72362381500627846933617215)
      ·
        refine ⟨108543572250941770400425823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72362381500627846933617215 108543572250941770400425823)
        ·
          refine ⟨162815358376412655600638735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108543572250941770400425823 162815358376412655600638735)
          ·
            refine ⟨244223037564618983400958103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162815358376412655600638735 244223037564618983400958103)
            ·
              refine ⟨366334556346928475101437155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244223037564618983400958103 366334556346928475101437155)
              ·
                refine ⟨549501834520392712652155733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366334556346928475101437155 549501834520392712652155733)
                ·
                  refine ⟨3219737311642926050696225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 549501834520392712652155733 3219737311642926050696225)
                  ·
                    refine ⟨2414802983732194538022169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219737311642926050696225 2414802983732194538022169)
                    ·
                      refine ⟨1811102237799145903516627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414802983732194538022169 1811102237799145903516627)
                      ·
                        rfl

theorem cell23_3527109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_3527109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527109 prefixEnd_3527109 := by exact prefixLift 3527109
  have htrace : WordTrace (prefixWord ++ tailWord_3527109) baseStart_3527109 baseEnd_3527109 := by
    simpa [prefixWord, tailWord_3527109, baseEnd_3527109] using wordTrace_append hprefix tailTrace_3527109
  have hstable : (prefixWord ++ tailWord_3527109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527109).length < 2 ^ (prefixWord ++ tailWord_3527109).sum := by decide
  have hdescent : baseEnd_3527109 < baseStart_3527109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527126 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3527126 : Nat := 118140960795 + 3527126 * 2 ^ 59
def prefixEnd_3527126 : Nat := 4983230072969 + 3 ^ 40 * 3527126 * 2
def baseEnd_3527126 : Nat := 1811110966970272337004049

theorem tailTrace_3527126 : CollatzResearch.WordTrace tailWord_3527126 prefixEnd_3527126 1811110966970272337004049 := by
  unfold tailWord_3527126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040303363739522625473577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85763235879888241338384821 8040303363739522625473577)
  ·
    refine ⟨6030227522804641969105183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8040303363739522625473577 6030227522804641969105183)
    ·
      refine ⟨9045341284206962953657775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030227522804641969105183 9045341284206962953657775)
      ·
        refine ⟨13568011926310444430486663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045341284206962953657775 13568011926310444430486663)
        ·
          refine ⟨20352017889465666645729995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568011926310444430486663 20352017889465666645729995)
          ·
            refine ⟨30528026834198499968594993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20352017889465666645729995 30528026834198499968594993)
            ·
              refine ⟨22896020125648874976446245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30528026834198499968594993 22896020125648874976446245)
              ·
                refine ⟨4293003773559164058083671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22896020125648874976446245 4293003773559164058083671)
                ·
                  refine ⟨6439505660338746087125507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293003773559164058083671 6439505660338746087125507)
                  ·
                    refine ⟨9659258490508119130688261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439505660338746087125507 9659258490508119130688261)
                    ·
                      refine ⟨1811110966970272337004049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9659258490508119130688261 1811110966970272337004049)
                      ·
                        rfl

theorem cell23_3527126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3527126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527126 prefixEnd_3527126 := by exact prefixLift 3527126
  have htrace : WordTrace (prefixWord ++ tailWord_3527126) baseStart_3527126 baseEnd_3527126 := by
    simpa [prefixWord, tailWord_3527126, baseEnd_3527126] using wordTrace_append hprefix tailTrace_3527126
  have hstable : (prefixWord ++ tailWord_3527126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527126).length < 2 ^ (prefixWord ++ tailWord_3527126).sum := by decide
  have hdescent : baseEnd_3527126 < baseStart_3527126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527129 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3527129 : Nat := 118140960795 + 3527129 * 2 ^ 59
def prefixEnd_3527129 : Nat := 4983230072969 + 3 ^ 40 * 3527129 * 2
def baseEnd_3527129 : Nat := 1811112507412235825266535

theorem tailTrace_3527129 : CollatzResearch.WordTrace tailWord_3527129 prefixEnd_3527129 1811112507412235825266535 := by
  unfold tailWord_3527129
  simp only [CollatzResearch.WordTrace]
  refine ⟨128644963238821493519936441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85763308825880995679957627 128644963238821493519936441)
  ·
    refine ⟨96483722429116120139952331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128644963238821493519936441 96483722429116120139952331)
    ·
      refine ⟨144725583643674180209928497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96483722429116120139952331 144725583643674180209928497)
      ·
        refine ⟨108544187732755635157446373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144725583643674180209928497 108544187732755635157446373)
        ·
          refine ⟨20352035199891681592021195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108544187732755635157446373 20352035199891681592021195)
          ·
            refine ⟨30528052799837522388031793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20352035199891681592021195 30528052799837522388031793)
            ·
              refine ⟨22896039599878141791023845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30528052799837522388031793 22896039599878141791023845)
              ·
                refine ⟨4293007424977151585816971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22896039599878141791023845 4293007424977151585816971)
                ·
                  refine ⟨6439511137465727378725457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293007424977151585816971 6439511137465727378725457)
                  ·
                    refine ⟨4829633353099295534044093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6439511137465727378725457 4829633353099295534044093)
                    ·
                      refine ⟨1811112507412235825266535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4829633353099295534044093 1811112507412235825266535)
                      ·
                        rfl

theorem cell23_3527129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3527129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527129 prefixEnd_3527129 := by exact prefixLift 3527129
  have htrace : WordTrace (prefixWord ++ tailWord_3527129) baseStart_3527129 baseEnd_3527129 := by
    simpa [prefixWord, tailWord_3527129, baseEnd_3527129] using wordTrace_append hprefix tailTrace_3527129
  have hstable : (prefixWord ++ tailWord_3527129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527129).length < 2 ^ (prefixWord ++ tailWord_3527129).sum := by decide
  have hdescent : baseEnd_3527129 < baseStart_3527129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527145 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_3527145 : Nat := 118140960795 + 3527145 * 2 ^ 59
def prefixEnd_3527145 : Nat := 4983230072969 + 3 ^ 40 * 3527145 * 2
def baseEnd_3527145 : Nat := 603706907700902587555487

theorem tailTrace_3527145 : CollatzResearch.WordTrace tailWord_3527145 prefixEnd_3527145 603706907700902587555487 := by
  unfold tailWord_3527145
  simp only [CollatzResearch.WordTrace]
  refine ⟨128645546806763528252518889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85763697871175685501679259 128645546806763528252518889)
  ·
    refine ⟨96484160105072646189389167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128645546806763528252518889 96484160105072646189389167)
    ·
      refine ⟨144726240157608969284083751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96484160105072646189389167 144726240157608969284083751)
      ·
        refine ⟨217089360236413453926125627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144726240157608969284083751 217089360236413453926125627)
        ·
          refine ⟨325634040354620180889188441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217089360236413453926125627 325634040354620180889188441)
          ·
            refine ⟨244225530265965135666891331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325634040354620180889188441 244225530265965135666891331)
            ·
              refine ⟨366338295398947703500336997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244225530265965135666891331 366338295398947703500336997)
              ·
                refine ⟨68688430387302694406313187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366338295398947703500336997 68688430387302694406313187)
                ·
                  refine ⟨103032645580954041609469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68688430387302694406313187 103032645580954041609469781)
                  ·
                    refine ⟨603706907700902587555487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103032645580954041609469781 603706907700902587555487)
                    ·
                      rfl

theorem cell23_3527145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_3527145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527145 prefixEnd_3527145 := by exact prefixLift 3527145
  have htrace : WordTrace (prefixWord ++ tailWord_3527145) baseStart_3527145 baseEnd_3527145 := by
    simpa [prefixWord, tailWord_3527145, baseEnd_3527145] using wordTrace_append hprefix tailTrace_3527145
  have hstable : (prefixWord ++ tailWord_3527145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527145).length < 2 ^ (prefixWord ++ tailWord_3527145).sum := by decide
  have hdescent : baseEnd_3527145 < baseStart_3527145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527146 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_3527146 : Nat := 118140960795 + 3527146 * 2 ^ 59
def prefixEnd_3527146 : Nat := 4983230072969 + 3 ^ 40 * 3527146 * 2
def baseEnd_3527146 : Nat := 1811121236583362258753957

theorem tailTrace_3527146 : CollatzResearch.WordTrace tailWord_3527146 prefixEnd_3527146 1811121236583362258753957 := by
  unfold tailWord_3527146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161395819939976355826323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85763722186506603615536861 32161395819939976355826323)
  ·
    refine ⟨48242093729909964533739485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32161395819939976355826323 48242093729909964533739485)
    ·
      refine ⟨18090785148716236700152307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48242093729909964533739485 18090785148716236700152307)
      ·
        refine ⟨27136177723074355050228461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18090785148716236700152307 27136177723074355050228461)
        ·
          refine ⟨10176066646152883143835673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27136177723074355050228461 10176066646152883143835673)
          ·
            refine ⟨7632049984614662357876755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10176066646152883143835673 7632049984614662357876755)
            ·
              refine ⟨11448074976921993536815133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632049984614662357876755 11448074976921993536815133)
              ·
                refine ⟨4293028116345747576305675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11448074976921993536815133 4293028116345747576305675)
                ·
                  refine ⟨6439542174518621364458513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293028116345747576305675 6439542174518621364458513)
                  ·
                    refine ⟨4829656630888966023343885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6439542174518621364458513 4829656630888966023343885)
                    ·
                      refine ⟨1811121236583362258753957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4829656630888966023343885 1811121236583362258753957)
                      ·
                        rfl

theorem cell23_3527146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_3527146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527146 prefixEnd_3527146 := by exact prefixLift 3527146
  have htrace : WordTrace (prefixWord ++ tailWord_3527146) baseStart_3527146 baseEnd_3527146 := by
    simpa [prefixWord, tailWord_3527146, baseEnd_3527146] using wordTrace_append hprefix tailTrace_3527146
  have hstable : (prefixWord ++ tailWord_3527146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527146).length < 2 ^ (prefixWord ++ tailWord_3527146).sum := by decide
  have hdescent : baseEnd_3527146 < baseStart_3527146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527170 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3527170 : Nat := 118140960795 + 3527170 * 2 ^ 59
def prefixEnd_3527170 : Nat := 4983230072969 + 3 ^ 40 * 3527170 * 2
def baseEnd_3527170 : Nat := 603711186706356721617949

theorem tailTrace_3527170 : CollatzResearch.WordTrace tailWord_3527170 prefixEnd_3527170 603711186706356721617949 := by
  unfold tailWord_3527170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161614657918239380544741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85764305754448638348119309 32161614657918239380544741)
  ·
    refine ⟨6030302748359669883852139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32161614657918239380544741 6030302748359669883852139)
    ·
      refine ⟨9045454122539504825778209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030302748359669883852139 9045454122539504825778209)
      ·
        refine ⟨6784090591904628619333657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9045454122539504825778209 6784090591904628619333657)
        ·
          refine ⟨5088067943928471464500243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6784090591904628619333657 5088067943928471464500243)
          ·
            refine ⟨7632101915892707196750365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088067943928471464500243 7632101915892707196750365)
            ·
              refine ⟨2862038218459765198781387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7632101915892707196750365 2862038218459765198781387)
              ·
                refine ⟨4293057327689647798172081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862038218459765198781387 4293057327689647798172081)
                ·
                  refine ⟨3219792995767235848629061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4293057327689647798172081 3219792995767235848629061)
                  ·
                    refine ⟨603711186706356721617949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219792995767235848629061 603711186706356721617949)
                    ·
                      rfl

theorem cell23_3527170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3527170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527170 prefixEnd_3527170 := by exact prefixLift 3527170
  have htrace : WordTrace (prefixWord ++ tailWord_3527170) baseStart_3527170 baseEnd_3527170 := by
    simpa [prefixWord, tailWord_3527170, baseEnd_3527170] using wordTrace_append hprefix tailTrace_3527170
  have hstable : (prefixWord ++ tailWord_3527170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527170).length < 2 ^ (prefixWord ++ tailWord_3527170).sum := by decide
  have hdescent : baseEnd_3527170 < baseStart_3527170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527199 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 4, 2]
def baseStart_3527199 : Nat := 118140960795 + 3527199 * 2 ^ 59
def prefixEnd_3527199 : Nat := 4983230072969 + 3 ^ 40 * 3527199 * 2
def baseEnd_3527199 : Nat := 1811148451058050551391213

theorem tailTrace_3527199 : CollatzResearch.WordTrace tailWord_3527199 prefixEnd_3527199 1811148451058050551391213 := by
  unfold tailWord_3527199
  simp only [CollatzResearch.WordTrace]
  refine ⟨128647516348567895474984651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85765010899045263649989767 128647516348567895474984651)
  ·
    refine ⟨192971274522851843212476977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128647516348567895474984651 192971274522851843212476977)
    ·
      refine ⟨144728455892138882409357733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192971274522851843212476977 144728455892138882409357733)
      ·
        refine ⟨27136585479776040451754575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144728455892138882409357733 27136585479776040451754575)
        ·
          refine ⟨40704878219664060677631863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27136585479776040451754575 40704878219664060677631863)
          ·
            refine ⟨61057317329496091016447795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40704878219664060677631863 61057317329496091016447795)
            ·
              refine ⟨91585975994244136524671693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61057317329496091016447795 91585975994244136524671693)
              ·
                refine ⟨34344740997841551196751885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91585975994244136524671693 34344740997841551196751885)
                ·
                  refine ⟨12879277874190581698781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34344740997841551196751885 12879277874190581698781957)
                  ·
                    refine ⟨2414864601410734068521617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12879277874190581698781957 2414864601410734068521617)
                    ·
                      refine ⟨1811148451058050551391213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414864601410734068521617 1811148451058050551391213)
                      ·
                        rfl

theorem cell23_3527199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_3527199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527199 prefixEnd_3527199 := by exact prefixLift 3527199
  have htrace : WordTrace (prefixWord ++ tailWord_3527199) baseStart_3527199 baseEnd_3527199 := by
    simpa [prefixWord, tailWord_3527199, baseEnd_3527199] using wordTrace_append hprefix tailTrace_3527199
  have hstable : (prefixWord ++ tailWord_3527199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527199).length < 2 ^ (prefixWord ++ tailWord_3527199).sum := by decide
  have hdescent : baseEnd_3527199 < baseStart_3527199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527212 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3527212 : Nat := 118140960795 + 3527212 * 2 ^ 59
def prefixEnd_3527212 : Nat := 4983230072969 + 3 ^ 40 * 3527212 * 2
def baseEnd_3527212 : Nat := 1811155126306559000528653

theorem tailTrace_3527212 : CollatzResearch.WordTrace tailWord_3527212 prefixEnd_3527212 1811155126306559000528653 := by
  unfold tailWord_3527212
  simp only [CollatzResearch.WordTrace]
  refine ⟨64323995248760399347603945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85765326998347199130138593 64323995248760399347603945)
  ·
    refine ⟨48242996436570299510702959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64323995248760399347603945 48242996436570299510702959)
    ·
      refine ⟨72364494654855449266054439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48242996436570299510702959 72364494654855449266054439)
      ·
        refine ⟨108546741982283173899081659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72364494654855449266054439 108546741982283173899081659)
        ·
          refine ⟨162820112973424760848622489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108546741982283173899081659 162820112973424760848622489)
          ·
            refine ⟨122115084730068570636466867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162820112973424760848622489 122115084730068570636466867)
            ·
              refine ⟨183172627095102855954700301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122115084730068570636466867 183172627095102855954700301)
              ·
                refine ⟨68689735160663570983012613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183172627095102855954700301 68689735160663570983012613)
                ·
                  refine ⟨12879325342624419559314865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68689735160663570983012613 12879325342624419559314865)
                  ·
                    refine ⟨9659494006968314669486149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12879325342624419559314865 9659494006968314669486149)
                    ·
                      refine ⟨1811155126306559000528653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9659494006968314669486149 1811155126306559000528653)
                      ·
                        rfl

theorem cell23_3527212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3527212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527212 prefixEnd_3527212 := by exact prefixLift 3527212
  have htrace : WordTrace (prefixWord ++ tailWord_3527212) baseStart_3527212 baseEnd_3527212 := by
    simpa [prefixWord, tailWord_3527212, baseEnd_3527212] using wordTrace_append hprefix tailTrace_3527212
  have hstable : (prefixWord ++ tailWord_3527212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527212).length < 2 ^ (prefixWord ++ tailWord_3527212).sum := by decide
  have hdescent : baseEnd_3527212 < baseStart_3527212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527216 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2]
def baseStart_3527216 : Nat := 118140960795 + 3527216 * 2 ^ 59
def prefixEnd_3527216 : Nat := 4983230072969 + 3 ^ 40 * 3527216 * 2
def baseEnd_3527216 : Nat := 1811157180229176984878635

theorem tailTrace_3527216 : CollatzResearch.WordTrace tailWord_3527216 prefixEnd_3527216 1811157180229176984878635 := by
  unfold tailWord_3527216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64324068194753153689176751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85765424259670871585569001 64324068194753153689176751)
  ·
    refine ⟨96486102292129730533765127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64324068194753153689176751 96486102292129730533765127)
    ·
      refine ⟨144729153438194595800647691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96486102292129730533765127 144729153438194595800647691)
      ·
        refine ⟨217093730157291893700971537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144729153438194595800647691 217093730157291893700971537)
        ·
          refine ⟨162820297617968920275728653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217093730157291893700971537 162820297617968920275728653)
          ·
            refine ⟨61057611606738345103398245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162820297617968920275728653 61057611606738345103398245)
            ·
              refine ⟨11448302176263439706887171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61057611606738345103398245 11448302176263439706887171)
              ·
                refine ⟨17172453264395159560330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448302176263439706887171 17172453264395159560330757)
                ·
                  refine ⟨3219834987074092417562017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17172453264395159560330757 3219834987074092417562017)
                  ·
                    refine ⟨2414876240305569313171513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3219834987074092417562017 2414876240305569313171513)
                    ·
                      refine ⟨1811157180229176984878635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414876240305569313171513 1811157180229176984878635)
                      ·
                        rfl

theorem cell23_3527216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2].length) (baseStart_3527216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527216 prefixEnd_3527216 := by exact prefixLift 3527216
  have htrace : WordTrace (prefixWord ++ tailWord_3527216) baseStart_3527216 baseEnd_3527216 := by
    simpa [prefixWord, tailWord_3527216, baseEnd_3527216] using wordTrace_append hprefix tailTrace_3527216
  have hstable : (prefixWord ++ tailWord_3527216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527216).length < 2 ^ (prefixWord ++ tailWord_3527216).sum := by decide
  have hdescent : baseEnd_3527216 < baseStart_3527216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527299 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 5, 4]
def baseStart_3527299 : Nat := 118140960795 + 3527299 * 2 ^ 59
def prefixEnd_3527299 : Nat := 4983230072969 + 3 ^ 40 * 3527299 * 2
def baseEnd_3527299 : Nat := 603733266374500053380251

theorem tailTrace_3527299 : CollatzResearch.WordTrace tailWord_3527299 prefixEnd_3527299 603733266374500053380251 := by
  unfold tailWord_3527299
  simp only [CollatzResearch.WordTrace]
  refine ⟨128651163648205612553624951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85767442432137075035749967 128651163648205612553624951)
  ·
    refine ⟨192976745472308418830437427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128651163648205612553624951 192976745472308418830437427)
    ·
      refine ⟨289465118208462628245656141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192976745472308418830437427 289465118208462628245656141)
      ·
        refine ⟨108549419328173485592121053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289465118208462628245656141 108549419328173485592121053)
        ·
          refine ⟨40706032248065057097045395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108549419328173485592121053 40706032248065057097045395)
          ·
            refine ⟨61059048372097585645568093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40706032248065057097045395 61059048372097585645568093)
            ·
              refine ⟨22897143139536594617088035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61059048372097585645568093 22897143139536594617088035)
              ·
                refine ⟨34345714709304891925632053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22897143139536594617088035 34345714709304891925632053)
                ·
                  refine ⟨3219910753997333618028005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34345714709304891925632053 3219910753997333618028005)
                  ·
                    refine ⟨603733266374500053380251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219910753997333618028005 603733266374500053380251)
                    ·
                      rfl

theorem cell23_3527299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 4].length) (baseStart_3527299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527299 prefixEnd_3527299 := by exact prefixLift 3527299
  have htrace : WordTrace (prefixWord ++ tailWord_3527299) baseStart_3527299 baseEnd_3527299 := by
    simpa [prefixWord, tailWord_3527299, baseEnd_3527299] using wordTrace_append hprefix tailTrace_3527299
  have hstable : (prefixWord ++ tailWord_3527299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527299).length < 2 ^ (prefixWord ++ tailWord_3527299).sum := by decide
  have hdescent : baseEnd_3527299 < baseStart_3527299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527306 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3527306 : Nat := 118140960795 + 3527306 * 2 ^ 59
def prefixEnd_3527306 : Nat := 4983230072969 + 3 ^ 40 * 3527306 * 2
def baseEnd_3527306 : Nat := 1811203393488081632753221

theorem tailTrace_3527306 : CollatzResearch.WordTrace tailWord_3527306 prefixEnd_3527306 1811203393488081632753221 := by
  unfold tailWord_3527306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32162854739795063187282443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85767612639453501832753181 32162854739795063187282443)
  ·
    refine ⟨48244282109692594780923665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32162854739795063187282443 48244282109692594780923665)
    ·
      refine ⟨36183211582269446085692749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48244282109692594780923665 36183211582269446085692749)
      ·
        refine ⟨13568704343351042282134781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36183211582269446085692749 13568704343351042282134781)
        ·
          refine ⟨5088264128756640855800543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13568704343351042282134781 5088264128756640855800543)
          ·
            refine ⟨7632396193134961283700815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088264128756640855800543 7632396193134961283700815)
            ·
              refine ⟨11448594289702441925551223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632396193134961283700815 11448594289702441925551223)
              ·
                refine ⟨17172891434553662888326835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448594289702441925551223 17172891434553662888326835)
                ·
                  refine ⟨25759337151830494332490253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17172891434553662888326835 25759337151830494332490253)
                  ·
                    refine ⟨9659751431936435374683845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25759337151830494332490253 9659751431936435374683845)
                    ·
                      refine ⟨1811203393488081632753221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9659751431936435374683845 1811203393488081632753221)
                      ·
                        rfl

theorem cell23_3527306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3527306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527306 prefixEnd_3527306 := by exact prefixLift 3527306
  have htrace : WordTrace (prefixWord ++ tailWord_3527306) baseStart_3527306 baseEnd_3527306 := by
    simpa [prefixWord, tailWord_3527306, baseEnd_3527306] using wordTrace_append hprefix tailTrace_3527306
  have hstable : (prefixWord ++ tailWord_3527306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527306).length < 2 ^ (prefixWord ++ tailWord_3527306).sum := by decide
  have hdescent : baseEnd_3527306 < baseStart_3527306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527383 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_3527383 : Nat := 118140960795 + 3527383 * 2 ^ 59
def prefixEnd_3527383 : Nat := 4983230072969 + 3 ^ 40 * 3527383 * 2
def baseEnd_3527383 : Nat := 1811242931498477831490367

theorem tailTrace_3527383 : CollatzResearch.WordTrace tailWord_3527383 prefixEnd_3527383 1811242931498477831490367 := by
  unfold tailWord_3527383
  simp only [CollatzResearch.WordTrace]
  refine ⟨128654227379901294899682803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85769484919934196599788535 128654227379901294899682803)
  ·
    refine ⟨192981341069851942349524205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128654227379901294899682803 192981341069851942349524205)
    ·
      refine ⟨72368002901194478381071577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192981341069851942349524205 72368002901194478381071577)
      ·
        refine ⟨54276002175895858785803683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72368002901194478381071577 54276002175895858785803683)
        ·
          refine ⟨81414003263843788178705525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54276002175895858785803683 81414003263843788178705525)
          ·
            refine ⟨7632562805985355141753643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81414003263843788178705525 7632562805985355141753643)
            ·
              refine ⟨11448844208978032712630465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632562805985355141753643 11448844208978032712630465)
              ·
                refine ⟨8586633156733524534472849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11448844208978032712630465 8586633156733524534472849)
                ·
                  refine ⟨6439974867550143400854637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8586633156733524534472849 6439974867550143400854637)
                  ·
                    refine ⟨2414990575331303775320489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6439974867550143400854637 2414990575331303775320489)
                    ·
                      refine ⟨1811242931498477831490367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2414990575331303775320489 1811242931498477831490367)
                      ·
                        rfl

theorem cell23_3527383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_3527383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527383 prefixEnd_3527383 := by exact prefixLift 3527383
  have htrace : WordTrace (prefixWord ++ tailWord_3527383) baseStart_3527383 baseEnd_3527383 := by
    simpa [prefixWord, tailWord_3527383, baseEnd_3527383] using wordTrace_append hprefix tailTrace_3527383
  have hstable : (prefixWord ++ tailWord_3527383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527383).length < 2 ^ (prefixWord ++ tailWord_3527383).sum := by decide
  have hdescent : baseEnd_3527383 < baseStart_3527383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527409 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3527409 : Nat := 118140960795 + 3527409 * 2 ^ 59
def prefixEnd_3527409 : Nat := 4983230072969 + 3 ^ 40 * 3527409 * 2
def baseEnd_3527409 : Nat := 1811256281995494729765247

theorem tailTrace_3527409 : CollatzResearch.WordTrace tailWord_3527409 prefixEnd_3527409 1811256281995494729765247 := by
  unfold tailWord_3527409
  simp only [CollatzResearch.WordTrace]
  refine ⟨128655175677807101340129281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85770117118538067560086187 128655175677807101340129281)
  ·
    refine ⟨96491381758355326005096961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128655175677807101340129281 96491381758355326005096961)
    ·
      refine ⟨72368536318766494503822721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96491381758355326005096961 72368536318766494503822721)
      ·
        refine ⟨54276402239074870877867041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72368536318766494503822721 54276402239074870877867041)
        ·
          refine ⟨40707301679306153158400281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54276402239074870877867041 40707301679306153158400281)
          ·
            refine ⟨30530476259479614868800211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40707301679306153158400281 30530476259479614868800211)
            ·
              refine ⟨45795714389219422303200317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30530476259479614868800211 45795714389219422303200317)
              ·
                refine ⟨17173392895957283363700119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45795714389219422303200317 17173392895957283363700119)
                ·
                  refine ⟨25760089343935925045550179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17173392895957283363700119 25760089343935925045550179)
                  ·
                    refine ⟨38640134015903887568325269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25760089343935925045550179 38640134015903887568325269)
                    ·
                      refine ⟨1811256281995494729765247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38640134015903887568325269 1811256281995494729765247)
                      ·
                        rfl

theorem cell23_3527409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3527409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527409 prefixEnd_3527409 := by exact prefixLift 3527409
  have htrace : WordTrace (prefixWord ++ tailWord_3527409) baseStart_3527409 baseEnd_3527409 := by
    simpa [prefixWord, tailWord_3527409, baseEnd_3527409] using wordTrace_append hprefix tailTrace_3527409
  have hstable : (prefixWord ++ tailWord_3527409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527409).length < 2 ^ (prefixWord ++ tailWord_3527409).sum := by decide
  have hdescent : baseEnd_3527409 < baseStart_3527409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527416 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_3527416 : Nat := 118140960795 + 3527416 * 2 ^ 59
def prefixEnd_3527416 : Nat := 4983230072969 + 3 ^ 40 * 3527416 * 2
def baseEnd_3527416 : Nat := 1811259876360076202377715

theorem tailTrace_3527416 : CollatzResearch.WordTrace tailWord_3527416 prefixEnd_3527416 1811259876360076202377715 := by
  unfold tailWord_3527416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64327715494390870767817051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85770287325854494357089401 64327715494390870767817051)
  ·
    refine ⟨96491573241586306151725577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64327715494390870767817051 96491573241586306151725577)
    ·
      refine ⟨72368679931189729613794183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96491573241586306151725577 72368679931189729613794183)
      ·
        refine ⟨108553019896784594420691275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72368679931189729613794183 108553019896784594420691275)
        ·
          refine ⟨162829529845176891631036913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108553019896784594420691275 162829529845176891631036913)
          ·
            refine ⟨122122147383882668723277685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162829529845176891631036913 122122147383882668723277685)
            ·
              refine ⟨11448951317239000192807283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122122147383882668723277685 11448951317239000192807283)
              ·
                refine ⟨17173426975858500289210925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448951317239000192807283 17173426975858500289210925)
                ·
                  refine ⟨6440035115946937608454097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17173426975858500289210925 6440035115946937608454097)
                  ·
                    refine ⟨4830026336960203206340573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440035115946937608454097 4830026336960203206340573)
                    ·
                      refine ⟨1811259876360076202377715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830026336960203206340573 1811259876360076202377715)
                      ·
                        rfl

theorem cell23_3527416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_3527416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527416 prefixEnd_3527416 := by exact prefixLift 3527416
  have htrace : WordTrace (prefixWord ++ tailWord_3527416) baseStart_3527416 baseEnd_3527416 := by
    simpa [prefixWord, tailWord_3527416, baseEnd_3527416] using wordTrace_append hprefix tailTrace_3527416
  have hstable : (prefixWord ++ tailWord_3527416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527416).length < 2 ^ (prefixWord ++ tailWord_3527416).sum := by decide
  have hdescent : baseEnd_3527416 < baseStart_3527416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527459 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3527459 : Nat := 118140960795 + 3527459 * 2 ^ 59
def prefixEnd_3527459 : Nat := 4983230072969 + 3 ^ 40 * 3527459 * 2
def baseEnd_3527459 : Nat := 1811281956028219534140017

theorem tailTrace_3527459 : CollatzResearch.WordTrace tailWord_3527459 prefixEnd_3527459 1811281956028219534140017 := by
  unfold tailWord_3527459
  simp only [CollatzResearch.WordTrace]
  refine ⟨128656999327625959879449431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85771332885083973252966287 128656999327625959879449431)
  ·
    refine ⟨192985498991438939819174147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128656999327625959879449431 192985498991438939819174147)
    ·
      refine ⟨289478248487158409728761221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192985498991438939819174147 289478248487158409728761221)
      ·
        refine ⟨54277171591342201824142729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289478248487158409728761221 54277171591342201824142729)
        ·
          refine ⟨40707878693506651368107047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54277171591342201824142729 40707878693506651368107047)
          ·
            refine ⟨61061818040259977052160571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40707878693506651368107047 61061818040259977052160571)
            ·
              refine ⟨91592727060389965578240857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61061818040259977052160571 91592727060389965578240857)
              ·
                refine ⟨68694545295292474183680643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91592727060389965578240857 68694545295292474183680643)
                ·
                  refine ⟨103041817942938711275520965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68694545295292474183680643 103041817942938711275520965)
                  ·
                    refine ⟨19320340864301008364160181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103041817942938711275520965 19320340864301008364160181)
                    ·
                      refine ⟨1811281956028219534140017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19320340864301008364160181 1811281956028219534140017)
                      ·
                        rfl

theorem cell23_3527459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3527459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527459 prefixEnd_3527459 := by exact prefixLift 3527459
  have htrace : WordTrace (prefixWord ++ tailWord_3527459) baseStart_3527459 baseEnd_3527459 := by
    simpa [prefixWord, tailWord_3527459, baseEnd_3527459] using wordTrace_append hprefix tailTrace_3527459
  have hstable : (prefixWord ++ tailWord_3527459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527459).length < 2 ^ (prefixWord ++ tailWord_3527459).sum := by decide
  have hdescent : baseEnd_3527459 < baseStart_3527459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527473 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_3527473 : Nat := 118140960795 + 3527473 * 2 ^ 59
def prefixEnd_3527473 : Nat := 4983230072969 + 3 ^ 40 * 3527473 * 2
def baseEnd_3527473 : Nat := 1811289144757382479364953

theorem tailTrace_3527473 : CollatzResearch.WordTrace tailWord_3527473 prefixEnd_3527473 1811289144757382479364953 := by
  unfold tailWord_3527473
  simp only [CollatzResearch.WordTrace]
  refine ⟨128657509949575240270459073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85771673299716826846972715 128657509949575240270459073)
  ·
    refine ⟨96493132462181430202844305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128657509949575240270459073 96493132462181430202844305)
    ·
      refine ⟨72369849346636072652133229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96493132462181430202844305 72369849346636072652133229)
      ·
        refine ⟨27138693504988527244549961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72369849346636072652133229 27138693504988527244549961)
        ·
          refine ⟨20354020128741395433412471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27138693504988527244549961 20354020128741395433412471)
          ·
            refine ⟨30531030193112093150118707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354020128741395433412471 30531030193112093150118707)
            ·
              refine ⟨45796545289668139725178061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30531030193112093150118707 45796545289668139725178061)
              ·
                refine ⟨17173704483625552396941773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45796545289668139725178061 17173704483625552396941773)
                ·
                  refine ⟨6440139181359582148853165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17173704483625552396941773 6440139181359582148853165)
                  ·
                    refine ⟨2415052193009843305819937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6440139181359582148853165 2415052193009843305819937)
                    ·
                      refine ⟨1811289144757382479364953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415052193009843305819937 1811289144757382479364953)
                      ·
                        rfl

theorem cell23_3527473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_3527473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527473 prefixEnd_3527473 := by exact prefixLift 3527473
  have htrace : WordTrace (prefixWord ++ tailWord_3527473) baseStart_3527473 baseEnd_3527473 := by
    simpa [prefixWord, tailWord_3527473, baseEnd_3527473] using wordTrace_append hprefix tailTrace_3527473
  have hstable : (prefixWord ++ tailWord_3527473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527473).length < 2 ^ (prefixWord ++ tailWord_3527473).sum := by decide
  have hdescent : baseEnd_3527473 < baseStart_3527473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527479 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3527479 : Nat := 118140960795 + 3527479 * 2 ^ 59
def prefixEnd_3527479 : Nat := 4983230072969 + 3 ^ 40 * 3527479 * 2
def baseEnd_3527479 : Nat := 603764075213769818629975

theorem tailTrace_3527479 : CollatzResearch.WordTrace tailWord_3527479 prefixEnd_3527479 603764075213769818629975 := by
  unfold tailWord_3527479
  simp only [CollatzResearch.WordTrace]
  refine ⟨128657728787553503295177491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85771819191702335530118327 128657728787553503295177491)
  ·
    refine ⟨192986593181330254942766237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128657728787553503295177491 192986593181330254942766237)
    ·
      refine ⟨72369972442998845603537339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192986593181330254942766237 72369972442998845603537339)
      ·
        refine ⟨108554958664498268405306009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72369972442998845603537339 108554958664498268405306009)
        ·
          refine ⟨81416218998373701303979507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108554958664498268405306009 81416218998373701303979507)
          ·
            refine ⟨122124328497560551955969261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81416218998373701303979507 122124328497560551955969261)
            ·
              refine ⟨45796623186585206983488473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122124328497560551955969261 45796623186585206983488473)
              ·
                refine ⟨34347467389938905237616355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45796623186585206983488473 34347467389938905237616355)
                ·
                  refine ⟨51521201084908357856424533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34347467389938905237616355 51521201084908357856424533)
                  ·
                    refine ⟨603764075213769818629975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51521201084908357856424533 603764075213769818629975)
                    ·
                      rfl

theorem cell23_3527479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3527479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527479 prefixEnd_3527479 := by exact prefixLift 3527479
  have htrace : WordTrace (prefixWord ++ tailWord_3527479) baseStart_3527479 baseEnd_3527479 := by
    simpa [prefixWord, tailWord_3527479, baseEnd_3527479] using wordTrace_append hprefix tailTrace_3527479
  have hstable : (prefixWord ++ tailWord_3527479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527479).length < 2 ^ (prefixWord ++ tailWord_3527479).sum := by decide
  have hdescent : baseEnd_3527479 < baseStart_3527479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527536 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_3527536 : Nat := 118140960795 + 3527536 * 2 ^ 59
def prefixEnd_3527536 : Nat := 4983230072969 + 3 ^ 40 * 3527536 * 2
def baseEnd_3527536 : Nat := 1811321494038615732877163

theorem tailTrace_3527536 : CollatzResearch.WordTrace tailWord_3527536 prefixEnd_3527536 1811321494038615732877163 := by
  unfold tailWord_3527536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64329903874173501015001231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85773205165564668020001641 64329903874173501015001231)
  ·
    refine ⟨96494855811260251522501847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64329903874173501015001231 96494855811260251522501847)
    ·
      refine ⟨144742283716890377283752771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96494855811260251522501847 144742283716890377283752771)
      ·
        refine ⟨217113425575335565925629157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144742283716890377283752771 217113425575335565925629157)
        ·
          refine ⟨40708767295375418611055467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217113425575335565925629157 40708767295375418611055467)
          ·
            refine ⟨61063150943063127916583201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40708767295375418611055467 61063150943063127916583201)
            ·
              refine ⟨45797363207297345937437401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61063150943063127916583201 45797363207297345937437401)
              ·
                refine ⟨34348022405473009453078051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45797363207297345937437401 34348022405473009453078051)
                ·
                  refine ⟨51522033608209514179617077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34348022405473009453078051 51522033608209514179617077)
                  ·
                    refine ⟨4830190650769641954339101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51522033608209514179617077 4830190650769641954339101)
                    ·
                      refine ⟨1811321494038615732877163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830190650769641954339101 1811321494038615732877163)
                      ·
                        rfl

theorem cell23_3527536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_3527536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527536 prefixEnd_3527536 := by exact prefixLift 3527536
  have htrace : WordTrace (prefixWord ++ tailWord_3527536) baseStart_3527536 baseEnd_3527536 := by
    simpa [prefixWord, tailWord_3527536, baseEnd_3527536] using wordTrace_append hprefix tailTrace_3527536
  have hstable : (prefixWord ++ tailWord_3527536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527536).length < 2 ^ (prefixWord ++ tailWord_3527536).sum := by decide
  have hdescent : baseEnd_3527536 < baseStart_3527536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527593 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_3527593 : Nat := 118140960795 + 3527593 * 2 ^ 59
def prefixEnd_3527593 : Nat := 4983230072969 + 3 ^ 40 * 3527593 * 2
def baseEnd_3527593 : Nat := 1811350762435922009864401

theorem tailTrace_3527593 : CollatzResearch.WordTrace tailWord_3527593 prefixEnd_3527593 1811350762435922009864401 := by
  unfold tailWord_3527593
  simp only [CollatzResearch.WordTrace]
  refine ⟨128661886709140500764827433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85774591139427000509884955 128661886709140500764827433)
  ·
    refine ⟨96496415031855375573620575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128661886709140500764827433 96496415031855375573620575)
    ·
      refine ⟨144744622547783063360430863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96496415031855375573620575 144744622547783063360430863)
      ·
        refine ⟨217116933821674595040646295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144744622547783063360430863 217116933821674595040646295)
        ·
          refine ⟨325675400732511892560969443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217116933821674595040646295 325675400732511892560969443)
          ·
            refine ⟨488513101098767838841454165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325675400732511892560969443 488513101098767838841454165)
            ·
              refine ⟨5724762903501185611423291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 488513101098767838841454165 5724762903501185611423291)
              ·
                refine ⟨8587144355251778417134937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724762903501185611423291 8587144355251778417134937)
                ·
                  refine ⟨6440358266438833812851203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8587144355251778417134937 6440358266438833812851203)
                  ·
                    refine ⟨9660537399658250719276805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6440358266438833812851203 9660537399658250719276805)
                    ·
                      refine ⟨1811350762435922009864401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9660537399658250719276805 1811350762435922009864401)
                      ·
                        rfl

theorem cell23_3527593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_3527593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527593 prefixEnd_3527593 := by exact prefixLift 3527593
  have htrace : WordTrace (prefixWord ++ tailWord_3527593) baseStart_3527593 baseEnd_3527593 := by
    simpa [prefixWord, tailWord_3527593, baseEnd_3527593] using wordTrace_append hprefix tailTrace_3527593
  have hstable : (prefixWord ++ tailWord_3527593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527593).length < 2 ^ (prefixWord ++ tailWord_3527593).sum := by decide
  have hdescent : baseEnd_3527593 < baseStart_3527593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527647 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_3527647 : Nat := 118140960795 + 3527647 * 2 ^ 59
def prefixEnd_3527647 : Nat := 4983230072969 + 3 ^ 40 * 3527647 * 2
def baseEnd_3527647 : Nat := 1811378490391264798589153

theorem tailTrace_3527647 : CollatzResearch.WordTrace tailWord_3527647 prefixEnd_3527647 1811378490391264798589153 := by
  unfold tailWord_3527647
  simp only [CollatzResearch.WordTrace]
  refine ⟨128663856250944867987293195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85775904167296578658195463 128663856250944867987293195)
  ·
    refine ⟨192995784376417301980939793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128663856250944867987293195 192995784376417301980939793)
    ·
      refine ⟨144746838282312976485704845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192995784376417301980939793 144746838282312976485704845)
      ·
        refine ⟨54280064355867366182139317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144746838282312976485704845 54280064355867366182139317)
        ·
          refine ⟨5088756033362565579575561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54280064355867366182139317 5088756033362565579575561)
          ·
            refine ⟨3816567025021924184681671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5088756033362565579575561 3816567025021924184681671)
            ·
              refine ⟨5724850537532886277022507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816567025021924184681671 5724850537532886277022507)
              ·
                refine ⟨8587275806299329415533761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724850537532886277022507 8587275806299329415533761)
                ·
                  refine ⟨6440456854724497061650321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8587275806299329415533761 6440456854724497061650321)
                  ·
                    refine ⟨4830342641043372796237741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440456854724497061650321 4830342641043372796237741)
                    ·
                      refine ⟨1811378490391264798589153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830342641043372796237741 1811378490391264798589153)
                      ·
                        rfl

theorem cell23_3527647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_3527647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527647 prefixEnd_3527647 := by exact prefixLift 3527647
  have htrace : WordTrace (prefixWord ++ tailWord_3527647) baseStart_3527647 baseEnd_3527647 := by
    simpa [prefixWord, tailWord_3527647, baseEnd_3527647] using wordTrace_append hprefix tailTrace_3527647
  have hstable : (prefixWord ++ tailWord_3527647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527647).length < 2 ^ (prefixWord ++ tailWord_3527647).sum := by decide
  have hdescent : baseEnd_3527647 < baseStart_3527647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527777 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_3527777 : Nat := 118140960795 + 3527777 * 2 ^ 59
def prefixEnd_3527777 : Nat := 4983230072969 + 3 ^ 40 * 3527777 * 2
def baseEnd_3527777 : Nat := 1811445242876349289963555

theorem tailTrace_3527777 : CollatzResearch.WordTrace tailWord_3527777 prefixEnd_3527777 1811445242876349289963555 := by
  unfold tailWord_3527777
  simp only [CollatzResearch.WordTrace]
  refine ⟨128668597740473900189525585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85779065160315933459683723 128668597740473900189525585)
  ·
    refine ⟨96501448305355425142144189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128668597740473900189525585 96501448305355425142144189)
    ·
      refine ⟨36188043114508284428304071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96501448305355425142144189 36188043114508284428304071)
      ·
        refine ⟨54282064671762426642456107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36188043114508284428304071 54282064671762426642456107)
        ·
          refine ⟨81423097007643639963684161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54282064671762426642456107 81423097007643639963684161)
          ·
            refine ⟨61067322755732729972763121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81423097007643639963684161 61067322755732729972763121)
            ·
              refine ⟨45800492066799547479572341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61067322755732729972763121 45800492066799547479572341)
              ·
                refine ⟨4293796131262457576209907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45800492066799547479572341 4293796131262457576209907)
                ·
                  refine ⟨6440694196893686364314861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293796131262457576209907 6440694196893686364314861)
                  ·
                    refine ⟨2415260323835132386618073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6440694196893686364314861 2415260323835132386618073)
                    ·
                      refine ⟨1811445242876349289963555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415260323835132386618073 1811445242876349289963555)
                      ·
                        rfl

theorem cell23_3527777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_3527777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527777 prefixEnd_3527777 := by exact prefixLift 3527777
  have htrace : WordTrace (prefixWord ++ tailWord_3527777) baseStart_3527777 baseEnd_3527777 := by
    simpa [prefixWord, tailWord_3527777, baseEnd_3527777] using wordTrace_append hprefix tailTrace_3527777
  have hstable : (prefixWord ++ tailWord_3527777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527777).length < 2 ^ (prefixWord ++ tailWord_3527777).sum := by decide
  have hdescent : baseEnd_3527777 < baseStart_3527777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527790 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3527790 : Nat := 118140960795 + 3527790 * 2 ^ 59
def prefixEnd_3527790 : Nat := 4983230072969 + 3 ^ 40 * 3527790 * 2
def baseEnd_3527790 : Nat := 1811451918124857739100995

theorem tailTrace_3527790 : CollatzResearch.WordTrace tailWord_3527790 prefixEnd_3527790 1811451918124857739100995 := by
  unfold tailWord_3527790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16083633986178350426218603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85779381259617868939832549 16083633986178350426218603)
  ·
    refine ⟨24125450979267525639327905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16083633986178350426218603 24125450979267525639327905)
    ·
      refine ⟨18094088234450644229495929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24125450979267525639327905 18094088234450644229495929)
      ·
        refine ⟨13570566175837983172121947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18094088234450644229495929 13570566175837983172121947)
        ·
          refine ⟨20355849263756974758182921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13570566175837983172121947 20355849263756974758182921)
          ·
            refine ⟨15266886947817731068637191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20355849263756974758182921 15266886947817731068637191)
            ·
              refine ⟨22900330421726596602955787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266886947817731068637191 22900330421726596602955787)
              ·
                refine ⟨34350495632589894904433681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22900330421726596602955787 34350495632589894904433681)
                ·
                  refine ⟨25762871724442421178325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34350495632589894904433681 25762871724442421178325261)
                  ·
                    refine ⟨9661076896665907941871973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25762871724442421178325261 9661076896665907941871973)
                    ·
                      refine ⟨1811451918124857739100995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9661076896665907941871973 1811451918124857739100995)
                      ·
                        rfl

theorem cell23_3527790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3527790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527790 prefixEnd_3527790 := by exact prefixLift 3527790
  have htrace : WordTrace (prefixWord ++ tailWord_3527790) baseStart_3527790 baseEnd_3527790 := by
    simpa [prefixWord, tailWord_3527790, baseEnd_3527790] using wordTrace_append hprefix tailTrace_3527790
  have hstable : (prefixWord ++ tailWord_3527790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527790).length < 2 ^ (prefixWord ++ tailWord_3527790).sum := by decide
  have hdescent : baseEnd_3527790 < baseStart_3527790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3527793 : Nat := 118140960795 + 3527793 * 2 ^ 59
def prefixEnd_3527793 : Nat := 4983230072969 + 3 ^ 40 * 3527793 * 2
def baseEnd_3527793 : Nat := 1811453458566821227363481

theorem tailTrace_3527793 : CollatzResearch.WordTrace tailWord_3527793 prefixEnd_3527793 1811453458566821227363481 := by
  unfold tailWord_3527793
  simp only [CollatzResearch.WordTrace]
  refine ⟨128669181308415934922108033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85779454205610623281405355 128669181308415934922108033)
  ·
    refine ⟨96501885981311951191581025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128669181308415934922108033 96501885981311951191581025)
    ·
      refine ⟨72376414485983963393685769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96501885981311951191581025 72376414485983963393685769)
      ·
        refine ⟨54282310864487972545264327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72376414485983963393685769 54282310864487972545264327)
        ·
          refine ⟨81423466296731958817896491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54282310864487972545264327 81423466296731958817896491)
          ·
            refine ⟨122135199445097938226844737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81423466296731958817896491 122135199445097938226844737)
            ·
              refine ⟨91601399583823453670133553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122135199445097938226844737 91601399583823453670133553)
              ·
                refine ⟨68701049687867590252600165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91601399583823453670133553 68701049687867590252600165)
                ·
                  refine ⟨12881446816475173172362531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68701049687867590252600165 12881446816475173172362531)
                  ·
                    refine ⟨19322170224712759758543797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12881446816475173172362531 19322170224712759758543797)
                    ·
                      refine ⟨1811453458566821227363481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19322170224712759758543797 1811453458566821227363481)
                      ·
                        rfl

theorem cell23_3527793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3527793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527793 prefixEnd_3527793 := by exact prefixLift 3527793
  have htrace : WordTrace (prefixWord ++ tailWord_3527793) baseStart_3527793 baseEnd_3527793 := by
    simpa [prefixWord, tailWord_3527793, baseEnd_3527793] using wordTrace_append hprefix tailTrace_3527793
  have hstable : (prefixWord ++ tailWord_3527793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527793).length < 2 ^ (prefixWord ++ tailWord_3527793).sum := by decide
  have hdescent : baseEnd_3527793 < baseStart_3527793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527840 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3527840 : Nat := 118140960795 + 3527840 * 2 ^ 59
def prefixEnd_3527840 : Nat := 4983230072969 + 3 ^ 40 * 3527840 * 2
def baseEnd_3527840 : Nat := 1811477592157582543475765

theorem tailTrace_3527840 : CollatzResearch.WordTrace tailWord_3527840 prefixEnd_3527840 1811477592157582543475765 := by
  unfold tailWord_3527840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64335447769622830974534487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85780597026163774632712649 64335447769622830974534487)
  ·
    refine ⟨96503171654434246461801731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64335447769622830974534487 96503171654434246461801731)
    ·
      refine ⟨144754757481651369692702597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96503171654434246461801731 144754757481651369692702597)
      ·
        refine ⟨27141517027809631817381737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144754757481651369692702597 27141517027809631817381737)
        ·
          refine ⟨20356137770857223863036303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27141517027809631817381737 20356137770857223863036303)
          ·
            refine ⟨30534206656285835794554455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20356137770857223863036303 30534206656285835794554455)
            ·
              refine ⟨45801309984428753691831683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30534206656285835794554455 45801309984428753691831683)
              ·
                refine ⟨68701964976643130537747525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45801309984428753691831683 68701964976643130537747525)
                ·
                  refine ⟨12881618433120586975827661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68701964976643130537747525 12881618433120586975827661)
                  ·
                    refine ⟨4830606912420220115935373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881618433120586975827661 4830606912420220115935373)
                    ·
                      refine ⟨1811477592157582543475765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830606912420220115935373 1811477592157582543475765)
                      ·
                        rfl

theorem cell23_3527840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3527840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527840 prefixEnd_3527840 := by exact prefixLift 3527840
  have htrace : WordTrace (prefixWord ++ tailWord_3527840) baseStart_3527840 baseEnd_3527840 := by
    simpa [prefixWord, tailWord_3527840, baseEnd_3527840] using wordTrace_append hprefix tailTrace_3527840
  have hstable : (prefixWord ++ tailWord_3527840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527840).length < 2 ^ (prefixWord ++ tailWord_3527840).sum := by decide
  have hdescent : baseEnd_3527840 < baseStart_3527840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527847 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 7]
def baseStart_3527847 : Nat := 118140960795 + 3527847 * 2 ^ 59
def prefixEnd_3527847 : Nat := 4983230072969 + 3 ^ 40 * 3527847 * 2
def baseEnd_3527847 : Nat := 201275687391351557343137

theorem tailTrace_3527847 : CollatzResearch.WordTrace tailWord_3527847 prefixEnd_3527847 201275687391351557343137 := by
  unfold tailWord_3527847
  simp only [CollatzResearch.WordTrace]
  refine ⟨128671150850220302144573795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85780767233480201429715863 128671150850220302144573795)
  ·
    refine ⟨193006726275330453216860693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128671150850220302144573795 193006726275330453216860693)
    ·
      refine ⟨9047190294156114994540345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193006726275330453216860693 9047190294156114994540345)
      ·
        refine ⟨6785392720617086245905259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9047190294156114994540345 6785392720617086245905259)
        ·
          refine ⟨10178089080925629368857889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785392720617086245905259 10178089080925629368857889)
          ·
            refine ⟨7633566810694222026643417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10178089080925629368857889 7633566810694222026643417)
            ·
              refine ⟨5725175108020666519982563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7633566810694222026643417 5725175108020666519982563)
              ·
                refine ⟨8587762662030999779973845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5725175108020666519982563 8587762662030999779973845)
                ·
                  refine ⟨201275687391351557343137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8587762662030999779973845 201275687391351557343137)
                  ·
                    rfl

theorem cell23_3527847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 7].length) (baseStart_3527847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527847 prefixEnd_3527847 := by exact prefixLift 3527847
  have htrace : WordTrace (prefixWord ++ tailWord_3527847) baseStart_3527847 baseEnd_3527847 := by
    simpa [prefixWord, tailWord_3527847, baseEnd_3527847] using wordTrace_append hprefix tailTrace_3527847
  have hstable : (prefixWord ++ tailWord_3527847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527847).length < 2 ^ (prefixWord ++ tailWord_3527847).sum := by decide
  have hdescent : baseEnd_3527847 < baseStart_3527847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527857 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3527857 : Nat := 118140960795 + 3527857 * 2 ^ 59
def prefixEnd_3527857 : Nat := 4983230072969 + 3 ^ 40 * 3527857 * 2
def baseEnd_3527857 : Nat := 1811486321328708976963187

theorem tailTrace_3527857 : CollatzResearch.WordTrace tailWord_3527857 prefixEnd_3527857 1811486321328708976963187 := by
  unfold tailWord_3527857
  simp only [CollatzResearch.WordTrace]
  refine ⟨128671515580184073852437825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85781010386789382568291883 128671515580184073852437825)
  ·
    refine ⟨96503636685138055389328369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128671515580184073852437825 96503636685138055389328369)
    ·
      refine ⟨72377727513853541541996277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96503636685138055389328369 72377727513853541541996277)
      ·
        refine ⟨6785411954423769519562151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72377727513853541541996277 6785411954423769519562151)
        ·
          refine ⟨10178117931635654279343227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785411954423769519562151 10178117931635654279343227)
          ·
            refine ⟨15267176897453481419014841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178117931635654279343227 15267176897453481419014841)
            ·
              refine ⟨11450382673090111064261131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15267176897453481419014841 11450382673090111064261131)
              ·
                refine ⟨17175574009635166596391697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450382673090111064261131 17175574009635166596391697)
                ·
                  refine ⟨12881680507226374947293773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17175574009635166596391697 12881680507226374947293773)
                  ·
                    refine ⟨4830630190209890605235165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881680507226374947293773 4830630190209890605235165)
                    ·
                      refine ⟨1811486321328708976963187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830630190209890605235165 1811486321328708976963187)
                      ·
                        rfl

theorem cell23_3527857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3527857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527857 prefixEnd_3527857 := by exact prefixLift 3527857
  have htrace : WordTrace (prefixWord ++ tailWord_3527857) baseStart_3527857 baseEnd_3527857 := by
    simpa [prefixWord, tailWord_3527857, baseEnd_3527857] using wordTrace_append hprefix tailTrace_3527857
  have hstable : (prefixWord ++ tailWord_3527857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527857).length < 2 ^ (prefixWord ++ tailWord_3527857).sum := by decide
  have hdescent : baseEnd_3527857 < baseStart_3527857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527880 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3527880 : Nat := 118140960795 + 3527880 * 2 ^ 59
def prefixEnd_3527880 : Nat := 4983230072969 + 3 ^ 40 * 3527880 * 2
def baseEnd_3527880 : Nat := 1811498131383762386975581

theorem tailTrace_3527880 : CollatzResearch.WordTrace tailWord_3527880 prefixEnd_3527880 1811498131383762386975581 := by
  unfold tailWord_3527880
  simp only [CollatzResearch.WordTrace]
  refine ⟨64336177229550374390262547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85781569639400499187016729 64336177229550374390262547)
  ·
    refine ⟨96504265844325561585393821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64336177229550374390262547 96504265844325561585393821)
    ·
      refine ⟨36189099691622085594522683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96504265844325561585393821 36189099691622085594522683)
      ·
        refine ⟨54283649537433128391784025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36189099691622085594522683 54283649537433128391784025)
        ·
          refine ⟨40712737153074846293838019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54283649537433128391784025 40712737153074846293838019)
          ·
            refine ⟨61069105729612269440757029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40712737153074846293838019 61069105729612269440757029)
            ·
              refine ⟨11450457324302300520141943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61069105729612269440757029 11450457324302300520141943)
              ·
                refine ⟨17175685986453450780212915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450457324302300520141943 17175685986453450780212915)
                ·
                  refine ⟨25763528979680176170319373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17175685986453450780212915 25763528979680176170319373)
                  ·
                    refine ⟨9661323367380066063869765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25763528979680176170319373 9661323367380066063869765)
                    ·
                      refine ⟨1811498131383762386975581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9661323367380066063869765 1811498131383762386975581)
                      ·
                        rfl

theorem cell23_3527880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3527880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527880 prefixEnd_3527880 := by exact prefixLift 3527880
  have htrace : WordTrace (prefixWord ++ tailWord_3527880) baseStart_3527880 baseEnd_3527880 := by
    simpa [prefixWord, tailWord_3527880, baseEnd_3527880] using wordTrace_append hprefix tailTrace_3527880
  have hstable : (prefixWord ++ tailWord_3527880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527880).length < 2 ^ (prefixWord ++ tailWord_3527880).sum := by decide
  have hdescent : baseEnd_3527880 < baseStart_3527880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527934 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3527934 : Nat := 118140960795 + 3527934 * 2 ^ 59
def prefixEnd_3527934 : Nat := 4983230072969 + 3 ^ 40 * 3527934 * 2
def baseEnd_3527934 : Nat := 1811525859339105175700333

theorem tailTrace_3527934 : CollatzResearch.WordTrace tailWord_3527934 prefixEnd_3527934 1811525859339105175700333 := by
  unfold tailWord_3527934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084290500113139500373857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85782882667270077335327237 16084290500113139500373857)
  ·
    refine ⟨12063217875084854625280393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16084290500113139500373857 12063217875084854625280393)
    ·
      refine ⟨9047413406313640968960295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12063217875084854625280393 9047413406313640968960295)
      ·
        refine ⟨13571120109470461453440443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047413406313640968960295 13571120109470461453440443)
        ·
          refine ⟨20356680164205692180160665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571120109470461453440443 20356680164205692180160665)
          ·
            refine ⟨15267510123154269135120499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20356680164205692180160665 15267510123154269135120499)
            ·
              refine ⟨22901265184731403702680749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267510123154269135120499 22901265184731403702680749)
              ·
                refine ⟨8587974444274276388505281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22901265184731403702680749 8587974444274276388505281)
                ·
                  refine ⟨6440980833205707291378961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8587974444274276388505281 6440980833205707291378961)
                  ·
                    refine ⟨4830735624904280468534221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440980833205707291378961 4830735624904280468534221)
                    ·
                      refine ⟨1811525859339105175700333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830735624904280468534221 1811525859339105175700333)
                      ·
                        rfl

theorem cell23_3527934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3527934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527934 prefixEnd_3527934 := by exact prefixLift 3527934
  have htrace : WordTrace (prefixWord ++ tailWord_3527934) baseStart_3527934 baseEnd_3527934 := by
    simpa [prefixWord, tailWord_3527934, baseEnd_3527934] using wordTrace_append hprefix tailTrace_3527934
  have hstable : (prefixWord ++ tailWord_3527934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527934).length < 2 ^ (prefixWord ++ tailWord_3527934).sum := by decide
  have hdescent : baseEnd_3527934 < baseStart_3527934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527957 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_3527957 : Nat := 118140960795 + 3527957 * 2 ^ 59
def prefixEnd_3527957 : Nat := 4983230072969 + 3 ^ 40 * 3527957 * 2
def baseEnd_3527957 : Nat := 1811537669394158585712727

theorem tailTrace_3527957 : CollatzResearch.WordTrace tailWord_3527957 prefixEnd_3527957 1811537669394158585712727 := by
  unfold tailWord_3527957
  simp only [CollatzResearch.WordTrace]
  refine ⟨128675162879821790931078125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85783441919881193954052083 128675162879821790931078125)
  ·
    refine ⟨48253186079933171599154297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128675162879821790931078125 48253186079933171599154297)
    ·
      refine ⟨36189889559949878699365723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48253186079933171599154297 36189889559949878699365723)
      ·
        refine ⟨54284834339924818049048585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36189889559949878699365723 54284834339924818049048585)
        ·
          refine ⟨40713625754943613536786439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54284834339924818049048585 40713625754943613536786439)
          ·
            refine ⟨61070438632415420305179659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40713625754943613536786439 61070438632415420305179659)
            ·
              refine ⟨91605657948623130457769489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61070438632415420305179659 91605657948623130457769489)
              ·
                refine ⟨68704243461467347843327117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91605657948623130457769489 68704243461467347843327117)
                ·
                  refine ⟨25764091298050255441247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68704243461467347843327117 25764091298050255441247669)
                  ·
                    refine ⟨2415383559192211447616969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25764091298050255441247669 2415383559192211447616969)
                    ·
                      refine ⟨1811537669394158585712727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415383559192211447616969 1811537669394158585712727)
                      ·
                        rfl

theorem cell23_3527957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_3527957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527957 prefixEnd_3527957 := by exact prefixLift 3527957
  have htrace : WordTrace (prefixWord ++ tailWord_3527957) baseStart_3527957 baseEnd_3527957 := by
    simpa [prefixWord, tailWord_3527957, baseEnd_3527957] using wordTrace_append hprefix tailTrace_3527957
  have hstable : (prefixWord ++ tailWord_3527957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527957).length < 2 ^ (prefixWord ++ tailWord_3527957).sum := by decide
  have hdescent : baseEnd_3527957 < baseStart_3527957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527981 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3527981 : Nat := 118140960795 + 3527981 * 2 ^ 59
def prefixEnd_3527981 : Nat := 4983230072969 + 3 ^ 40 * 3527981 * 2
def baseEnd_3527981 : Nat := 1811549992929866491812617

theorem tailTrace_3527981 : CollatzResearch.WordTrace tailWord_3527981 prefixEnd_3527981 1811549992929866491812617 := by
  unfold tailWord_3527981
  simp only [CollatzResearch.WordTrace]
  refine ⟨128676038231734843029951797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85784025487823228686634531 128676038231734843029951797)
  ·
    refine ⟨12063378584225141534057981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128676038231734843029951797 12063378584225141534057981)
    ·
      refine ⟨4523766969084428075271743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12063378584225141534057981 4523766969084428075271743)
      ·
        refine ⟨6785650453626642112907615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523766969084428075271743 6785650453626642112907615)
        ·
          refine ⟨10178475680439963169361423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785650453626642112907615 10178475680439963169361423)
          ·
            refine ⟨15267713520659944754042135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178475680439963169361423 15267713520659944754042135)
            ·
              refine ⟨22901570280989917131063203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267713520659944754042135 22901570280989917131063203)
              ·
                refine ⟨34352355421484875696594805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22901570280989917131063203 34352355421484875696594805)
                ·
                  refine ⟨3220533320764207096555763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34352355421484875696594805 3220533320764207096555763)
                  ·
                    refine ⟨4830799981146310644833645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220533320764207096555763 4830799981146310644833645)
                    ·
                      refine ⟨1811549992929866491812617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830799981146310644833645 1811549992929866491812617)
                      ·
                        rfl

theorem cell23_3527981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3527981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527981 prefixEnd_3527981 := by exact prefixLift 3527981
  have htrace : WordTrace (prefixWord ++ tailWord_3527981) baseStart_3527981 baseEnd_3527981 := by
    simpa [prefixWord, tailWord_3527981, baseEnd_3527981] using wordTrace_append hprefix tailTrace_3527981
  have hstable : (prefixWord ++ tailWord_3527981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527981).length < 2 ^ (prefixWord ++ tailWord_3527981).sum := by decide
  have hdescent : baseEnd_3527981 < baseStart_3527981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527987 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4]
def baseStart_3527987 : Nat := 118140960795 + 3527987 * 2 ^ 59
def prefixEnd_3527987 : Nat := 4983230072969 + 3 ^ 40 * 3527987 * 2
def baseEnd_3527987 : Nat := 1811553073813793468337589

theorem tailTrace_3527987 : CollatzResearch.WordTrace tailWord_3527987 prefixEnd_3527987 1811553073813793468337589 := by
  unfold tailWord_3527987
  simp only [CollatzResearch.WordTrace]
  refine ⟨128676257069713106054670215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85784171379808737369780143 128676257069713106054670215)
  ·
    refine ⟨193014385604569659082005323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128676257069713106054670215 193014385604569659082005323)
    ·
      refine ⟨289521578406854488623007985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193014385604569659082005323 289521578406854488623007985)
      ·
        refine ⟨217141183805140866467255989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289521578406854488623007985 217141183805140866467255989)
        ·
          refine ⟨20356985981731956231305249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217141183805140866467255989 20356985981731956231305249)
          ·
            refine ⟨15267739486298967173478937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20356985981731956231305249 15267739486298967173478937)
            ·
              refine ⟨11450804614724225380109203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15267739486298967173478937 11450804614724225380109203)
              ·
                refine ⟨17176206922086338070163805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450804614724225380109203 17176206922086338070163805)
                ·
                  refine ⟨6441077595782376776311427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17176206922086338070163805 6441077595782376776311427)
                  ·
                    refine ⟨9661616393673565164467141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6441077595782376776311427 9661616393673565164467141)
                    ·
                      refine ⟨1811553073813793468337589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9661616393673565164467141 1811553073813793468337589)
                      ·
                        rfl

theorem cell23_3527987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_3527987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527987 prefixEnd_3527987 := by exact prefixLift 3527987
  have htrace : WordTrace (prefixWord ++ tailWord_3527987) baseStart_3527987 baseEnd_3527987 := by
    simpa [prefixWord, tailWord_3527987, baseEnd_3527987] using wordTrace_append hprefix tailTrace_3527987
  have hstable : (prefixWord ++ tailWord_3527987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527987).length < 2 ^ (prefixWord ++ tailWord_3527987).sum := by decide
  have hdescent : baseEnd_3527987 < baseStart_3527987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527998 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_3527998 : Nat := 118140960795 + 3527998 * 2 ^ 59
def prefixEnd_3527998 : Nat := 4983230072969 + 3 ^ 40 * 3527998 * 2
def baseEnd_3527998 : Nat := 1811558722100992925300039

theorem tailTrace_3527998 : CollatzResearch.WordTrace tailWord_3527998 prefixEnd_3527998 1811558722100992925300039 := by
  unfold tailWord_3527998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084582284084156866665081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85784438848448836622213765 16084582284084156866665081)
  ·
    refine ⟨12063436713063117649998811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16084582284084156866665081 12063436713063117649998811)
    ·
      refine ⟨18095155069594676474998217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063436713063117649998811 18095155069594676474998217)
      ·
        refine ⟨13571366302196007356248663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18095155069594676474998217 13571366302196007356248663)
        ·
          refine ⟨20357049453294011034372995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571366302196007356248663 20357049453294011034372995)
          ·
            refine ⟨30535574179941016551559493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357049453294011034372995 30535574179941016551559493)
            ·
              refine ⟨5725420158738940603417405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30535574179941016551559493 5725420158738940603417405)
              ·
                refine ⟨2147032559527102726281527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5725420158738940603417405 2147032559527102726281527)
                ·
                  refine ⟨3220548839290654089422291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147032559527102726281527 3220548839290654089422291)
                  ·
                    refine ⟨4830823258935981134133437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220548839290654089422291 4830823258935981134133437)
                    ·
                      refine ⟨1811558722100992925300039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830823258935981134133437 1811558722100992925300039)
                      ·
                        rfl

theorem cell23_3527998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_3527998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3527998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3527998 prefixEnd_3527998 := by exact prefixLift 3527998
  have htrace : WordTrace (prefixWord ++ tailWord_3527998) baseStart_3527998 baseEnd_3527998 := by
    simpa [prefixWord, tailWord_3527998, baseEnd_3527998] using wordTrace_append hprefix tailTrace_3527998
  have hstable : (prefixWord ++ tailWord_3527998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527998).length < 2 ^ (prefixWord ++ tailWord_3527998).sum := by decide
  have hdescent : baseEnd_3527998 < baseStart_3527998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528001 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3528001 : Nat := 118140960795 + 3528001 * 2 ^ 59
def prefixEnd_3528001 : Nat := 4983230072969 + 3 ^ 40 * 3528001 * 2
def baseEnd_3528001 : Nat := 603853420847652137854175

theorem tailTrace_3528001 : CollatzResearch.WordTrace tailWord_3528001 prefixEnd_3528001 603853420847652137854175 := by
  unfold tailWord_3528001
  simp only [CollatzResearch.WordTrace]
  refine ⟨128676767691662386445679857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85784511794441590963786571 128676767691662386445679857)
  ·
    refine ⟨96507575768746789834259893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128676767691662386445679857 96507575768746789834259893)
    ·
      refine ⟨9047585228320011546961865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96507575768746789834259893 9047585228320011546961865)
      ·
        refine ⟨6785688921240008660221399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9047585228320011546961865 6785688921240008660221399)
        ·
          refine ⟨10178533381860012990332099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785688921240008660221399 10178533381860012990332099)
          ·
            refine ⟨15267800072790019485498149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178533381860012990332099 15267800072790019485498149)
            ·
              refine ⟨2862712513648128653530903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15267800072790019485498149 2862712513648128653530903)
              ·
                refine ⟨4294068770472192980296355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862712513648128653530903 4294068770472192980296355)
                ·
                  refine ⟨6441103155708289470444533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294068770472192980296355 6441103155708289470444533)
                  ·
                    refine ⟨603853420847652137854175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6441103155708289470444533 603853420847652137854175)
                    ·
                      rfl

theorem cell23_3528001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3528001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528001 prefixEnd_3528001 := by exact prefixLift 3528001
  have htrace : WordTrace (prefixWord ++ tailWord_3528001) baseStart_3528001 baseEnd_3528001 := by
    simpa [prefixWord, tailWord_3528001, baseEnd_3528001] using wordTrace_append hprefix tailTrace_3528001
  have hstable : (prefixWord ++ tailWord_3528001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528001).length < 2 ^ (prefixWord ++ tailWord_3528001).sum := by decide
  have hdescent : baseEnd_3528001 < baseStart_3528001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528021 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3528021 : Nat := 118140960795 + 3528021 * 2 ^ 59
def prefixEnd_3528021 : Nat := 4983230072969 + 3 ^ 40 * 3528021 * 2
def baseEnd_3528021 : Nat := 1811570532156046335312433

theorem tailTrace_3528021 : CollatzResearch.WordTrace tailWord_3528021 prefixEnd_3528021 1811570532156046335312433 := by
  unfold tailWord_3528021
  simp only [CollatzResearch.WordTrace]
  refine ⟨128677497151589929861407917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85784998101059953240938611 128677497151589929861407917)
  ·
    refine ⟨48254061431846223698027969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128677497151589929861407917 48254061431846223698027969)
    ·
      refine ⟨36190546073884667773520977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48254061431846223698027969 36190546073884667773520977)
      ·
        refine ⟨27142909555413500830140733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36190546073884667773520977 27142909555413500830140733)
        ·
          refine ⟨10178591083280062811302775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27142909555413500830140733 10178591083280062811302775)
          ·
            refine ⟨15267886624920094216954163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178591083280062811302775 15267886624920094216954163)
            ·
              refine ⟨22901829937380141325431245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267886624920094216954163 22901829937380141325431245)
              ·
                refine ⟨8588186226517552997036717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22901829937380141325431245 8588186226517552997036717)
                ·
                  refine ⟨3220569834944082373888769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8588186226517552997036717 3220569834944082373888769)
                  ·
                    refine ⟨2415427376208061780416577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220569834944082373888769 2415427376208061780416577)
                    ·
                      refine ⟨1811570532156046335312433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415427376208061780416577 1811570532156046335312433)
                      ·
                        rfl

theorem cell23_3528021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3528021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528021 prefixEnd_3528021 := by exact prefixLift 3528021
  have htrace : WordTrace (prefixWord ++ tailWord_3528021) baseStart_3528021 baseEnd_3528021 := by
    simpa [prefixWord, tailWord_3528021, baseEnd_3528021] using wordTrace_append hprefix tailTrace_3528021
  have hstable : (prefixWord ++ tailWord_3528021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528021).length < 2 ^ (prefixWord ++ tailWord_3528021).sum := by decide
  have hdescent : baseEnd_3528021 < baseStart_3528021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528044 : List Nat := [2, 2, 1, 1, 5, 3, 2, 7]
def baseStart_3528044 : Nat := 118140960795 + 3528044 * 2 ^ 59
def prefixEnd_3528044 : Nat := 4983230072969 + 3 ^ 40 * 3528044 * 2
def baseEnd_3528044 : Nat := 67095642304114805382401

theorem tailTrace_3528044 : CollatzResearch.WordTrace tailWord_3528044 prefixEnd_3528044 67095642304114805382401 := by
  unfold tailWord_3528044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64339168015253302394747593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85785557353671069859663457 64339168015253302394747593)
  ·
    refine ⟨48254376011439976796060695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64339168015253302394747593 48254376011439976796060695)
    ·
      refine ⟨72381564017159965194091043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48254376011439976796060695 72381564017159965194091043)
      ·
        refine ⟨108572346025739947791136565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72381564017159965194091043 108572346025739947791136565)
        ·
          refine ⟨10178657439913120105419053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108572346025739947791136565 10178657439913120105419053)
          ·
            refine ⟨3816996539967420039532145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10178657439913120105419053 3816996539967420039532145)
            ·
              refine ⟨2862747404975565029649109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3816996539967420039532145 2862747404975565029649109)
              ·
                refine ⟨67095642304114805382401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2862747404975565029649109 67095642304114805382401)
                ·
                  rfl

theorem cell23_3528044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 7].length) (baseStart_3528044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528044 prefixEnd_3528044 := by exact prefixLift 3528044
  have htrace : WordTrace (prefixWord ++ tailWord_3528044) baseStart_3528044 baseEnd_3528044 := by
    simpa [prefixWord, tailWord_3528044, baseEnd_3528044] using wordTrace_append hprefix tailTrace_3528044
  have hstable : (prefixWord ++ tailWord_3528044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528044).length < 2 ^ (prefixWord ++ tailWord_3528044).sum := by decide
  have hdescent : baseEnd_3528044 < baseStart_3528044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528082 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3528082 : Nat := 118140960795 + 3528082 * 2 ^ 59
def prefixEnd_3528082 : Nat := 4983230072969 + 3 ^ 40 * 3528082 * 2
def baseEnd_3528082 : Nat := 603867284825323532216551

theorem tailTrace_3528082 : CollatzResearch.WordTrace tailWord_3528082 prefixEnd_3528082 603867284825323532216551 := by
  unfold tailWord_3528082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169930501092234319844625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85786481336245958186252333 32169930501092234319844625)
  ·
    refine ⟨24127447875819175739883469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32169930501092234319844625 24127447875819175739883469)
    ·
      refine ⟨9047792953432190902456301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24127447875819175739883469 9047792953432190902456301)
      ·
        refine ⟨3392922357537071588421113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9047792953432190902456301 3392922357537071588421113)
        ·
          refine ⟨2544691768152803691315835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3392922357537071588421113 2544691768152803691315835)
          ·
            refine ⟨3817037652229205536973753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544691768152803691315835 3817037652229205536973753)
            ·
              refine ⟨2862778239171904152730315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817037652229205536973753 2862778239171904152730315)
              ·
                refine ⟨4294167358757856229095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862778239171904152730315 4294167358757856229095473)
                ·
                  refine ⟨3220625519068392171821605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294167358757856229095473 3220625519068392171821605)
                  ·
                    refine ⟨603867284825323532216551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220625519068392171821605 603867284825323532216551)
                    ·
                      rfl

theorem cell23_3528082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3528082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528082 prefixEnd_3528082 := by exact prefixLift 3528082
  have htrace : WordTrace (prefixWord ++ tailWord_3528082) baseStart_3528082 baseEnd_3528082 := by
    simpa [prefixWord, tailWord_3528082, baseEnd_3528082] using wordTrace_append hprefix tailTrace_3528082
  have hstable : (prefixWord ++ tailWord_3528082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528082).length < 2 ^ (prefixWord ++ tailWord_3528082).sum := by decide
  have hdescent : baseEnd_3528082 < baseStart_3528082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528088 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3528088 : Nat := 118140960795 + 3528088 * 2 ^ 59
def prefixEnd_3528088 : Nat := 4983230072969 + 3 ^ 40 * 3528088 * 2
def baseEnd_3528088 : Nat := 1811604935359897573174625

theorem tailTrace_3528088 : CollatzResearch.WordTrace tailWord_3528088 prefixEnd_3528088 1811604935359897573174625 := by
  unfold tailWord_3528088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64339970421173600152048459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85786627228231466869397945 64339970421173600152048459)
  ·
    refine ⟨96509955631760400228072689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64339970421173600152048459 96509955631760400228072689)
    ·
      refine ⟨72382466723820300171054517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96509955631760400228072689 72382466723820300171054517)
      ·
        refine ⟨6785856255358153141036361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72382466723820300171054517 6785856255358153141036361)
        ·
          refine ⟨5089392191518614855777271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785856255358153141036361 5089392191518614855777271)
          ·
            refine ⟨7634088287277922283665907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089392191518614855777271 7634088287277922283665907)
            ·
              refine ⟨11451132430916883425498861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634088287277922283665907 11451132430916883425498861)
              ·
                refine ⟨4294174661593831284562073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451132430916883425498861 4294174661593831284562073)
                ·
                  refine ⟨3220630996195373463421555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294174661593831284562073 3220630996195373463421555)
                  ·
                    refine ⟨4830946494293060195132333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220630996195373463421555 4830946494293060195132333)
                    ·
                      refine ⟨1811604935359897573174625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830946494293060195132333 1811604935359897573174625)
                      ·
                        rfl

theorem cell23_3528088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3528088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528088 prefixEnd_3528088 := by exact prefixLift 3528088
  have htrace : WordTrace (prefixWord ++ tailWord_3528088) baseStart_3528088 baseEnd_3528088 := by
    simpa [prefixWord, tailWord_3528088, baseEnd_3528088] using wordTrace_append hprefix tailTrace_3528088
  have hstable : (prefixWord ++ tailWord_3528088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528088).length < 2 ^ (prefixWord ++ tailWord_3528088).sum := by decide
  have hdescent : baseEnd_3528088 < baseStart_3528088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528098 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_3528098 : Nat := 118140960795 + 3528098 * 2 ^ 59
def prefixEnd_3528098 : Nat := 4983230072969 + 3 ^ 40 * 3528098 * 2
def baseEnd_3528098 : Nat := 1811610070166442534049579

theorem tailTrace_3528098 : CollatzResearch.WordTrace tailWord_3528098 prefixEnd_3528098 1811610070166442534049579 := by
  unfold tailWord_3528098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32170076393077743002990237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85786870381540648007973965 32170076393077743002990237)
  ·
    refine ⟨12063778647404153626121339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32170076393077743002990237 12063778647404153626121339)
    ·
      refine ⟨18095667971106230439182009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063778647404153626121339 18095667971106230439182009)
      ·
        refine ⟨13571750978329672829386507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18095667971106230439182009 13571750978329672829386507)
        ·
          refine ⟨20357626467494509244079761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571750978329672829386507 20357626467494509244079761)
          ·
            refine ⟨15268219850620881933059821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20357626467494509244079761 15268219850620881933059821)
            ·
              refine ⟨5725582443982830724897433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15268219850620881933059821 5725582443982830724897433)
              ·
                refine ⟨4294186832987123043673075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725582443982830724897433 4294186832987123043673075)
                ·
                  refine ⟨6441280249480684565509613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294186832987123043673075 6441280249480684565509613)
                  ·
                    refine ⟨2415480093555256712066105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6441280249480684565509613 2415480093555256712066105)
                    ·
                      refine ⟨1811610070166442534049579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415480093555256712066105 1811610070166442534049579)
                      ·
                        rfl

theorem cell23_3528098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_3528098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528098 prefixEnd_3528098 := by exact prefixLift 3528098
  have htrace : WordTrace (prefixWord ++ tailWord_3528098) baseStart_3528098 baseEnd_3528098 := by
    simpa [prefixWord, tailWord_3528098, baseEnd_3528098] using wordTrace_append hprefix tailTrace_3528098
  have hstable : (prefixWord ++ tailWord_3528098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528098).length < 2 ^ (prefixWord ++ tailWord_3528098).sum := by decide
  have hdescent : baseEnd_3528098 < baseStart_3528098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528127 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_3528127 : Nat := 118140960795 + 3528127 * 2 ^ 59
def prefixEnd_3528127 : Nat := 4983230072969 + 3 ^ 40 * 3528127 * 2
def baseEnd_3528127 : Nat := 1811624961105422920586945

theorem tailTrace_3528127 : CollatzResearch.WordTrace tailWord_3528127 prefixEnd_3528127 1811624961105422920586945 := by
  unfold tailWord_3528127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128681363289205909964766635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85787575526137273309844423 128681363289205909964766635)
  ·
    refine ⟨193022044933808864947149953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128681363289205909964766635 193022044933808864947149953)
    ·
      refine ⟨144766533700356648710362465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193022044933808864947149953 144766533700356648710362465)
      ·
        refine ⟨108574900275267486532771849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144766533700356648710362465 108574900275267486532771849)
        ·
          refine ⟨81431175206450614899578887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108574900275267486532771849 81431175206450614899578887)
          ·
            refine ⟨122146762809675922349368331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81431175206450614899578887 122146762809675922349368331)
            ·
              refine ⟨183220144214513883524052497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122146762809675922349368331 183220144214513883524052497)
              ·
                refine ⟨137415108160885412643039373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183220144214513883524052497 137415108160885412643039373)
                ·
                  refine ⟨51530665560332029741139765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137415108160885412643039373 51530665560332029741139765)
                  ·
                    refine ⟨4830999896281127788231853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51530665560332029741139765 4830999896281127788231853)
                    ·
                      refine ⟨1811624961105422920586945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4830999896281127788231853 1811624961105422920586945)
                      ·
                        rfl

theorem cell23_3528127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_3528127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528127 prefixEnd_3528127 := by exact prefixLift 3528127
  have htrace : WordTrace (prefixWord ++ tailWord_3528127) baseStart_3528127 baseEnd_3528127 := by
    simpa [prefixWord, tailWord_3528127, baseEnd_3528127] using wordTrace_append hprefix tailTrace_3528127
  have hstable : (prefixWord ++ tailWord_3528127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528127).length < 2 ^ (prefixWord ++ tailWord_3528127).sum := by decide
  have hdescent : baseEnd_3528127 < baseStart_3528127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528197 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3528197 : Nat := 118140960795 + 3528197 * 2 ^ 59
def prefixEnd_3528197 : Nat := 4983230072969 + 3 ^ 40 * 3528197 * 2
def baseEnd_3528197 : Nat := 1811660904751237646711623

theorem tailTrace_3528197 : CollatzResearch.WordTrace tailWord_3528197 prefixEnd_3528197 1811660904751237646711623 := by
  unfold tailWord_3528197
  simp only [CollatzResearch.WordTrace]
  refine ⟨128683916398952311919814845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85789277599301541279876563 128683916398952311919814845)
  ·
    refine ⟨48256468649607116969930567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128683916398952311919814845 48256468649607116969930567)
    ·
      refine ⟨72384702974410675454895851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48256468649607116969930567 72384702974410675454895851)
      ·
        refine ⟨108577054461616013182343777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72384702974410675454895851 108577054461616013182343777)
        ·
          refine ⟨81432790846212009886757833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108577054461616013182343777 81432790846212009886757833)
          ·
            refine ⟨61074593134659007415068375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81432790846212009886757833 61074593134659007415068375)
            ·
              refine ⟨91611889701988511122602563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61074593134659007415068375 91611889701988511122602563)
              ·
                refine ⟨137417834552982766683903845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91611889701988511122602563 137417834552982766683903845)
                ·
                  refine ⟨25765843978684268753231971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137417834552982766683903845 25765843978684268753231971)
                  ·
                    refine ⟨38648765968026403129847957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25765843978684268753231971 38648765968026403129847957)
                    ·
                      refine ⟨1811660904751237646711623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38648765968026403129847957 1811660904751237646711623)
                      ·
                        rfl

theorem cell23_3528197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3528197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528197 prefixEnd_3528197 := by exact prefixLift 3528197
  have htrace : WordTrace (prefixWord ++ tailWord_3528197) baseStart_3528197 baseEnd_3528197 := by
    simpa [prefixWord, tailWord_3528197, baseEnd_3528197] using wordTrace_append hprefix tailTrace_3528197
  have hstable : (prefixWord ++ tailWord_3528197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528197).length < 2 ^ (prefixWord ++ tailWord_3528197).sum := by decide
  have hdescent : baseEnd_3528197 < baseStart_3528197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528221 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3528221 : Nat := 118140960795 + 3528221 * 2 ^ 59
def prefixEnd_3528221 : Nat := 4983230072969 + 3 ^ 40 * 3528221 * 2
def baseEnd_3528221 : Nat := 1811673228286945552811513

theorem tailTrace_3528221 : CollatzResearch.WordTrace tailWord_3528221 prefixEnd_3528221 1811673228286945552811513 := by
  unfold tailWord_3528221
  simp only [CollatzResearch.WordTrace]
  refine ⟨128684791750865364018688517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85789861167243576012459011 128684791750865364018688517)
  ·
    refine ⟨24128398453287255753504097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128684791750865364018688517 24128398453287255753504097)
    ·
      refine ⟨18096298839965441815128073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24128398453287255753504097 18096298839965441815128073)
      ·
        refine ⟨13572224129974081361346055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18096298839965441815128073 13572224129974081361346055)
        ·
          refine ⟨20358336194961122042019083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572224129974081361346055 20358336194961122042019083)
          ·
            refine ⟨30537504292441683063028625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358336194961122042019083 30537504292441683063028625)
            ·
              refine ⟨22903128219331262297271469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30537504292441683063028625 22903128219331262297271469)
              ·
                refine ⟨8588673082249223361476801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22903128219331262297271469 8588673082249223361476801)
                ·
                  refine ⟨6441504811686917521107601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588673082249223361476801 6441504811686917521107601)
                  ·
                    refine ⟨4831128608765188140830701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6441504811686917521107601 4831128608765188140830701)
                    ·
                      refine ⟨1811673228286945552811513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831128608765188140830701 1811673228286945552811513)
                      ·
                        rfl

theorem cell23_3528221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3528221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528221 prefixEnd_3528221 := by exact prefixLift 3528221
  have htrace : WordTrace (prefixWord ++ tailWord_3528221) baseStart_3528221 baseEnd_3528221 := by
    simpa [prefixWord, tailWord_3528221, baseEnd_3528221] using wordTrace_append hprefix tailTrace_3528221
  have hstable : (prefixWord ++ tailWord_3528221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528221).length < 2 ^ (prefixWord ++ tailWord_3528221).sum := by decide
  have hdescent : baseEnd_3528221 < baseStart_3528221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528224 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 8]
def baseStart_3528224 : Nat := 118140960795 + 3528224 * 2 ^ 59
def prefixEnd_3528224 : Nat := 4983230072969 + 3 ^ 40 * 3528224 * 2
def baseEnd_3528224 : Nat := 201297196525434337897111

theorem tailTrace_3528224 : CollatzResearch.WordTrace tailWord_3528224 prefixEnd_3528224 201297196525434337897111 := by
  unfold tailWord_3528224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64342450584927247765523863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85789934113236330354031817 64342450584927247765523863)
  ·
    refine ⟨96513675877390871648285795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64342450584927247765523863 96513675877390871648285795)
    ·
      refine ⟨144770513816086307472428693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96513675877390871648285795 144770513816086307472428693)
      ·
        refine ⟨6786117835129045662770095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144770513816086307472428693 6786117835129045662770095)
        ·
          refine ⟨10179176752693568494155143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786117835129045662770095 10179176752693568494155143)
          ·
            refine ⟨15268765129040352741232715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10179176752693568494155143 15268765129040352741232715)
            ·
              refine ⟨22903147693560529111849073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15268765129040352741232715 22903147693560529111849073)
              ·
                refine ⟨17177360770170396833886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22903147693560529111849073 17177360770170396833886805)
                ·
                  refine ⟨201297196525434337897111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17177360770170396833886805 201297196525434337897111)
                  ·
                    rfl

theorem cell23_3528224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_3528224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528224 prefixEnd_3528224 := by exact prefixLift 3528224
  have htrace : WordTrace (prefixWord ++ tailWord_3528224) baseStart_3528224 baseEnd_3528224 := by
    simpa [prefixWord, tailWord_3528224, baseEnd_3528224] using wordTrace_append hprefix tailTrace_3528224
  have hstable : (prefixWord ++ tailWord_3528224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528224).length < 2 ^ (prefixWord ++ tailWord_3528224).sum := by decide
  have hdescent : baseEnd_3528224 < baseStart_3528224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528238 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3528238 : Nat := 118140960795 + 3528238 * 2 ^ 59
def prefixEnd_3528238 : Nat := 4983230072969 + 3 ^ 40 * 3528238 * 2
def baseEnd_3528238 : Nat := 1811681957458071986298935

theorem tailTrace_3528238 : CollatzResearch.WordTrace tailWord_3528238 prefixEnd_3528238 1811681957458071986298935 := by
  unfold tailWord_3528238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085676473975471990257171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85790274527869183948038245 16085676473975471990257171)
  ·
    refine ⟨24128514710963207985385757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085676473975471990257171 24128514710963207985385757)
    ·
      refine ⟨9048193016611202994519659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24128514710963207985385757 9048193016611202994519659)
      ·
        refine ⟨13572289524916804491779489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048193016611202994519659 13572289524916804491779489)
        ·
          refine ⟨10179217143687603368834617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572289524916804491779489 10179217143687603368834617)
          ·
            refine ⟨7634412857765702526625963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179217143687603368834617 7634412857765702526625963)
            ·
              refine ⟨11451619286648553789938945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634412857765702526625963 11451619286648553789938945)
              ·
                refine ⟨8588714464986415342454209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11451619286648553789938945 8588714464986415342454209)
                ·
                  refine ⟨6441535848739811506840657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588714464986415342454209 6441535848739811506840657)
                  ·
                    refine ⟨4831151886554858630130493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6441535848739811506840657 4831151886554858630130493)
                    ·
                      refine ⟨1811681957458071986298935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831151886554858630130493 1811681957458071986298935)
                      ·
                        rfl

theorem cell23_3528238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3528238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528238 prefixEnd_3528238 := by exact prefixLift 3528238
  have htrace : WordTrace (prefixWord ++ tailWord_3528238) baseStart_3528238 baseEnd_3528238 := by
    simpa [prefixWord, tailWord_3528238, baseEnd_3528238] using wordTrace_append hprefix tailTrace_3528238
  have hstable : (prefixWord ++ tailWord_3528238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528238).length < 2 ^ (prefixWord ++ tailWord_3528238).sum := by decide
  have hdescent : baseEnd_3528238 < baseStart_3528238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528245 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3528245 : Nat := 118140960795 + 3528245 * 2 ^ 59
def prefixEnd_3528245 : Nat := 4983230072969 + 3 ^ 40 * 3528245 * 2
def baseEnd_3528245 : Nat := 603895183940884486303801

theorem tailTrace_3528245 : CollatzResearch.WordTrace tailWord_3528245 prefixEnd_3528245 603895183940884486303801 := by
  unfold tailWord_3528245
  simp only [CollatzResearch.WordTrace]
  refine ⟨128685667102778416117562189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85790444735185610745041459 128685667102778416117562189)
  ·
    refine ⟨48257125163541906044085821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128685667102778416117562189 48257125163541906044085821)
    ·
      refine ⟨18096421936328214766532183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48257125163541906044085821 18096421936328214766532183)
      ·
        refine ⟨27144632904492322149798275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18096421936328214766532183 27144632904492322149798275)
        ·
          refine ⟨40716949356738483224697413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27144632904492322149798275 40716949356738483224697413)
          ·
            refine ⟨7634428004388465604630765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40716949356738483224697413 7634428004388465604630765)
            ·
              refine ⟨2862910501645674601736537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7634428004388465604630765 2862910501645674601736537)
              ·
                refine ⟨2147182876234255951302403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862910501645674601736537 2147182876234255951302403)
                ·
                  refine ⟨3220774314351383926953605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147182876234255951302403 3220774314351383926953605)
                  ·
                    refine ⟨603895183940884486303801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220774314351383926953605 603895183940884486303801)
                    ·
                      rfl

theorem cell23_3528245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3528245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528245 prefixEnd_3528245 := by exact prefixLift 3528245
  have htrace : WordTrace (prefixWord ++ tailWord_3528245) baseStart_3528245 baseEnd_3528245 := by
    simpa [prefixWord, tailWord_3528245, baseEnd_3528245] using wordTrace_append hprefix tailTrace_3528245
  have hstable : (prefixWord ++ tailWord_3528245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528245).length < 2 ^ (prefixWord ++ tailWord_3528245).sum := by decide
  have hdescent : baseEnd_3528245 < baseStart_3528245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528261 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_3528261 : Nat := 118140960795 + 3528261 * 2 ^ 59
def prefixEnd_3528261 : Nat := 4983230072969 + 3 ^ 40 * 3528261 * 2
def baseEnd_3528261 : Nat := 1811693767513125396311329

theorem tailTrace_3528261 : CollatzResearch.WordTrace tailWord_3528261 prefixEnd_3528261 1811693767513125396311329 := by
  unfold tailWord_3528261
  simp only [CollatzResearch.WordTrace]
  refine ⟨128686250670720450850144637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85790833780480300566763091 128686250670720450850144637)
  ·
    refine ⟨48257344001520169068804239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128686250670720450850144637 48257344001520169068804239)
    ·
      refine ⟨72386016002280253603206359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48257344001520169068804239 72386016002280253603206359)
      ·
        refine ⟨108579024003420380404809539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72386016002280253603206359 108579024003420380404809539)
        ·
          refine ⟨162868536005130570607214309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108579024003420380404809539 162868536005130570607214309)
          ·
            refine ⟨30537850500961981988852683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162868536005130570607214309 30537850500961981988852683)
            ·
              refine ⟨45806775751442972983279025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30537850500961981988852683 45806775751442972983279025)
              ·
                refine ⟨34355081813582229737459269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45806775751442972983279025 34355081813582229737459269)
                ·
                  refine ⟨6441577840046668075773613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34355081813582229737459269 6441577840046668075773613)
                  ·
                    refine ⟨2415591690017500528415105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6441577840046668075773613 2415591690017500528415105)
                    ·
                      refine ⟨1811693767513125396311329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415591690017500528415105 1811693767513125396311329)
                      ·
                        rfl

theorem cell23_3528261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_3528261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528261 prefixEnd_3528261 := by exact prefixLift 3528261
  have htrace : WordTrace (prefixWord ++ tailWord_3528261) baseStart_3528261 baseEnd_3528261 := by
    simpa [prefixWord, tailWord_3528261, baseEnd_3528261] using wordTrace_append hprefix tailTrace_3528261
  have hstable : (prefixWord ++ tailWord_3528261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528261).length < 2 ^ (prefixWord ++ tailWord_3528261).sum := by decide
  have hdescent : baseEnd_3528261 < baseStart_3528261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528302 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3528302 : Nat := 118140960795 + 3528302 * 2 ^ 59
def prefixEnd_3528302 : Nat := 4983230072969 + 3 ^ 40 * 3528302 * 2
def baseEnd_3528302 : Nat := 1811714820219959735898641

theorem tailTrace_3528302 : CollatzResearch.WordTrace tailWord_3528302 prefixEnd_3528302 1811714820219959735898641 := by
  unfold tailWord_3528302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085968257946489356548395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85791830709047943234924773 16085968257946489356548395)
  ·
    refine ⟨24128952386919734034822593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085968257946489356548395 24128952386919734034822593)
    ·
      refine ⟨18096714290189800526116945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24128952386919734034822593 18096714290189800526116945)
      ·
        refine ⟨13572535717642350394587709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18096714290189800526116945 13572535717642350394587709)
        ·
          refine ⟨5089700894115881397970391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13572535717642350394587709 5089700894115881397970391)
          ·
            refine ⟨7634551341173822096955587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089700894115881397970391 7634551341173822096955587)
            ·
              refine ⟨11451827011760733145433381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634551341173822096955587 11451827011760733145433381)
              ·
                refine ⟨2147217564705137464768759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11451827011760733145433381 2147217564705137464768759)
                ·
                  refine ⟨3220826347057706197153139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147217564705137464768759 3220826347057706197153139)
                  ·
                    refine ⟨4831239520586559295729709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220826347057706197153139 4831239520586559295729709)
                    ·
                      refine ⟨1811714820219959735898641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831239520586559295729709 1811714820219959735898641)
                      ·
                        rfl

theorem cell23_3528302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3528302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528302 prefixEnd_3528302 := by exact prefixLift 3528302
  have htrace : WordTrace (prefixWord ++ tailWord_3528302) baseStart_3528302 baseEnd_3528302 := by
    simpa [prefixWord, tailWord_3528302, baseEnd_3528302] using wordTrace_append hprefix tailTrace_3528302
  have hstable : (prefixWord ++ tailWord_3528302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528302).length < 2 ^ (prefixWord ++ tailWord_3528302).sum := by decide
  have hdescent : baseEnd_3528302 < baseStart_3528302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528321 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3528321 : Nat := 118140960795 + 3528321 * 2 ^ 59
def prefixEnd_3528321 : Nat := 4983230072969 + 3 ^ 40 * 3528321 * 2
def baseEnd_3528321 : Nat := 1811724576352395161561053

theorem tailTrace_3528321 : CollatzResearch.WordTrace tailWord_3528321 prefixEnd_3528321 1811724576352395161561053 := by
  unfold tailWord_3528321
  simp only [CollatzResearch.WordTrace]
  refine ⟨128688439050503081097328817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85792292700335387398219211 128688439050503081097328817)
  ·
    refine ⟨96516329287877310822996613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128688439050503081097328817 96516329287877310822996613)
    ·
      refine ⟨18096811741476995779311865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96516329287877310822996613 18096811741476995779311865)
      ·
        refine ⟨13572608806107746834483899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18096811741476995779311865 13572608806107746834483899)
        ·
          refine ⟨20358913209161620251725849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572608806107746834483899 20358913209161620251725849)
          ·
            refine ⟨15269184906871215188794387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20358913209161620251725849 15269184906871215188794387)
            ·
              refine ⟨22903777360306822783191581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269184906871215188794387 22903777360306822783191581)
              ·
                refine ⟨8588916510115058543696843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22903777360306822783191581 8588916510115058543696843)
                ·
                  refine ⟨12883374765172587815545265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8588916510115058543696843 12883374765172587815545265)
                  ·
                    refine ⟨9662531073879440861658949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12883374765172587815545265 9662531073879440861658949)
                    ·
                      refine ⟨1811724576352395161561053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9662531073879440861658949 1811724576352395161561053)
                      ·
                        rfl

theorem cell23_3528321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3528321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528321 prefixEnd_3528321 := by exact prefixLift 3528321
  have htrace : WordTrace (prefixWord ++ tailWord_3528321) baseStart_3528321 baseEnd_3528321 := by
    simpa [prefixWord, tailWord_3528321, baseEnd_3528321] using wordTrace_append hprefix tailTrace_3528321
  have hstable : (prefixWord ++ tailWord_3528321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528321).length < 2 ^ (prefixWord ++ tailWord_3528321).sum := by decide
  have hdescent : baseEnd_3528321 < baseStart_3528321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528398 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_3528398 : Nat := 118140960795 + 3528398 * 2 ^ 59
def prefixEnd_3528398 : Nat := 4983230072969 + 3 ^ 40 * 3528398 * 2
def baseEnd_3528398 : Nat := 1811764114362791360298199

theorem tailTrace_3528398 : CollatzResearch.WordTrace tailWord_3528398 prefixEnd_3528398 1811764114362791360298199 := by
  unfold tailWord_3528398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086405933903015405985231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85794164980816082165254565 16086405933903015405985231)
  ·
    refine ⟨24129608900854523108977847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16086405933903015405985231 24129608900854523108977847)
    ·
      refine ⟨36194413351281784663466771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24129608900854523108977847 36194413351281784663466771)
      ·
        refine ⟨54291620026922676995200157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36194413351281784663466771 54291620026922676995200157)
        ·
          refine ⟨20359357510096003873200059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54291620026922676995200157 20359357510096003873200059)
          ·
            refine ⟨30539036265144005809800089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20359357510096003873200059 30539036265144005809800089)
            ·
              refine ⟨22904277198858004357350067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30539036265144005809800089 22904277198858004357350067)
              ·
                refine ⟨34356415798287006536025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22904277198858004357350067 34356415798287006536025101)
                ·
                  refine ⟨12883655924357627451009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34356415798287006536025101 12883655924357627451009413)
                  ·
                    refine ⟨2415685485817055147064265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12883655924357627451009413 2415685485817055147064265)
                    ·
                      refine ⟨1811764114362791360298199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415685485817055147064265 1811764114362791360298199)
                      ·
                        rfl

theorem cell23_3528398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_3528398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528398 prefixEnd_3528398 := by exact prefixLift 3528398
  have htrace : WordTrace (prefixWord ++ tailWord_3528398) baseStart_3528398 baseEnd_3528398 := by
    simpa [prefixWord, tailWord_3528398, baseEnd_3528398] using wordTrace_append hprefix tailTrace_3528398
  have hstable : (prefixWord ++ tailWord_3528398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528398).length < 2 ^ (prefixWord ++ tailWord_3528398).sum := by decide
  have hdescent : baseEnd_3528398 < baseStart_3528398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528401 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3528401 : Nat := 118140960795 + 3528401 * 2 ^ 59
def prefixEnd_3528401 : Nat := 4983230072969 + 3 ^ 40 * 3528401 * 2
def baseEnd_3528401 : Nat := 1811765654804754848560685

theorem tailTrace_3528401 : CollatzResearch.WordTrace tailWord_3528401 prefixEnd_3528401 1811765654804754848560685 := by
  unfold tailWord_3528401
  simp only [CollatzResearch.WordTrace]
  refine ⟨128691356890213254760241057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85794237926808836506827371 128691356890213254760241057)
  ·
    refine ⟨96518517667659941070180793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128691356890213254760241057 96518517667659941070180793)
    ·
      refine ⟨72388888250744955802635595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96518517667659941070180793 72388888250744955802635595)
      ·
        refine ⟨108583332376117433703953393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72388888250744955802635595 108583332376117433703953393)
        ·
          refine ⟨81437499282088075277965045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108583332376117433703953393 81437499282088075277965045)
          ·
            refine ⟨7634765557695757057309223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81437499282088075277965045 7634765557695757057309223)
            ·
              refine ⟨11452148336543635585963835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634765557695757057309223 11452148336543635585963835)
              ·
                refine ⟨17178222504815453378945753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452148336543635585963835 17178222504815453378945753)
                ·
                  refine ⟨12883666878611590034209315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17178222504815453378945753 12883666878611590034209315)
                  ·
                    refine ⟨19325500317917385051313973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12883666878611590034209315 19325500317917385051313973)
                    ·
                      refine ⟨1811765654804754848560685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19325500317917385051313973 1811765654804754848560685)
                      ·
                        rfl

theorem cell23_3528401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3528401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528401 prefixEnd_3528401 := by exact prefixLift 3528401
  have htrace : WordTrace (prefixWord ++ tailWord_3528401) baseStart_3528401 baseEnd_3528401 := by
    simpa [prefixWord, tailWord_3528401, baseEnd_3528401] using wordTrace_append hprefix tailTrace_3528401
  have hstable : (prefixWord ++ tailWord_3528401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528401).length < 2 ^ (prefixWord ++ tailWord_3528401).sum := by decide
  have hdescent : baseEnd_3528401 < baseStart_3528401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528415 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 2, 2, 2]
def baseStart_3528415 : Nat := 118140960795 + 3528415 * 2 ^ 59
def prefixEnd_3528415 : Nat := 4983230072969 + 3 ^ 40 * 3528415 * 2
def baseEnd_3528415 : Nat := 1811772843533917793785621

theorem tailTrace_3528415 : CollatzResearch.WordTrace tailWord_3528415 prefixEnd_3528415 1811772843533917793785621 := by
  unfold tailWord_3528415
  simp only [CollatzResearch.WordTrace]
  refine ⟨128691867512162535151250699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85794578341441690100833799 128691867512162535151250699)
  ·
    refine ⟨193037801268243802726876049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128691867512162535151250699 193037801268243802726876049)
    ·
      refine ⟨144778350951182852045157037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193037801268243802726876049 144778350951182852045157037)
      ·
        refine ⟨54291881606693569516933889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144778350951182852045157037 54291881606693569516933889)
        ·
          refine ⟨40718911205020177137700417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54291881606693569516933889 40718911205020177137700417)
          ·
            refine ⟨30539183403765132853275313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40718911205020177137700417 30539183403765132853275313)
            ·
              refine ⟨22904387552823849639956485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30539183403765132853275313 22904387552823849639956485)
              ·
                refine ⟨4294572666154471807491841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22904387552823849639956485 4294572666154471807491841)
                ·
                  refine ⟨3220929499615853855618881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294572666154471807491841 3220929499615853855618881)
                  ·
                    refine ⟨2415697124711890391714161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3220929499615853855618881 2415697124711890391714161)
                    ·
                      refine ⟨1811772843533917793785621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415697124711890391714161 1811772843533917793785621)
                      ·
                        rfl

theorem cell23_3528415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_3528415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528415 prefixEnd_3528415 := by exact prefixLift 3528415
  have htrace : WordTrace (prefixWord ++ tailWord_3528415) baseStart_3528415 baseEnd_3528415 := by
    simpa [prefixWord, tailWord_3528415, baseEnd_3528415] using wordTrace_append hprefix tailTrace_3528415
  have hstable : (prefixWord ++ tailWord_3528415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528415).length < 2 ^ (prefixWord ++ tailWord_3528415).sum := by decide
  have hdescent : baseEnd_3528415 < baseStart_3528415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528431 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_3528431 : Nat := 118140960795 + 3528431 * 2 ^ 59
def prefixEnd_3528431 : Nat := 4983230072969 + 3 ^ 40 * 3528431 * 2
def baseEnd_3528431 : Nat := 1811781059224389731185547

theorem tailTrace_3528431 : CollatzResearch.WordTrace tailWord_3528431 prefixEnd_3528431 1811781059224389731185547 := by
  unfold tailWord_3528431
  simp only [CollatzResearch.WordTrace]
  refine ⟨128692451080104569883833147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85794967386736379922555431 128692451080104569883833147)
  ·
    refine ⟨193038676620156854825749721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128692451080104569883833147 193038676620156854825749721)
    ·
      refine ⟨144779007465117641119312291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193038676620156854825749721 144779007465117641119312291)
      ·
        refine ⟨217168511197676461678968437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144779007465117641119312291 217168511197676461678968437)
        ·
          refine ⟨20359547924782168282403291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217168511197676461678968437 20359547924782168282403291)
          ·
            refine ⟨30539321887173252423604937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20359547924782168282403291 30539321887173252423604937)
            ·
              refine ⟨22904491415379939317703703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30539321887173252423604937 22904491415379939317703703)
              ·
                refine ⟨34356737123069908976555555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22904491415379939317703703 34356737123069908976555555)
                ·
                  refine ⟨51535105684604863464833333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34356737123069908976555555 51535105684604863464833333)
                  ·
                    refine ⟨4831416157931705949828125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51535105684604863464833333 4831416157931705949828125)
                    ·
                      refine ⟨1811781059224389731185547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831416157931705949828125 1811781059224389731185547)
                      ·
                        rfl

theorem cell23_3528431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_3528431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528431 prefixEnd_3528431 := by exact prefixLift 3528431
  have htrace : WordTrace (prefixWord ++ tailWord_3528431) baseStart_3528431 baseEnd_3528431 := by
    simpa [prefixWord, tailWord_3528431, baseEnd_3528431] using wordTrace_append hprefix tailTrace_3528431
  have hstable : (prefixWord ++ tailWord_3528431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528431).length < 2 ^ (prefixWord ++ tailWord_3528431).sum := by decide
  have hdescent : baseEnd_3528431 < baseStart_3528431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528436 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3528436 : Nat := 118140960795 + 3528436 * 2 ^ 59
def prefixEnd_3528436 : Nat := 4983230072969 + 3 ^ 40 * 3528436 * 2
def baseEnd_3528436 : Nat := 1811783626627662211623025

theorem tailTrace_3528436 : CollatzResearch.WordTrace tailWord_3528436 prefixEnd_3528436 1811783626627662211623025 := by
  unfold tailWord_3528436
  simp only [CollatzResearch.WordTrace]
  refine ⟨64346316722543227868882581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85795088963390970491843441 64346316722543227868882581)
  ·
    refine ⟨3016233596369213806353871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64346316722543227868882581 3016233596369213806353871)
    ·
      refine ⟨4524350394553820709530807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016233596369213806353871 4524350394553820709530807)
      ·
        refine ⟨6786525591830731064296211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524350394553820709530807 6786525591830731064296211)
        ·
          refine ⟨10179788387746096596444317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786525591830731064296211 10179788387746096596444317)
          ·
            refine ⟨3817420645404786223666619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10179788387746096596444317 3817420645404786223666619)
            ·
              refine ⟨5726130968107179335499929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817420645404786223666619 5726130968107179335499929)
              ·
                refine ⟨4294598226080384501624947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5726130968107179335499929 4294598226080384501624947)
                ·
                  refine ⟨6441897339120576752437421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294598226080384501624947 6441897339120576752437421)
                  ·
                    refine ⟨2415711502170216282164033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6441897339120576752437421 2415711502170216282164033)
                    ·
                      refine ⟨1811783626627662211623025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415711502170216282164033 1811783626627662211623025)
                      ·
                        rfl

theorem cell23_3528436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3528436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528436 prefixEnd_3528436 := by exact prefixLift 3528436
  have htrace : WordTrace (prefixWord ++ tailWord_3528436) baseStart_3528436 baseEnd_3528436 := by
    simpa [prefixWord, tailWord_3528436, baseEnd_3528436] using wordTrace_append hprefix tailTrace_3528436
  have hstable : (prefixWord ++ tailWord_3528436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528436).length < 2 ^ (prefixWord ++ tailWord_3528436).sum := by decide
  have hdescent : baseEnd_3528436 < baseStart_3528436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528451 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 2, 5]
def baseStart_3528451 : Nat := 118140960795 + 3528451 * 2 ^ 59
def prefixEnd_3528451 : Nat := 4983230072969 + 3 ^ 40 * 3528451 * 2
def baseEnd_3528451 : Nat := 603930442945826550978485

theorem tailTrace_3528451 : CollatzResearch.WordTrace tailWord_3528451 prefixEnd_3528451 603930442945826550978485 := by
  unfold tailWord_3528451
  simp only [CollatzResearch.WordTrace]
  refine ⟨128693180540032113299561207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85795453693354742199707471 128693180540032113299561207)
  ·
    refine ⟨193039770810048169949341811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128693180540032113299561207 193039770810048169949341811)
    ·
      refine ⟨289559656215072254924012717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193039770810048169949341811 289559656215072254924012717)
      ·
        refine ⟨108584871080652095596504769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289559656215072254924012717 108584871080652095596504769)
        ·
          refine ⟨81438653310489071697378577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108584871080652095596504769 81438653310489071697378577)
          ·
            refine ⟨61078989982866803773033933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81438653310489071697378577 61078989982866803773033933)
            ·
              refine ⟨22904621243575051414887725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61078989982866803773033933 22904621243575051414887725)
              ·
                refine ⟨8589232966340644280582897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22904621243575051414887725 8589232966340644280582897)
                ·
                  refine ⟨6441924724755483210437173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589232966340644280582897 6441924724755483210437173)
                  ·
                    refine ⟨603930442945826550978485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6441924724755483210437173 603930442945826550978485)
                    ·
                      rfl

theorem cell23_3528451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].length) (baseStart_3528451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528451 prefixEnd_3528451 := by exact prefixLift 3528451
  have htrace : WordTrace (prefixWord ++ tailWord_3528451) baseStart_3528451 baseEnd_3528451 := by
    simpa [prefixWord, tailWord_3528451, baseEnd_3528451] using wordTrace_append hprefix tailTrace_3528451
  have hstable : (prefixWord ++ tailWord_3528451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528451).length < 2 ^ (prefixWord ++ tailWord_3528451).sum := by decide
  have hdescent : baseEnd_3528451 < baseStart_3528451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528498 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3528498 : Nat := 118140960795 + 3528498 * 2 ^ 59
def prefixEnd_3528498 : Nat := 4983230072969 + 3 ^ 40 * 3528498 * 2
def baseEnd_3528498 : Nat := 603938487476080323015913

theorem tailTrace_3528498 : CollatzResearch.WordTrace tailWord_3528498 prefixEnd_3528498 603938487476080323015913 := by
  unfold tailWord_3528498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32173723692715460081630537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85796596513907893551014765 32173723692715460081630537)
  ·
    refine ⟨24130292769536595061222903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32173723692715460081630537 24130292769536595061222903)
    ·
      refine ⟨36195439154304892591834355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24130292769536595061222903 36195439154304892591834355)
      ·
        refine ⟨54293158731457338887751533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36195439154304892591834355 54293158731457338887751533)
        ·
          refine ⟨20359934524296502082906825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54293158731457338887751533 20359934524296502082906825)
          ·
            refine ⟨15269950893222376562180119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20359934524296502082906825 15269950893222376562180119)
            ·
              refine ⟨22904926339833564843270179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269950893222376562180119 22904926339833564843270179)
              ·
                refine ⟨34357389509750347264905269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22904926339833564843270179 34357389509750347264905269)
                ·
                  refine ⟨3221005266539095056084869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34357389509750347264905269 3221005266539095056084869)
                  ·
                    refine ⟨603938487476080323015913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221005266539095056084869 603938487476080323015913)
                    ·
                      rfl

theorem cell23_3528498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3528498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528498 prefixEnd_3528498 := by exact prefixLift 3528498
  have htrace : WordTrace (prefixWord ++ tailWord_3528498) baseStart_3528498 baseEnd_3528498 := by
    simpa [prefixWord, tailWord_3528498, baseEnd_3528498] using wordTrace_append hprefix tailTrace_3528498
  have hstable : (prefixWord ++ tailWord_3528498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528498).length < 2 ^ (prefixWord ++ tailWord_3528498).sum := by decide
  have hdescent : baseEnd_3528498 < baseStart_3528498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528502 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3528502 : Nat := 118140960795 + 3528502 * 2 ^ 59
def prefixEnd_3528502 : Nat := 4983230072969 + 3 ^ 40 * 3528502 * 2
def baseEnd_3528502 : Nat := 603939172116952984465907

theorem tailTrace_3528502 : CollatzResearch.WordTrace tailWord_3528502 prefixEnd_3528502 603939172116952984465907 := by
  unfold tailWord_3528502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043440041427959313104235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85796693775231566006445173 8043440041427959313104235)
  ·
    refine ⟨12065160062141938969656353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8043440041427959313104235 12065160062141938969656353)
    ·
      refine ⟨9048870046606454227242265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12065160062141938969656353 9048870046606454227242265)
      ·
        refine ⟨6786652534954840670431699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9048870046606454227242265 6786652534954840670431699)
        ·
          refine ⟨10179978802432261005647549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786652534954840670431699 10179978802432261005647549)
          ·
            refine ⟨3817492050912097877117831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10179978802432261005647549 3817492050912097877117831)
            ·
              refine ⟨5726238076368146815676747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817492050912097877117831 5726238076368146815676747)
              ·
                refine ⟨8589357114552220223515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726238076368146815676747 8589357114552220223515121)
                ·
                  refine ⟨6442017835914165167636341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589357114552220223515121 6442017835914165167636341)
                  ·
                    refine ⟨603939172116952984465907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6442017835914165167636341 603939172116952984465907)
                    ·
                      rfl

theorem cell23_3528502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3528502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528502 prefixEnd_3528502 := by exact prefixLift 3528502
  have htrace : WordTrace (prefixWord ++ tailWord_3528502) baseStart_3528502 baseEnd_3528502 := by
    simpa [prefixWord, tailWord_3528502, baseEnd_3528502] using wordTrace_append hprefix tailTrace_3528502
  have hstable : (prefixWord ++ tailWord_3528502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528502).length < 2 ^ (prefixWord ++ tailWord_3528502).sum := by decide
  have hdescent : baseEnd_3528502 < baseStart_3528502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528505 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3528505 : Nat := 118140960795 + 3528505 * 2 ^ 59
def prefixEnd_3528505 : Nat := 4983230072969 + 3 ^ 40 * 3528505 * 2
def baseEnd_3528505 : Nat := 1811819056792822441660207

theorem tailTrace_3528505 : CollatzResearch.WordTrace tailWord_3528505 prefixEnd_3528505 1811819056792822441660207 := by
  unfold tailWord_3528505
  simp only [CollatzResearch.WordTrace]
  refine ⟨128695150081836480522026969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85796766721224320348017979 128695150081836480522026969)
  ·
    refine ⟨96521362561377360391520227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128695150081836480522026969 96521362561377360391520227)
    ·
      refine ⟨144782043842066040587280341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96521362561377360391520227 144782043842066040587280341)
      ·
        refine ⟨3393329152548422826264383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144782043842066040587280341 3393329152548422826264383)
        ·
          refine ⟨5089993728822634239396575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393329152548422826264383 5089993728822634239396575)
          ·
            refine ⟨7634990593233951359094863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089993728822634239396575 7634990593233951359094863)
            ·
              refine ⟨11452485889850927038642295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634990593233951359094863 11452485889850927038642295)
              ·
                refine ⟨17178728834776390557963443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452485889850927038642295 17178728834776390557963443)
                ·
                  refine ⟨25768093252164585836945165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17178728834776390557963443 25768093252164585836945165)
                  ·
                    refine ⟨9663034969561719688854437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25768093252164585836945165 9663034969561719688854437)
                    ·
                      refine ⟨1811819056792822441660207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663034969561719688854437 1811819056792822441660207)
                      ·
                        rfl

theorem cell23_3528505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3528505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528505 prefixEnd_3528505 := by exact prefixLift 3528505
  have htrace : WordTrace (prefixWord ++ tailWord_3528505) baseStart_3528505 baseEnd_3528505 := by
    simpa [prefixWord, tailWord_3528505, baseEnd_3528505] using wordTrace_append hprefix tailTrace_3528505
  have hstable : (prefixWord ++ tailWord_3528505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528505).length < 2 ^ (prefixWord ++ tailWord_3528505).sum := by decide
  have hdescent : baseEnd_3528505 < baseStart_3528505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528515 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 1, 4]
def baseStart_3528515 : Nat := 118140960795 + 3528515 * 2 ^ 59
def prefixEnd_3528515 : Nat := 4983230072969 + 3 ^ 40 * 3528515 * 2
def baseEnd_3528515 : Nat := 603941397199789134178387

theorem tailTrace_3528515 : CollatzResearch.WordTrace tailWord_3528515 prefixEnd_3528515 603941397199789134178387 := by
  unfold tailWord_3528515
  simp only [CollatzResearch.WordTrace]
  refine ⟨128695514811800252229890999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85797009874533501486593999 128695514811800252229890999)
  ·
    refine ⟨193043272217700378344836499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128695514811800252229890999 193043272217700378344836499)
    ·
      refine ⟨289564908326550567517254749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193043272217700378344836499 289564908326550567517254749)
      ·
        refine ⟨108586840622456462818970531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289564908326550567517254749 108586840622456462818970531)
        ·
          refine ⟨162880260933684694228455797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108586840622456462818970531 162880260933684694228455797)
          ·
            refine ⟨15270024462532940083917731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162880260933684694228455797 15270024462532940083917731)
            ·
              refine ⟨22905036693799410125876597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270024462532940083917731 22905036693799410125876597)
              ·
                refine ⟨2147347190043694699300931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22905036693799410125876597 2147347190043694699300931)
                ·
                  refine ⟨3221020785065542048951397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147347190043694699300931 3221020785065542048951397)
                  ·
                    refine ⟨603941397199789134178387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221020785065542048951397 603941397199789134178387)
                    ·
                      rfl

theorem cell23_3528515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 4].length) (baseStart_3528515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528515 prefixEnd_3528515 := by exact prefixLift 3528515
  have htrace : WordTrace (prefixWord ++ tailWord_3528515) baseStart_3528515 baseEnd_3528515 := by
    simpa [prefixWord, tailWord_3528515, baseEnd_3528515] using wordTrace_append hprefix tailTrace_3528515
  have hstable : (prefixWord ++ tailWord_3528515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528515).length < 2 ^ (prefixWord ++ tailWord_3528515).sum := by decide
  have hdescent : baseEnd_3528515 < baseStart_3528515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528532 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3528532 : Nat := 118140960795 + 3528532 * 2 ^ 59
def prefixEnd_3528532 : Nat := 4983230072969 + 3 ^ 40 * 3528532 * 2
def baseEnd_3528532 : Nat := 603944306923497945340861

theorem tailTrace_3528532 : CollatzResearch.WordTrace tailWord_3528532 prefixEnd_3528532 603944306923497945340861 := by
  unfold tailWord_3528532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348067426369332066629925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85797423235159109422173233 64348067426369332066629925)
  ·
    refine ⟨12065262642444249762493111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64348067426369332066629925 12065262642444249762493111)
    ·
      refine ⟨18097893963666374643739667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12065262642444249762493111 18097893963666374643739667)
      ·
        refine ⟨27146840945499561965609501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18097893963666374643739667 27146840945499561965609501)
        ·
          refine ⟨10180065354562335737103563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27146840945499561965609501 10180065354562335737103563)
          ·
            refine ⟨15270098031843503605655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10180065354562335737103563 15270098031843503605655345)
            ·
              refine ⟨11452573523882627704241509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15270098031843503605655345 11452573523882627704241509)
              ·
                refine ⟨2147357535727992694545283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11452573523882627704241509 2147357535727992694545283)
                ·
                  refine ⟨3221036303591989041817925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147357535727992694545283 3221036303591989041817925)
                  ·
                    refine ⟨603944306923497945340861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221036303591989041817925 603944306923497945340861)
                    ·
                      rfl

theorem cell23_3528532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3528532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528532 prefixEnd_3528532 := by exact prefixLift 3528532
  have htrace : WordTrace (prefixWord ++ tailWord_3528532) baseStart_3528532 baseEnd_3528532 := by
    simpa [prefixWord, tailWord_3528532, baseEnd_3528532] using wordTrace_append hprefix tailTrace_3528532
  have hstable : (prefixWord ++ tailWord_3528532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528532).length < 2 ^ (prefixWord ++ tailWord_3528532).sum := by decide
  have hdescent : baseEnd_3528532 < baseStart_3528532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528565 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3528565 : Nat := 118140960795 + 3528565 * 2 ^ 59
def prefixEnd_3528565 : Nat := 4983230072969 + 3 ^ 40 * 3528565 * 2
def baseEnd_3528565 : Nat := 1811849865632092206909931

theorem tailTrace_3528565 : CollatzResearch.WordTrace tailWord_3528565 prefixEnd_3528565 1811849865632092206909931 := by
  unfold tailWord_3528565
  simp only [CollatzResearch.WordTrace]
  refine ⟨128697338461619110769211149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85798225641079407179474099 128697338461619110769211149)
  ·
    refine ⟨48261501923107166538454181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128697338461619110769211149 48261501923107166538454181)
    ·
      refine ⟨9049031610582593725960159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48261501923107166538454181 9049031610582593725960159)
      ·
        refine ⟨13573547415873890588940239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049031610582593725960159 13573547415873890588940239)
        ·
          refine ⟨20360321123810835883410359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13573547415873890588940239 20360321123810835883410359)
          ·
            refine ⟨30540481685716253825115539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20360321123810835883410359 30540481685716253825115539)
            ·
              refine ⟨45810722528574380737673309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30540481685716253825115539 45810722528574380737673309)
              ·
                refine ⟨17179020948215392776627491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45810722528574380737673309 17179020948215392776627491)
                ·
                  refine ⟨25768531422323089164941237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17179020948215392776627491 25768531422323089164941237)
                  ·
                    refine ⟨2415799820842789609213241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25768531422323089164941237 2415799820842789609213241)
                    ·
                      refine ⟨1811849865632092206909931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415799820842789609213241 1811849865632092206909931)
                      ·
                        rfl

theorem cell23_3528565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3528565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528565 prefixEnd_3528565 := by exact prefixLift 3528565
  have htrace : WordTrace (prefixWord ++ tailWord_3528565) baseStart_3528565 baseEnd_3528565 := by
    simpa [prefixWord, tailWord_3528565, baseEnd_3528565] using wordTrace_append hprefix tailTrace_3528565
  have hstable : (prefixWord ++ tailWord_3528565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528565).length < 2 ^ (prefixWord ++ tailWord_3528565).sum := by decide
  have hdescent : baseEnd_3528565 < baseStart_3528565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528566 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_3528566 : Nat := 118140960795 + 3528566 * 2 ^ 59
def prefixEnd_3528566 : Nat := 4983230072969 + 3 ^ 40 * 3528566 * 2
def baseEnd_3528566 : Nat := 603950126370915567665809

theorem tailTrace_3528566 : CollatzResearch.WordTrace tailWord_3528566 prefixEnd_3528566 603950126370915567665809 := by
  unfold tailWord_3528566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043585933413467996249847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85798249956410325293331701 8043585933413467996249847)
  ·
    refine ⟨12065378900120201994374771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8043585933413467996249847 12065378900120201994374771)
    ·
      refine ⟨18098068350180302991562157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12065378900120201994374771 18098068350180302991562157)
      ·
        refine ⟨6786775631317613621835809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18098068350180302991562157 6786775631317613621835809)
        ·
          refine ⟨5090081723488210216376857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786775631317613621835809 5090081723488210216376857)
          ·
            refine ⟨3817561292616157662282643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090081723488210216376857 3817561292616157662282643)
            ·
              refine ⟨5726341938924236493423965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817561292616157662282643 5726341938924236493423965)
              ·
                refine ⟨2147378227096588685033987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5726341938924236493423965 2147378227096588685033987)
                ·
                  refine ⟨3221067340644883027550981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147378227096588685033987 3221067340644883027550981)
                  ·
                    refine ⟨603950126370915567665809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221067340644883027550981 603950126370915567665809)
                    ·
                      rfl

theorem cell23_3528566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_3528566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528566 prefixEnd_3528566 := by exact prefixLift 3528566
  have htrace : WordTrace (prefixWord ++ tailWord_3528566) baseStart_3528566 baseEnd_3528566 := by
    simpa [prefixWord, tailWord_3528566, baseEnd_3528566] using wordTrace_append hprefix tailTrace_3528566
  have hstable : (prefixWord ++ tailWord_3528566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528566).length < 2 ^ (prefixWord ++ tailWord_3528566).sum := by decide
  have hdescent : baseEnd_3528566 < baseStart_3528566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528571 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 6]
def baseStart_3528571 : Nat := 118140960795 + 3528571 * 2 ^ 59
def prefixEnd_3528571 : Nat := 4983230072969 + 3 ^ 40 * 3528571 * 2
def baseEnd_3528571 : Nat := 603950982172006394478301

theorem tailTrace_3528571 : CollatzResearch.WordTrace tailWord_3528571 prefixEnd_3528571 603950982172006394478301 := by
  unfold tailWord_3528571
  simp only [CollatzResearch.WordTrace]
  refine ⟨128697557299597373793929567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85798371533064915862619711 128697557299597373793929567)
  ·
    refine ⟨193046335949396060690894351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128697557299597373793929567 193046335949396060690894351)
    ·
      refine ⟨289569503924094091036341527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193046335949396060690894351 289569503924094091036341527)
      ·
        refine ⟨434354255886141136554512291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289569503924094091036341527 434354255886141136554512291)
        ·
          refine ⟨651531383829211704831768437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434354255886141136554512291 651531383829211704831768437)
          ·
            refine ⟨61081067233988597327978291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 651531383829211704831768437 61081067233988597327978291)
            ·
              refine ⟨91621600850982895991967437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61081067233988597327978291 91621600850982895991967437)
              ·
                refine ⟨34358100319118585996987789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91621600850982895991967437 34358100319118585996987789)
                ·
                  refine ⟨12884287619669469748870421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34358100319118585996987789 12884287619669469748870421)
                  ·
                    refine ⟨603950982172006394478301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12884287619669469748870421 603950982172006394478301)
                    ·
                      rfl

theorem cell23_3528571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_3528571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528571 prefixEnd_3528571 := by exact prefixLift 3528571
  have htrace : WordTrace (prefixWord ++ tailWord_3528571) baseStart_3528571 baseEnd_3528571 := by
    simpa [prefixWord, tailWord_3528571, baseEnd_3528571] using wordTrace_append hprefix tailTrace_3528571
  have hstable : (prefixWord ++ tailWord_3528571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528571).length < 2 ^ (prefixWord ++ tailWord_3528571).sum := by decide
  have hdescent : baseEnd_3528571 < baseStart_3528571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528601 : List Nat := [1, 2, 1, 2, 1, 3, 3, 10]
def baseStart_3528601 : Nat := 118140960795 + 3528601 * 2 ^ 59
def prefixEnd_3528601 : Nat := 4983230072969 + 3 ^ 40 * 3528601 * 2
def baseEnd_3528601 : Nat := 67106235219839039483695

theorem tailTrace_3528601 : CollatzResearch.WordTrace tailWord_3528601 prefixEnd_3528601 67106235219839039483695 := by
  unfold tailWord_3528601
  simp only [CollatzResearch.WordTrace]
  refine ⟨128698651489488688917521657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85799100992992459278347771 128698651489488688917521657)
  ·
    refine ⟨96523988617116516688141243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128698651489488688917521657 96523988617116516688141243)
    ·
      refine ⟨144785982925674775032211865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96523988617116516688141243 144785982925674775032211865)
      ·
        refine ⟨108589487194256081274158899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144785982925674775032211865 108589487194256081274158899)
        ·
          refine ⟨162884230791384121911238349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108589487194256081274158899 162884230791384121911238349)
          ·
            refine ⟨61081586546769045716714381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162884230791384121911238349 61081586546769045716714381)
            ·
              refine ⟨22905594955038392143767893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61081586546769045716714381 22905594955038392143767893)
              ·
                refine ⟨67106235219839039483695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22905594955038392143767893 67106235219839039483695)
                ·
                  rfl

theorem cell23_3528601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 10].length) (baseStart_3528601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528601 prefixEnd_3528601 := by exact prefixLift 3528601
  have htrace : WordTrace (prefixWord ++ tailWord_3528601) baseStart_3528601 baseEnd_3528601 := by
    simpa [prefixWord, tailWord_3528601, baseEnd_3528601] using wordTrace_append hprefix tailTrace_3528601
  have hstable : (prefixWord ++ tailWord_3528601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528601).length < 2 ^ (prefixWord ++ tailWord_3528601).sum := by decide
  have hdescent : baseEnd_3528601 < baseStart_3528601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528608 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3528608 : Nat := 118140960795 + 3528608 * 2 ^ 59
def prefixEnd_3528608 : Nat := 4983230072969 + 3 ^ 40 * 3528608 * 2
def baseEnd_3528608 : Nat := 1811871945300235538672233

theorem tailTrace_3528608 : CollatzResearch.WordTrace tailWord_3528608 prefixEnd_3528608 1811871945300235538672233 := by
  unfold tailWord_3528608
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349453400231664556513239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85799271200308886075350985 64349453400231664556513239)
  ·
    refine ⟨96524180100347496834769859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64349453400231664556513239 96524180100347496834769859)
    ·
      refine ⟨144786270150521245252154789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96524180100347496834769859 144786270150521245252154789)
      ·
        refine ⟨27147425653222733484779023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144786270150521245252154789 27147425653222733484779023)
        ·
          refine ⟨40721138479834100227168535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27147425653222733484779023 40721138479834100227168535)
          ·
            refine ⟨61081707719751150340752803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40721138479834100227168535 61081707719751150340752803)
            ·
              refine ⟨91622561579626725511129205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61081707719751150340752803 91622561579626725511129205)
              ·
                refine ⟨8589615148090005516668363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91622561579626725511129205 8589615148090005516668363)
                ·
                  refine ⟨12884422722135008275002545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589615148090005516668363 12884422722135008275002545)
                  ·
                    refine ⟨9663317041601256206251909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12884422722135008275002545 9663317041601256206251909)
                    ·
                      refine ⟨1811871945300235538672233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663317041601256206251909 1811871945300235538672233)
                      ·
                        rfl

theorem cell23_3528608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3528608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528608 prefixEnd_3528608 := by exact prefixLift 3528608
  have htrace : WordTrace (prefixWord ++ tailWord_3528608) baseStart_3528608 baseEnd_3528608 := by
    simpa [prefixWord, tailWord_3528608, baseEnd_3528608] using wordTrace_append hprefix tailTrace_3528608
  have hstable : (prefixWord ++ tailWord_3528608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528608).length < 2 ^ (prefixWord ++ tailWord_3528608).sum := by decide
  have hdescent : baseEnd_3528608 < baseStart_3528608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528609 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3528609 : Nat := 118140960795 + 3528609 * 2 ^ 59
def prefixEnd_3528609 : Nat := 4983230072969 + 3 ^ 40 * 3528609 * 2
def baseEnd_3528609 : Nat := 603957486260296678253243

theorem tailTrace_3528609 : CollatzResearch.WordTrace tailWord_3528609 prefixEnd_3528609 603957486260296678253243 := by
  unfold tailWord_3528609
  simp only [CollatzResearch.WordTrace]
  refine ⟨128698943273459706283812881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85799295515639804189208587 128698943273459706283812881)
  ·
    refine ⟨96524207455094779712859661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128698943273459706283812881 96524207455094779712859661)
    ·
      refine ⟨36196577795660542392322373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96524207455094779712859661 36196577795660542392322373)
      ·
        refine ⟨6786858336686351698560445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36196577795660542392322373 6786858336686351698560445)
        ·
          refine ⟨2545071876257381886960167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6786858336686351698560445 2545071876257381886960167)
          ·
            refine ⟨3817607814386072830440251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545071876257381886960167 3817607814386072830440251)
            ·
              refine ⟨5726411721579109245660377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817607814386072830440251 5726411721579109245660377)
              ·
                refine ⟨4294808791184331934245283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5726411721579109245660377 4294808791184331934245283)
                ·
                  refine ⟨6442213186776497901367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294808791184331934245283 6442213186776497901367925)
                  ·
                    refine ⟨603957486260296678253243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6442213186776497901367925 603957486260296678253243)
                    ·
                      rfl

theorem cell23_3528609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3528609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528609 prefixEnd_3528609 := by exact prefixLift 3528609
  have htrace : WordTrace (prefixWord ++ tailWord_3528609) baseStart_3528609 baseEnd_3528609 := by
    simpa [prefixWord, tailWord_3528609, baseEnd_3528609] using wordTrace_append hprefix tailTrace_3528609
  have hstable : (prefixWord ++ tailWord_3528609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528609).length < 2 ^ (prefixWord ++ tailWord_3528609).sum := by decide
  have hdescent : baseEnd_3528609 < baseStart_3528609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528612 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_3528612 : Nat := 118140960795 + 3528612 * 2 ^ 59
def prefixEnd_3528612 : Nat := 4983230072969 + 3 ^ 40 * 3528612 * 2
def baseEnd_3528612 : Nat := 1811873999222853523022215

theorem tailTrace_3528612 : CollatzResearch.WordTrace tailWord_3528612 prefixEnd_3528612 1811873999222853523022215 := by
  unfold tailWord_3528612
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349526346224418898086045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85799368461632558530781393 64349526346224418898086045)
  ·
    refine ⟨24131072379834157086782267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64349526346224418898086045 24131072379834157086782267)
    ·
      refine ⟨36196608569751235630173401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24131072379834157086782267 36196608569751235630173401)
      ·
        refine ⟨27147456427313426722630051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36196608569751235630173401 27147456427313426722630051)
        ·
          refine ⟨40721184640970140083945077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27147456427313426722630051 40721184640970140083945077)
          ·
            refine ⟨3817611060090950632869851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40721184640970140083945077 3817611060090950632869851)
            ·
              refine ⟨5726416590136425949304777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817611060090950632869851 5726416590136425949304777)
              ·
                refine ⟨4294812442602319461978583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5726416590136425949304777 4294812442602319461978583)
                ·
                  refine ⟨6442218663903479192967875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294812442602319461978583 6442218663903479192967875)
                  ·
                    refine ⟨9663327995855218789451813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442218663903479192967875 9663327995855218789451813)
                    ·
                      refine ⟨1811873999222853523022215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663327995855218789451813 1811873999222853523022215)
                      ·
                        rfl

theorem cell23_3528612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_3528612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528612 prefixEnd_3528612 := by exact prefixLift 3528612
  have htrace : WordTrace (prefixWord ++ tailWord_3528612) baseStart_3528612 baseEnd_3528612 := by
    simpa [prefixWord, tailWord_3528612, baseEnd_3528612] using wordTrace_append hprefix tailTrace_3528612
  have hstable : (prefixWord ++ tailWord_3528612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528612).length < 2 ^ (prefixWord ++ tailWord_3528612).sum := by decide
  have hdescent : baseEnd_3528612 < baseStart_3528612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528616 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3528616 : Nat := 118140960795 + 3528616 * 2 ^ 59
def prefixEnd_3528616 : Nat := 4983230072969 + 3 ^ 40 * 3528616 * 2
def baseEnd_3528616 : Nat := 1811876053145471507372197

theorem tailTrace_3528616 : CollatzResearch.WordTrace tailWord_3528616 prefixEnd_3528616 1811876053145471507372197 := by
  unfold tailWord_3528616
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349599292217173239658851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85799465722956230986211801 64349599292217173239658851)
  ·
    refine ⟨96524398938325759859488277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64349599292217173239658851 96524398938325759859488277)
    ·
      refine ⟨4524581200234019993413513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96524398938325759859488277 4524581200234019993413513)
      ·
        refine ⟨3393435900175514995060135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4524581200234019993413513 3393435900175514995060135)
        ·
          refine ⟨5090153850263272492590203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393435900175514995060135 5090153850263272492590203)
          ·
            refine ⟨7635230775394908738885305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090153850263272492590203 7635230775394908738885305)
            ·
              refine ⟨5726423081546181554163979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635230775394908738885305 5726423081546181554163979)
              ·
                refine ⟨8589634622319272331245969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726423081546181554163979 8589634622319272331245969)
                ·
                  refine ⟨6442225966739454248434477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589634622319272331245969 6442225966739454248434477)
                  ·
                    refine ⟨2415834737527295343162929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442225966739454248434477 2415834737527295343162929)
                    ·
                      refine ⟨1811876053145471507372197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415834737527295343162929 1811876053145471507372197)
                      ·
                        rfl

theorem cell23_3528616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3528616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528616 prefixEnd_3528616 := by exact prefixLift 3528616
  have htrace : WordTrace (prefixWord ++ tailWord_3528616) baseStart_3528616 baseEnd_3528616 := by
    simpa [prefixWord, tailWord_3528616, baseEnd_3528616] using wordTrace_append hprefix tailTrace_3528616
  have hstable : (prefixWord ++ tailWord_3528616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528616).length < 2 ^ (prefixWord ++ tailWord_3528616).sum := by decide
  have hdescent : baseEnd_3528616 < baseStart_3528616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528625 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3528625 : Nat := 118140960795 + 3528625 * 2 ^ 59
def prefixEnd_3528625 : Nat := 4983230072969 + 3 ^ 40 * 3528625 * 2
def baseEnd_3528625 : Nat := 1811880674471361972159655

theorem tailTrace_3528625 : CollatzResearch.WordTrace tailWord_3528625 prefixEnd_3528625 1811880674471361972159655 := by
  unfold tailWord_3528625
  simp only [CollatzResearch.WordTrace]
  refine ⟨128699526841401741016395329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85799684560934494010930219 128699526841401741016395329)
  ·
    refine ⟨96524645131051305762296497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128699526841401741016395329 96524645131051305762296497)
    ·
      refine ⟨72393483848288479321722373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96524645131051305762296497 72393483848288479321722373)
      ·
        refine ⟨13573778221554089872822945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72393483848288479321722373 13573778221554089872822945)
        ·
          refine ⟨10180333666165567404617209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13573778221554089872822945 10180333666165567404617209)
          ·
            refine ⟨7635250249624175553462907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10180333666165567404617209 7635250249624175553462907)
            ·
              refine ⟨11452875374436263330194361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635250249624175553462907 11452875374436263330194361)
              ·
                refine ⟨8589656530827197497645771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11452875374436263330194361 8589656530827197497645771)
                ·
                  refine ⟨12884484796240796246468657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589656530827197497645771 12884484796240796246468657)
                  ·
                    refine ⟨9663363597180597184851493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12884484796240796246468657 9663363597180597184851493)
                    ·
                      refine ⟨1811880674471361972159655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663363597180597184851493 1811880674471361972159655)
                      ·
                        rfl

theorem cell23_3528625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3528625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528625 prefixEnd_3528625 := by exact prefixLift 3528625
  have htrace : WordTrace (prefixWord ++ tailWord_3528625) baseStart_3528625 baseEnd_3528625 := by
    simpa [prefixWord, tailWord_3528625, baseEnd_3528625] using wordTrace_append hprefix tailTrace_3528625
  have hstable : (prefixWord ++ tailWord_3528625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528625).length < 2 ^ (prefixWord ++ tailWord_3528625).sum := by decide
  have hdescent : baseEnd_3528625 < baseStart_3528625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528632 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_3528632 : Nat := 118140960795 + 3528632 * 2 ^ 59
def prefixEnd_3528632 : Nat := 4983230072969 + 3 ^ 40 * 3528632 * 2
def baseEnd_3528632 : Nat := 1811884268835943444772123

theorem tailTrace_3528632 : CollatzResearch.WordTrace tailWord_3528632 prefixEnd_3528632 1811884268835943444772123 := by
  unfold tailWord_3528632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349891076188190605950075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85799854768250920807933433 64349891076188190605950075)
  ·
    refine ⟨96524836614282285908925113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64349891076188190605950075 96524836614282285908925113)
    ·
      refine ⟨72393627460711714431693835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96524836614282285908925113 72393627460711714431693835)
      ·
        refine ⟨108590441191067571647540753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72393627460711714431693835 108590441191067571647540753)
        ·
          refine ⟨81442830893300678735655565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108590441191067571647540753 81442830893300678735655565)
          ·
            refine ⟨30541061584987754525870837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81442830893300678735655565 30541061584987754525870837)
            ·
              refine ⟨2863224523592601986800391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30541061584987754525870837 2863224523592601986800391)
              ·
                refine ⟨4294836785388902980200587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863224523592601986800391 4294836785388902980200587)
                ·
                  refine ⟨6442255178083354470300881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294836785388902980200587 6442255178083354470300881)
                  ·
                    refine ⟨4831691383562515852725661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442255178083354470300881 4831691383562515852725661)
                    ·
                      refine ⟨1811884268835943444772123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831691383562515852725661 1811884268835943444772123)
                      ·
                        rfl

theorem cell23_3528632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_3528632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528632 prefixEnd_3528632 := by exact prefixLift 3528632
  have htrace : WordTrace (prefixWord ++ tailWord_3528632) baseStart_3528632 baseEnd_3528632 := by
    simpa [prefixWord, tailWord_3528632, baseEnd_3528632] using wordTrace_append hprefix tailTrace_3528632
  have hstable : (prefixWord ++ tailWord_3528632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528632).length < 2 ^ (prefixWord ++ tailWord_3528632).sum := by decide
  have hdescent : baseEnd_3528632 < baseStart_3528632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528648 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_3528648 : Nat := 118140960795 + 3528648 * 2 ^ 59
def prefixEnd_3528648 : Nat := 4983230072969 + 3 ^ 40 * 3528648 * 2
def baseEnd_3528648 : Nat := 603964161508805127390683

theorem tailTrace_3528648 : CollatzResearch.WordTrace tailWord_3528648 prefixEnd_3528648 603964161508805127390683 := by
  unfold tailWord_3528648
  simp only [CollatzResearch.WordTrace]
  refine ⟨64350182860159207972241299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85800243813545610629655065 64350182860159207972241299)
  ·
    refine ⟨96525274290238811958361949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64350182860159207972241299 96525274290238811958361949)
    ·
      refine ⟨36196977858839554484385731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96525274290238811958361949 36196977858839554484385731)
      ·
        refine ⟨54295466788259331726578597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36196977858839554484385731 54295466788259331726578597)
        ·
          refine ⟨10180400022798624698733487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54295466788259331726578597 10180400022798624698733487)
          ·
            refine ⟨15270600034197937048100231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10180400022798624698733487 15270600034197937048100231)
            ·
              refine ⟨22905900051296905572150347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270600034197937048100231 22905900051296905572150347)
              ·
                refine ⟨34358850076945358358225521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22905900051296905572150347 34358850076945358358225521)
                ·
                  refine ⟨25769137557709018768669141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34358850076945358358225521 25769137557709018768669141)
                  ·
                    refine ⟨603964161508805127390683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25769137557709018768669141 603964161508805127390683)
                    ·
                      rfl

theorem cell23_3528648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_3528648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528648 prefixEnd_3528648 := by exact prefixLift 3528648
  have htrace : WordTrace (prefixWord ++ tailWord_3528648) baseStart_3528648 baseEnd_3528648 := by
    simpa [prefixWord, tailWord_3528648, baseEnd_3528648] using wordTrace_append hprefix tailTrace_3528648
  have hstable : (prefixWord ++ tailWord_3528648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528648).length < 2 ^ (prefixWord ++ tailWord_3528648).sum := by decide
  have hdescent : baseEnd_3528648 < baseStart_3528648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528655 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 5, 3, 2]
def baseStart_3528655 : Nat := 118140960795 + 3528655 * 2 ^ 59
def prefixEnd_3528655 : Nat := 4983230072969 + 3 ^ 40 * 3528655 * 2
def baseEnd_3528655 : Nat := 1811896078890996854784517

theorem tailTrace_3528655 : CollatzResearch.WordTrace tailWord_3528655 prefixEnd_3528655 1811896078890996854784517 := by
  unfold tailWord_3528655
  simp only [CollatzResearch.WordTrace]
  refine ⟨128700621031293056139987419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85800414020862037426658279 128700621031293056139987419)
  ·
    refine ⟨193050931546939584209981129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128700621031293056139987419 193050931546939584209981129)
    ·
      refine ⟨144788198660204688157485847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193050931546939584209981129 144788198660204688157485847)
      ·
        refine ⟨217182297990307032236228771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144788198660204688157485847 217182297990307032236228771)
        ·
          refine ⟨325773446985460548354343157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217182297990307032236228771 325773446985460548354343157)
          ·
            refine ⟨30541260654886926408219671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 325773446985460548354343157 30541260654886926408219671)
            ·
              refine ⟨45811890982330389612329507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30541260654886926408219671 45811890982330389612329507)
              ·
                refine ⟨68717836473495584418494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45811890982330389612329507 68717836473495584418494261)
                ·
                  refine ⟨6442297169390211039233837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68717836473495584418494261 6442297169390211039233837)
                  ·
                    refine ⟨2415861438521329139712689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442297169390211039233837 2415861438521329139712689)
                    ·
                      refine ⟨1811896078890996854784517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415861438521329139712689 1811896078890996854784517)
                      ·
                        rfl

theorem cell23_3528655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3, 2].length) (baseStart_3528655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528655 prefixEnd_3528655 := by exact prefixLift 3528655
  have htrace : WordTrace (prefixWord ++ tailWord_3528655) baseStart_3528655 baseEnd_3528655 := by
    simpa [prefixWord, tailWord_3528655, baseEnd_3528655] using wordTrace_append hprefix tailTrace_3528655
  have hstable : (prefixWord ++ tailWord_3528655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528655).length < 2 ^ (prefixWord ++ tailWord_3528655).sum := by decide
  have hdescent : baseEnd_3528655 < baseStart_3528655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528688 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_3528688 : Nat := 118140960795 + 3528688 * 2 ^ 59
def prefixEnd_3528688 : Nat := 4983230072969 + 3 ^ 40 * 3528688 * 2
def baseEnd_3528688 : Nat := 1811913023752595225671865

theorem tailTrace_3528688 : CollatzResearch.WordTrace tailWord_3528688 prefixEnd_3528688 1811913023752595225671865 := by
  unfold tailWord_3528688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64350912320086751387969359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85801216426782335183959145 64350912320086751387969359)
  ·
    refine ⟨96526368480130127081954039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64350912320086751387969359 96526368480130127081954039)
    ·
      refine ⟨144789552720195190622931059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96526368480130127081954039 144789552720195190622931059)
      ·
        refine ⟨217184329080292785934396589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144789552720195190622931059 217184329080292785934396589)
        ·
          refine ⟨81444123405109794725398721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217184329080292785934396589 81444123405109794725398721)
          ·
            refine ⟨61083092553832346044049041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81444123405109794725398721 61083092553832346044049041)
            ·
              refine ⟨45812319415374259533036781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61083092553832346044049041 45812319415374259533036781)
              ·
                refine ⟨17179619780765347324888793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45812319415374259533036781 17179619780765347324888793)
                ·
                  refine ⟨12884714835574010493666595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17179619780765347324888793 12884714835574010493666595)
                  ·
                    refine ⟨19327072253361015740499893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884714835574010493666595 19327072253361015740499893)
                    ·
                      refine ⟨1811913023752595225671865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19327072253361015740499893 1811913023752595225671865)
                      ·
                        rfl

theorem cell23_3528688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_3528688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528688 prefixEnd_3528688 := by exact prefixLift 3528688
  have htrace : WordTrace (prefixWord ++ tailWord_3528688) baseStart_3528688 baseEnd_3528688 := by
    simpa [prefixWord, tailWord_3528688, baseEnd_3528688] using wordTrace_append hprefix tailTrace_3528688
  have hstable : (prefixWord ++ tailWord_3528688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528688).length < 2 ^ (prefixWord ++ tailWord_3528688).sum := by decide
  have hdescent : baseEnd_3528688 < baseStart_3528688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528689 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_3528689 : Nat := 118140960795 + 3528689 * 2 ^ 59
def prefixEnd_3528689 : Nat := 4983230072969 + 3 ^ 40 * 3528689 * 2
def baseEnd_3528689 : Nat := 1811913537233249721759361

theorem tailTrace_3528689 : CollatzResearch.WordTrace tailWord_3528689 prefixEnd_3528689 1811913537233249721759361 := by
  unfold tailWord_3528689
  simp only [CollatzResearch.WordTrace]
  refine ⟨128701861113169879946725121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85801240742113253297816747 128701861113169879946725121)
  ·
    refine ⟨96526395834877409960043841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128701861113169879946725121 96526395834877409960043841)
    ·
      refine ⟨72394796876158057470032881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96526395834877409960043841 72394796876158057470032881)
      ·
        refine ⟨54296097657118543102524661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72394796876158057470032881 54296097657118543102524661)
        ·
          refine ⟨5090259155354863415861687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54296097657118543102524661 5090259155354863415861687)
          ·
            refine ⟨7635388733032295123792531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090259155354863415861687 7635388733032295123792531)
            ·
              refine ⟨11453083099548442685688797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635388733032295123792531 11453083099548442685688797)
              ·
                refine ⟨4294906162330666007133299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11453083099548442685688797 4294906162330666007133299)
                ·
                  refine ⟨6442359243495999010699949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294906162330666007133299 6442359243495999010699949)
                  ·
                    refine ⟨2415884716310999629012481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442359243495999010699949 2415884716310999629012481)
                    ·
                      refine ⟨1811913537233249721759361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2415884716310999629012481 1811913537233249721759361)
                      ·
                        rfl

theorem cell23_3528689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_3528689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528689 prefixEnd_3528689 := by exact prefixLift 3528689
  have htrace : WordTrace (prefixWord ++ tailWord_3528689) baseStart_3528689 baseEnd_3528689 := by
    simpa [prefixWord, tailWord_3528689, baseEnd_3528689] using wordTrace_append hprefix tailTrace_3528689
  have hstable : (prefixWord ++ tailWord_3528689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528689).length < 2 ^ (prefixWord ++ tailWord_3528689).sum := by decide
  have hdescent : baseEnd_3528689 < baseStart_3528689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528710 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3528710 : Nat := 118140960795 + 3528710 * 2 ^ 59
def prefixEnd_3528710 : Nat := 4983230072969 + 3 ^ 40 * 3528710 * 2
def baseEnd_3528710 : Nat := 1811924320326994139596765

theorem tailTrace_3528710 : CollatzResearch.WordTrace tailWord_3528710 prefixEnd_3528710 1811924320326994139596765 := by
  unfold tailWord_3528710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021957095190431266663737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85801751364062533688826389 4021957095190431266663737)
  ·
    refine ⟨3016467821392823449997803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4021957095190431266663737 3016467821392823449997803)
    ·
      refine ⟨4524701732089235174996705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016467821392823449997803 4524701732089235174996705)
      ·
        refine ⟨3393526299066926381247529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4524701732089235174996705 3393526299066926381247529)
        ·
          refine ⟨2545144724300194785935647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3393526299066926381247529 2545144724300194785935647)
          ·
            refine ⟨3817717086450292178903471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545144724300194785935647 3817717086450292178903471)
            ·
              refine ⟨5726575629675438268355207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817717086450292178903471 5726575629675438268355207)
              ·
                refine ⟨8589863444513157402532811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726575629675438268355207 8589863444513157402532811)
                ·
                  refine ⟨12884795166769736103799217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589863444513157402532811 12884795166769736103799217)
                  ·
                    refine ⟨9663596375077302077849413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12884795166769736103799217 9663596375077302077849413)
                    ·
                      refine ⟨1811924320326994139596765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663596375077302077849413 1811924320326994139596765)
                      ·
                        rfl

theorem cell23_3528710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3528710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528710 prefixEnd_3528710 := by exact prefixLift 3528710
  have htrace : WordTrace (prefixWord ++ tailWord_3528710) baseStart_3528710 baseEnd_3528710 := by
    simpa [prefixWord, tailWord_3528710, baseEnd_3528710] using wordTrace_append hprefix tailTrace_3528710
  have hstable : (prefixWord ++ tailWord_3528710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528710).length < 2 ^ (prefixWord ++ tailWord_3528710).sum := by decide
  have hdescent : baseEnd_3528710 < baseStart_3528710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528765 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3528765 : Nat := 118140960795 + 3528765 * 2 ^ 59
def prefixEnd_3528765 : Nat := 4983230072969 + 3 ^ 40 * 3528765 * 2
def baseEnd_3528765 : Nat := 1811952561762991424409011

theorem tailTrace_3528765 : CollatzResearch.WordTrace tailWord_3528765 prefixEnd_3528765 1811952561762991424409011 := by
  unfold tailWord_3528765
  simp only [CollatzResearch.WordTrace]
  refine ⟨128704633060894544926491749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85803088707263029950994499 128704633060894544926491749)
  ·
    refine ⟨24132118698917727173717203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128704633060894544926491749 24132118698917727173717203)
    ·
      refine ⟨36198178048376590760575805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132118698917727173717203 36198178048376590760575805)
      ·
        refine ⟨13574316768141221535215927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36198178048376590760575805 13574316768141221535215927)
        ·
          refine ⟨20361475152211832302823891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574316768141221535215927 20361475152211832302823891)
          ·
            refine ⟨30542212728317748454235837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20361475152211832302823891 30542212728317748454235837)
            ·
              refine ⟨11453329773119155670338439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30542212728317748454235837 11453329773119155670338439)
              ·
                refine ⟨17179994659678733505507659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11453329773119155670338439 17179994659678733505507659)
                ·
                  refine ⟨25769991989518100258261489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17179994659678733505507659 25769991989518100258261489)
                  ·
                    refine ⟨19327493992138575193696117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25769991989518100258261489 19327493992138575193696117)
                    ·
                      refine ⟨1811952561762991424409011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19327493992138575193696117 1811952561762991424409011)
                      ·
                        rfl

theorem cell23_3528765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3528765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528765 prefixEnd_3528765 := by exact prefixLift 3528765
  have htrace : WordTrace (prefixWord ++ tailWord_3528765) baseStart_3528765 baseEnd_3528765 := by
    simpa [prefixWord, tailWord_3528765, baseEnd_3528765] using wordTrace_append hprefix tailTrace_3528765
  have hstable : (prefixWord ++ tailWord_3528765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528765).length < 2 ^ (prefixWord ++ tailWord_3528765).sum := by decide
  have hdescent : baseEnd_3528765 < baseStart_3528765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528775 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3528775 : Nat := 118140960795 + 3528775 * 2 ^ 59
def prefixEnd_3528775 : Nat := 4983230072969 + 3 ^ 40 * 3528775 * 2
def baseEnd_3528775 : Nat := 1811957696569536385283965

theorem tailTrace_3528775 : CollatzResearch.WordTrace tailWord_3528775 prefixEnd_3528775 1811957696569536385283965 := by
  unfold tailWord_3528775
  simp only [CollatzResearch.WordTrace]
  refine ⟨128704997790858316634355779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85803331860572211089570519 128704997790858316634355779)
  ·
    refine ⟨193057496686287474951533669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128704997790858316634355779 193057496686287474951533669)
    ·
      refine ⟨36198280628678901553412563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193057496686287474951533669 36198280628678901553412563)
      ·
        refine ⟨54297420943018352330118845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36198280628678901553412563 54297420943018352330118845)
        ·
          refine ⟨20361532853631882123794567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54297420943018352330118845 20361532853631882123794567)
          ·
            refine ⟨30542299280447823185691851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20361532853631882123794567 30542299280447823185691851)
            ·
              refine ⟨45813448920671734778537777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30542299280447823185691851 45813448920671734778537777)
              ·
                refine ⟨34360086690503801083903333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45813448920671734778537777 34360086690503801083903333)
                ·
                  refine ⟨6442516254469462703231875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34360086690503801083903333 6442516254469462703231875)
                  ·
                    refine ⟨9663774381704194054847813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442516254469462703231875 9663774381704194054847813)
                    ·
                      refine ⟨1811957696569536385283965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663774381704194054847813 1811957696569536385283965)
                      ·
                        rfl

theorem cell23_3528775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3528775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528775 prefixEnd_3528775 := by exact prefixLift 3528775
  have htrace : WordTrace (prefixWord ++ tailWord_3528775) baseStart_3528775 baseEnd_3528775 := by
    simpa [prefixWord, tailWord_3528775, baseEnd_3528775] using wordTrace_append hprefix tailTrace_3528775
  have hstable : (prefixWord ++ tailWord_3528775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528775).length < 2 ^ (prefixWord ++ tailWord_3528775).sum := by decide
  have hdescent : baseEnd_3528775 < baseStart_3528775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528785 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3528785 : Nat := 118140960795 + 3528785 * 2 ^ 59
def prefixEnd_3528785 : Nat := 4983230072969 + 3 ^ 40 * 3528785 * 2
def baseEnd_3528785 : Nat := 603987610458693782052973

theorem tailTrace_3528785 : CollatzResearch.WordTrace tailWord_3528785 prefixEnd_3528785 603987610458693782052973 := by
  unfold tailWord_3528785
  simp only [CollatzResearch.WordTrace]
  refine ⟨128705362520822088342219809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85803575013881392228146539 128705362520822088342219809)
  ·
    refine ⟨96529021890616566256664857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128705362520822088342219809 96529021890616566256664857)
    ·
      refine ⟨72396766417962424692498643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96529021890616566256664857 72396766417962424692498643)
      ·
        refine ⟨108595149626943637038747965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72396766417962424692498643 108595149626943637038747965)
        ·
          refine ⟨40723181110103863889530487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108595149626943637038747965 40723181110103863889530487)
          ·
            refine ⟨61084771665155795834295731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40723181110103863889530487 61084771665155795834295731)
            ·
              refine ⟨91627157497733693751443597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61084771665155795834295731 91627157497733693751443597)
              ·
                refine ⟨34360184061650135156791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91627157497733693751443597 34360184061650135156791349)
                ·
                  refine ⟨3221267255779700170949189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34360184061650135156791349 3221267255779700170949189)
                  ·
                    refine ⟨603987610458693782052973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221267255779700170949189 603987610458693782052973)
                    ·
                      rfl

theorem cell23_3528785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3528785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528785 prefixEnd_3528785 := by exact prefixLift 3528785
  have htrace : WordTrace (prefixWord ++ tailWord_3528785) baseStart_3528785 baseEnd_3528785 := by
    simpa [prefixWord, tailWord_3528785, baseEnd_3528785] using wordTrace_append hprefix tailTrace_3528785
  have hstable : (prefixWord ++ tailWord_3528785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528785).length < 2 ^ (prefixWord ++ tailWord_3528785).sum := by decide
  have hdescent : baseEnd_3528785 < baseStart_3528785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528792 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3528792 : Nat := 118140960795 + 3528792 * 2 ^ 59
def prefixEnd_3528792 : Nat := 4983230072969 + 3 ^ 40 * 3528792 * 2
def baseEnd_3528792 : Nat := 1811966425740662818771387

theorem tailTrace_3528792 : CollatzResearch.WordTrace tailWord_3528792 prefixEnd_3528792 1811966425740662818771387 := by
  unfold tailWord_3528792
  simp only [CollatzResearch.WordTrace]
  refine ⟨64352808915898364268862315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85803745221197819025149753 64352808915898364268862315)
  ·
    refine ⟨96529213373847546403293473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64352808915898364268862315 96529213373847546403293473)
    ·
      refine ⟨72396910030385659802470105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96529213373847546403293473 72396910030385659802470105)
      ·
        refine ⟨54297682522789244851852579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72396910030385659802470105 54297682522789244851852579)
        ·
          refine ⟨81446523784183867277778869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54297682522789244851852579 81446523784183867277778869)
          ·
            refine ⟨7635611604767237557291769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81446523784183867277778869 7635611604767237557291769)
            ·
              refine ⟨5726708703575428167968827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635611604767237557291769 5726708703575428167968827)
              ·
                refine ⟨8590063055363142251953241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726708703575428167968827 8590063055363142251953241)
                ·
                  refine ⟨6442547291522356688964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590063055363142251953241 6442547291522356688964931)
                  ·
                    refine ⟨9663820937283535033447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442547291522356688964931 9663820937283535033447397)
                    ·
                      refine ⟨1811966425740662818771387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9663820937283535033447397 1811966425740662818771387)
                      ·
                        rfl

theorem cell23_3528792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3528792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528792 prefixEnd_3528792 := by exact prefixLift 3528792
  have htrace : WordTrace (prefixWord ++ tailWord_3528792) baseStart_3528792 baseEnd_3528792 := by
    simpa [prefixWord, tailWord_3528792, baseEnd_3528792] using wordTrace_append hprefix tailTrace_3528792
  have hstable : (prefixWord ++ tailWord_3528792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528792).length < 2 ^ (prefixWord ++ tailWord_3528792).sum := by decide
  have hdescent : baseEnd_3528792 < baseStart_3528792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528812 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_3528812 : Nat := 118140960795 + 3528812 * 2 ^ 59
def prefixEnd_3528812 : Nat := 4983230072969 + 3 ^ 40 * 3528812 * 2
def baseEnd_3528812 : Nat := 1811976695353752740521295

theorem tailTrace_3528812 : CollatzResearch.WordTrace tailWord_3528812 prefixEnd_3528812 1811976695353752740521295 := by
  unfold tailWord_3528812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64353173645862135976726345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85804231527816181302301793 64353173645862135976726345)
  ·
    refine ⟨48264880234396601982544759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64353173645862135976726345 48264880234396601982544759)
    ·
      refine ⟨72397320351594902973817139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48264880234396601982544759 72397320351594902973817139)
      ·
        refine ⟨108595980527392354460725709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72397320351594902973817139 108595980527392354460725709)
        ·
          refine ⟨40723492697772132922772141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108595980527392354460725709 40723492697772132922772141)
          ·
            refine ⟨15271309761664549846039553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40723492697772132922772141 15271309761664549846039553)
            ·
              refine ⟨11453482321248412384529665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15271309761664549846039553 11453482321248412384529665)
              ·
                refine ⟨8590111740936309288397249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11453482321248412384529665 8590111740936309288397249)
                ·
                  refine ⟨6442583805702231966297937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590111740936309288397249 6442583805702231966297937)
                  ·
                    refine ⟨4831937854276673974723453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442583805702231966297937 4831937854276673974723453)
                    ·
                      refine ⟨1811976695353752740521295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831937854276673974723453 1811976695353752740521295)
                      ·
                        rfl

theorem cell23_3528812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_3528812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528812 prefixEnd_3528812 := by exact prefixLift 3528812
  have htrace : WordTrace (prefixWord ++ tailWord_3528812) baseStart_3528812 baseEnd_3528812 := by
    simpa [prefixWord, tailWord_3528812, baseEnd_3528812] using wordTrace_append hprefix tailTrace_3528812
  have hstable : (prefixWord ++ tailWord_3528812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528812).length < 2 ^ (prefixWord ++ tailWord_3528812).sum := by decide
  have hdescent : baseEnd_3528812 < baseStart_3528812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528815 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 6]
def baseStart_3528815 : Nat := 118140960795 + 3528815 * 2 ^ 59
def prefixEnd_3528815 : Nat := 4983230072969 + 3 ^ 40 * 3528815 * 2
def baseEnd_3528815 : Nat := 201330915088412914309309

theorem tailTrace_3528815 : CollatzResearch.WordTrace tailWord_3528815 prefixEnd_3528815 201330915088412914309309 := by
  unfold tailWord_3528815
  simp only [CollatzResearch.WordTrace]
  refine ⟨128706456710713403465811899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85804304473808935643874599 128706456710713403465811899)
  ·
    refine ⟨193059685066070105198717849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128706456710713403465811899 193059685066070105198717849)
    ·
      refine ⟨144794763799552578899038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193059685066070105198717849 144794763799552578899038387)
      ·
        refine ⟨217192145699328868348557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144794763799552578899038387 217192145699328868348557581)
        ·
          refine ⟨81447054637248325630709093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217192145699328868348557581 81447054637248325630709093)
          ·
            refine ⟨15271322744484061055757955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81447054637248325630709093 15271322744484061055757955)
            ·
              refine ⟨22906984116726091583636933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15271322744484061055757955 22906984116726091583636933)
              ·
                refine ⟨4295059521886142171931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22906984116726091583636933 4295059521886142171931925)
                ·
                  refine ⟨201330915088412914309309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4295059521886142171931925 201330915088412914309309)
                  ·
                    rfl

theorem cell23_3528815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 6].length) (baseStart_3528815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528815 prefixEnd_3528815 := by exact prefixLift 3528815
  have htrace : WordTrace (prefixWord ++ tailWord_3528815) baseStart_3528815 baseEnd_3528815 := by
    simpa [prefixWord, tailWord_3528815, baseEnd_3528815] using wordTrace_append hprefix tailTrace_3528815
  have hstable : (prefixWord ++ tailWord_3528815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528815).length < 2 ^ (prefixWord ++ tailWord_3528815).sum := by decide
  have hdescent : baseEnd_3528815 < baseStart_3528815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528846 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3528846 : Nat := 118140960795 + 3528846 * 2 ^ 59
def prefixEnd_3528846 : Nat := 4983230072969 + 3 ^ 40 * 3528846 * 2
def baseEnd_3528846 : Nat := 1811994153696005607496139

theorem tailTrace_3528846 : CollatzResearch.WordTrace tailWord_3528846 prefixEnd_3528846 1811994153696005607496139 := by
  unfold tailWord_3528846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088448421700136970023799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85805058249067397173460261 16088448421700136970023799)
  ·
    refine ⟨24132672632550205455035699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16088448421700136970023799 24132672632550205455035699)
    ·
      refine ⟨36199008948825308182553549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132672632550205455035699 36199008948825308182553549)
      ·
        refine ⟨13574628355809490568457581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36199008948825308182553549 13574628355809490568457581)
        ·
          refine ⟨5090485633428558963171593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13574628355809490568457581 5090485633428558963171593)
          ·
            refine ⟨3817864225071419222378695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090485633428558963171593 3817864225071419222378695)
            ·
              refine ⟨5726796337607128833568043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817864225071419222378695 5726796337607128833568043)
              ·
                refine ⟨8590194506410693250352065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726796337607128833568043 8590194506410693250352065)
                ·
                  refine ⟨6442645879808019937764049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590194506410693250352065 6442645879808019937764049)
                  ·
                    refine ⟨4831984409856014953323037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442645879808019937764049 4831984409856014953323037)
                    ·
                      refine ⟨1811994153696005607496139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4831984409856014953323037 1811994153696005607496139)
                      ·
                        rfl

theorem cell23_3528846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3528846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528846 prefixEnd_3528846 := by exact prefixLift 3528846
  have htrace : WordTrace (prefixWord ++ tailWord_3528846) baseStart_3528846 baseEnd_3528846 := by
    simpa [prefixWord, tailWord_3528846, baseEnd_3528846] using wordTrace_append hprefix tailTrace_3528846
  have hstable : (prefixWord ++ tailWord_3528846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528846).length < 2 ^ (prefixWord ++ tailWord_3528846).sum := by decide
  have hdescent : baseEnd_3528846 < baseStart_3528846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528933 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3528933 : Nat := 118140960795 + 3528933 * 2 ^ 59
def prefixEnd_3528933 : Nat := 4983230072969 + 3 ^ 40 * 3528933 * 2
def baseEnd_3528933 : Nat := 1812038826512946767108239

theorem tailTrace_3528933 : CollatzResearch.WordTrace tailWord_3528933 prefixEnd_3528933 1812038826512946767108239 := by
  unfold tailWord_3528933
  simp only [CollatzResearch.WordTrace]
  refine ⟨128710760524285909618607453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85807173682857273079071635 128710760524285909618607453)
  ·
    refine ⟨48266535196607216106977795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128710760524285909618607453 48266535196607216106977795)
    ·
      refine ⟨72399802794910824160466693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48266535196607216106977795 72399802794910824160466693)
      ·
        refine ⟨13574963024045779530087505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72399802794910824160466693 13574963024045779530087505)
        ·
          refine ⟨10181222268034334647565629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13574963024045779530087505 10181222268034334647565629)
          ·
            refine ⟨3817958350512875492837111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10181222268034334647565629 3817958350512875492837111)
            ·
              refine ⟨5726937525769313239255667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817958350512875492837111 5726937525769313239255667)
              ·
                refine ⟨8590406288653969858883501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726937525769313239255667 8590406288653969858883501)
                ·
                  refine ⟨3221402358245238697081313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8590406288653969858883501 3221402358245238697081313)
                  ·
                    refine ⟨2416051768683929022810985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3221402358245238697081313 2416051768683929022810985)
                    ·
                      refine ⟨1812038826512946767108239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416051768683929022810985 1812038826512946767108239)
                      ·
                        rfl

theorem cell23_3528933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3528933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528933 prefixEnd_3528933 := by exact prefixLift 3528933
  have htrace : WordTrace (prefixWord ++ tailWord_3528933) baseStart_3528933 baseEnd_3528933 := by
    simpa [prefixWord, tailWord_3528933, baseEnd_3528933] using wordTrace_append hprefix tailTrace_3528933
  have hstable : (prefixWord ++ tailWord_3528933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528933).length < 2 ^ (prefixWord ++ tailWord_3528933).sum := by decide
  have hdescent : baseEnd_3528933 < baseStart_3528933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528959 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 3, 3, 2]
def baseStart_3528959 : Nat := 118140960795 + 3528959 * 2 ^ 59
def prefixEnd_3528959 : Nat := 4983230072969 + 3 ^ 40 * 3528959 * 2
def baseEnd_3528959 : Nat := 1812052177009963665383119

theorem tailTrace_3528959 : CollatzResearch.WordTrace tailWord_3528959 prefixEnd_3528959 1812052177009963665383119 := by
  unfold tailWord_3528959
  simp only [CollatzResearch.WordTrace]
  refine ⟨128711708822191716059053931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85807805881461144039369287 128711708822191716059053931)
  ·
    refine ⟨193067563233287574088580897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128711708822191716059053931 193067563233287574088580897)
    ·
      refine ⟨144800672424965680566435673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193067563233287574088580897 144800672424965680566435673)
      ·
        refine ⟨108600504318724260424826755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144800672424965680566435673 108600504318724260424826755)
        ·
          refine ⟨162900756478086390637240133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108600504318724260424826755 162900756478086390637240133)
          ·
            refine ⟨30543891839641198244482525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162900756478086390637240133 30543891839641198244482525)
            ·
              refine ⟨11453959439865449341680947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30543891839641198244482525 11453959439865449341680947)
              ·
                refine ⟨17180939159798174012521421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11453959439865449341680947 17180939159798174012521421)
                ·
                  refine ⟨6442852184924315254695533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17180939159798174012521421 6442852184924315254695533)
                  ·
                    refine ⟨2416069569346618220510825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6442852184924315254695533 2416069569346618220510825)
                    ·
                      refine ⟨1812052177009963665383119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416069569346618220510825 1812052177009963665383119)
                      ·
                        rfl

theorem cell23_3528959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_3528959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528959 prefixEnd_3528959 := by exact prefixLift 3528959
  have htrace : WordTrace (prefixWord ++ tailWord_3528959) baseStart_3528959 baseEnd_3528959 := by
    simpa [prefixWord, tailWord_3528959, baseEnd_3528959] using wordTrace_append hprefix tailTrace_3528959
  have hstable : (prefixWord ++ tailWord_3528959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528959).length < 2 ^ (prefixWord ++ tailWord_3528959).sum := by decide
  have hdescent : baseEnd_3528959 < baseStart_3528959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528965 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_3528965 : Nat := 118140960795 + 3528965 * 2 ^ 59
def prefixEnd_3528965 : Nat := 4983230072969 + 3 ^ 40 * 3528965 * 2
def baseEnd_3528965 : Nat := 604018419297963547302697

theorem tailTrace_3528965 : CollatzResearch.WordTrace tailWord_3528965 prefixEnd_3528965 604018419297963547302697 := by
  unfold tailWord_3528965
  simp only [CollatzResearch.WordTrace]
  refine ⟨128711927660169979083772349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85807951773446652722514899 128711927660169979083772349)
  ·
    refine ⟨48266972872563742156414631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128711927660169979083772349 48266972872563742156414631)
    ·
      refine ⟨72400459308845613234621947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48266972872563742156414631 72400459308845613234621947)
      ·
        refine ⟨108600688963268419851932921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72400459308845613234621947 108600688963268419851932921)
        ·
          refine ⟨81450516722451314888949691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108600688963268419851932921 81450516722451314888949691)
          ·
            refine ⟨122175775083676972333424537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81450516722451314888949691 122175775083676972333424537)
            ·
              refine ⟨91631831312757729250068403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122175775083676972333424537 91631831312757729250068403)
              ·
                refine ⟨137447746969136593875102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91631831312757729250068403 137447746969136593875102605)
                ·
                  refine ⟨51542905113426222703163477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137447746969136593875102605 51542905113426222703163477)
                  ·
                    refine ⟨604018419297963547302697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51542905113426222703163477 604018419297963547302697)
                    ·
                      rfl

theorem cell23_3528965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_3528965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3528965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3528965 prefixEnd_3528965 := by exact prefixLift 3528965
  have htrace : WordTrace (prefixWord ++ tailWord_3528965) baseStart_3528965 baseEnd_3528965 := by
    simpa [prefixWord, tailWord_3528965, baseEnd_3528965] using wordTrace_append hprefix tailTrace_3528965
  have hstable : (prefixWord ++ tailWord_3528965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528965).length < 2 ^ (prefixWord ++ tailWord_3528965).sum := by decide
  have hdescent : baseEnd_3528965 < baseStart_3528965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_3529079 : Nat := 118140960795 + 3529079 * 2 ^ 59
def prefixEnd_3529079 : Nat := 4983230072969 + 3 ^ 40 * 3529079 * 2
def baseEnd_3529079 : Nat := 1812113794688503195882567

theorem tailTrace_3529079 : CollatzResearch.WordTrace tailWord_3529079 prefixEnd_3529079 1812113794688503195882567 := by
  unfold tailWord_3529079
  simp only [CollatzResearch.WordTrace]
  refine ⟨128716085581756976553422291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85810723721171317702281527 128716085581756976553422291)
  ·
    refine ⟨193074128372635464830133437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128716085581756976553422291 193074128372635464830133437)
    ·
      refine ⟨72402798139738299311300039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193074128372635464830133437 72402798139738299311300039)
      ·
        refine ⟨108604197209607448966950059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72402798139738299311300039 108604197209607448966950059)
        ·
          refine ⟨162906295814411173450425089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108604197209607448966950059 162906295814411173450425089)
          ·
            refine ⟨122179721860808380087818817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162906295814411173450425089 122179721860808380087818817)
            ·
              refine ⟨91634791395606285065864113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122179721860808380087818817 91634791395606285065864113)
              ·
                refine ⟨68726093546704713799398085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91634791395606285065864113 68726093546704713799398085)
                ·
                  refine ⟨12886142540007133837387141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68726093546704713799398085 12886142540007133837387141)
                  ·
                    refine ⟨2416151726251337594510089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12886142540007133837387141 2416151726251337594510089)
                    ·
                      refine ⟨1812113794688503195882567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416151726251337594510089 1812113794688503195882567)
                      ·
                        rfl

theorem cell23_3529079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_3529079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529079 prefixEnd_3529079 := by exact prefixLift 3529079
  have htrace : WordTrace (prefixWord ++ tailWord_3529079) baseStart_3529079 baseEnd_3529079 := by
    simpa [prefixWord, tailWord_3529079, baseEnd_3529079] using wordTrace_append hprefix tailTrace_3529079
  have hstable : (prefixWord ++ tailWord_3529079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529079).length < 2 ^ (prefixWord ++ tailWord_3529079).sum := by decide
  have hdescent : baseEnd_3529079 < baseStart_3529079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529099 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3]
def baseStart_3529099 : Nat := 118140960795 + 3529099 * 2 ^ 59
def prefixEnd_3529099 : Nat := 4983230072969 + 3 ^ 40 * 3529099 * 2
def baseEnd_3529099 : Nat := 1812124064301593117632475

theorem tailTrace_3529099 : CollatzResearch.WordTrace tailWord_3529099 prefixEnd_3529099 1812124064301593117632475 := by
  unfold tailWord_3529099
  simp only [CollatzResearch.WordTrace]
  refine ⟨128716815041684519969150351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85811210027789679979433567 128716815041684519969150351)
  ·
    refine ⟨193075222562526779953725527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128716815041684519969150351 193075222562526779953725527)
    ·
      refine ⟨289612833843790169930588291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193075222562526779953725527 289612833843790169930588291)
      ·
        refine ⟨434419250765685254895882437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289612833843790169930588291 434419250765685254895882437)
        ·
          refine ⟨81453609518565985292977957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434419250765685254895882437 81453609518565985292977957)
          ·
            refine ⟨15272551784731122242433367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81453609518565985292977957 15272551784731122242433367)
            ·
              refine ⟨22908827677096683363650051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15272551784731122242433367 22908827677096683363650051)
              ·
                refine ⟨34363241515645025045475077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22908827677096683363650051 34363241515645025045475077)
                ·
                  refine ⟨6443107784183442196026577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34363241515645025045475077 6443107784183442196026577)
                  ·
                    refine ⟨4832330838137581647019933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443107784183442196026577 4832330838137581647019933)
                    ·
                      refine ⟨1812124064301593117632475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832330838137581647019933 1812124064301593117632475)
                      ·
                        rfl

theorem cell23_3529099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].length) (baseStart_3529099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529099 prefixEnd_3529099 := by exact prefixLift 3529099
  have htrace : WordTrace (prefixWord ++ tailWord_3529099) baseStart_3529099 baseEnd_3529099 := by
    simpa [prefixWord, tailWord_3529099, baseEnd_3529099] using wordTrace_append hprefix tailTrace_3529099
  have hstable : (prefixWord ++ tailWord_3529099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529099).length < 2 ^ (prefixWord ++ tailWord_3529099).sum := by decide
  have hdescent : baseEnd_3529099 < baseStart_3529099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529119 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 6]
def baseStart_3529119 : Nat := 118140960795 + 3529119 * 2 ^ 59
def prefixEnd_3529119 : Nat := 4983230072969 + 3 ^ 40 * 3529119 * 2
def baseEnd_3529119 : Nat := 201348259323853671042487

theorem tailTrace_3529119 : CollatzResearch.WordTrace tailWord_3529119 prefixEnd_3529119 201348259323853671042487 := by
  unfold tailWord_3529119
  simp only [CollatzResearch.WordTrace]
  refine ⟨128717544501612063384878411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85811696334408042256585607 128717544501612063384878411)
  ·
    refine ⟨193076316752418095077317617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128717544501612063384878411 193076316752418095077317617)
    ·
      refine ⟨144807237564313571307988213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193076316752418095077317617 144807237564313571307988213)
      ·
        refine ⟨13575678521654397310123895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144807237564313571307988213 13575678521654397310123895)
        ·
          refine ⟨20363517782481595965185843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575678521654397310123895 20363517782481595965185843)
          ·
            refine ⟨30545276673722393947778765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363517782481595965185843 30545276673722393947778765)
            ·
              refine ⟨11454478752645897730417037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30545276673722393947778765 11454478752645897730417037)
              ·
                refine ⟨4295429532242211648906389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11454478752645897730417037 4295429532242211648906389)
                ·
                  refine ⟨201348259323853671042487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4295429532242211648906389 201348259323853671042487)
                  ·
                    rfl

theorem cell23_3529119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 6].length) (baseStart_3529119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529119 prefixEnd_3529119 := by exact prefixLift 3529119
  have htrace : WordTrace (prefixWord ++ tailWord_3529119) baseStart_3529119 baseEnd_3529119 := by
    simpa [prefixWord, tailWord_3529119, baseEnd_3529119] using wordTrace_append hprefix tailTrace_3529119
  have hstable : (prefixWord ++ tailWord_3529119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529119).length < 2 ^ (prefixWord ++ tailWord_3529119).sum := by decide
  have hdescent : baseEnd_3529119 < baseStart_3529119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529197 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3529197 : Nat := 118140960795 + 3529197 * 2 ^ 59
def prefixEnd_3529197 : Nat := 4983230072969 + 3 ^ 40 * 3529197 * 2
def baseEnd_3529197 : Nat := 1812174385405733734207025

theorem tailTrace_3529197 : CollatzResearch.WordTrace tailWord_3529197 prefixEnd_3529197 1812174385405733734207025 := by
  unfold tailWord_3529197
  simp only [CollatzResearch.WordTrace]
  refine ⟨128720389395329482706217845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85813592930219655137478563 128720389395329482706217845)
  ·
    refine ⟨12067536505812139003707923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128720389395329482706217845 12067536505812139003707923)
    ·
      refine ⟨18101304758718208505561885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12067536505812139003707923 18101304758718208505561885)
      ·
        refine ⟨6787989284519328189585707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18101304758718208505561885 6787989284519328189585707)
        ·
          refine ⟨10181983926778992284378561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6787989284519328189585707 10181983926778992284378561)
          ·
            refine ⟨7636487945084244213283921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10181983926778992284378561 7636487945084244213283921)
            ·
              refine ⟨5727365958813183159962941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636487945084244213283921 5727365958813183159962941)
              ·
                refine ⟨2147762234554943684986103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727365958813183159962941 2147762234554943684986103)
                ·
                  refine ⟨3221643351832415527479155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147762234554943684986103 3221643351832415527479155)
                  ·
                    refine ⟨4832465027748623291218733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3221643351832415527479155 4832465027748623291218733)
                    ·
                      refine ⟨1812174385405733734207025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832465027748623291218733 1812174385405733734207025)
                      ·
                        rfl

theorem cell23_3529197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3529197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529197 prefixEnd_3529197 := by exact prefixLift 3529197
  have htrace : WordTrace (prefixWord ++ tailWord_3529197) baseStart_3529197 baseEnd_3529197 := by
    simpa [prefixWord, tailWord_3529197, baseEnd_3529197] using wordTrace_append hprefix tailTrace_3529197
  have hstable : (prefixWord ++ tailWord_3529197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529197).length < 2 ^ (prefixWord ++ tailWord_3529197).sum := by decide
  have hdescent : baseEnd_3529197 < baseStart_3529197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529206 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3529206 : Nat := 118140960795 + 3529206 * 2 ^ 59
def prefixEnd_3529206 : Nat := 4983230072969 + 3 ^ 40 * 3529206 * 2
def baseEnd_3529206 : Nat := 1812179006731624198994483

theorem tailTrace_3529206 : CollatzResearch.WordTrace tailWord_3529206 prefixEnd_3529206 1812179006731624198994483 := by
  unfold tailWord_3529206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045044853268554827705967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85813811768197918162196981 8045044853268554827705967)
  ·
    refine ⟨12067567279902832241558951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045044853268554827705967 12067567279902832241558951)
    ·
      refine ⟨18101350919854248362338427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12067567279902832241558951 18101350919854248362338427)
      ·
        refine ⟨27152026379781372543507641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18101350919854248362338427 27152026379781372543507641)
        ·
          refine ⟨20364019784836029407630731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27152026379781372543507641 20364019784836029407630731)
          ·
            refine ⟨30546029677254044111446097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20364019784836029407630731 30546029677254044111446097)
            ·
              refine ⟨22909522257940533083584573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30546029677254044111446097 22909522257940533083584573)
              ·
                refine ⟨8591070846727699906344215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22909522257940533083584573 8591070846727699906344215)
                ·
                  refine ⟨12886606270091549859516323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591070846727699906344215 12886606270091549859516323)
                  ·
                    refine ⟨19329909405137324789274485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12886606270091549859516323 19329909405137324789274485)
                    ·
                      refine ⟨1812179006731624198994483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19329909405137324789274485 1812179006731624198994483)
                      ·
                        rfl

theorem cell23_3529206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3529206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529206 prefixEnd_3529206 := by exact prefixLift 3529206
  have htrace : WordTrace (prefixWord ++ tailWord_3529206) baseStart_3529206 baseEnd_3529206 := by
    simpa [prefixWord, tailWord_3529206, baseEnd_3529206] using wordTrace_append hprefix tailTrace_3529206
  have hstable : (prefixWord ++ tailWord_3529206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529206).length < 2 ^ (prefixWord ++ tailWord_3529206).sum := by decide
  have hdescent : baseEnd_3529206 < baseStart_3529206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529220 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3529220 : Nat := 118140960795 + 3529220 * 2 ^ 59
def prefixEnd_3529220 : Nat := 4983230072969 + 3 ^ 40 * 3529220 * 2
def baseEnd_3529220 : Nat := 1812186195460787144219419

theorem tailTrace_3529220 : CollatzResearch.WordTrace tailWord_3529220 prefixEnd_3529220 1812186195460787144219419 := by
  unfold tailWord_3529220
  simp only [CollatzResearch.WordTrace]
  refine ⟨64360614137123078817152557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85814152182830771756203409 64360614137123078817152557)
  ·
    refine ⟨24135230301421154556432209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64360614137123078817152557 24135230301421154556432209)
    ·
      refine ⟨18101422726065865917324157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24135230301421154556432209 18101422726065865917324157)
      ·
        refine ⟨6788033522274699718996559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18101422726065865917324157 6788033522274699718996559)
        ·
          refine ⟨10182050283412049578494839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788033522274699718996559 10182050283412049578494839)
          ·
            refine ⟨15273075425118074367742259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182050283412049578494839 15273075425118074367742259)
            ·
              refine ⟨22909613137677111551613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15273075425118074367742259 22909613137677111551613389)
              ·
                refine ⟨8591104926628916831855021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22909613137677111551613389 8591104926628916831855021)
                ·
                  refine ⟨3221664347485843811945633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8591104926628916831855021 3221664347485843811945633)
                  ·
                    refine ⟨2416248260614382858959225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3221664347485843811945633 2416248260614382858959225)
                    ·
                      refine ⟨1812186195460787144219419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416248260614382858959225 1812186195460787144219419)
                      ·
                        rfl

theorem cell23_3529220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3529220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529220 prefixEnd_3529220 := by exact prefixLift 3529220
  have htrace : WordTrace (prefixWord ++ tailWord_3529220) baseStart_3529220 baseEnd_3529220 := by
    simpa [prefixWord, tailWord_3529220, baseEnd_3529220] using wordTrace_append hprefix tailTrace_3529220
  have hstable : (prefixWord ++ tailWord_3529220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529220).length < 2 ^ (prefixWord ++ tailWord_3529220).sum := by decide
  have hdescent : baseEnd_3529220 < baseStart_3529220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529230 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3529230 : Nat := 118140960795 + 3529230 * 2 ^ 59
def prefixEnd_3529230 : Nat := 4983230072969 + 3 ^ 40 * 3529230 * 2
def baseEnd_3529230 : Nat := 604063776755777368364791

theorem tailTrace_3529230 : CollatzResearch.WordTrace tailWord_3529230 prefixEnd_3529230 604063776755777368364791 := by
  unfold tailWord_3529230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090199125526241167771143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85814395336139952894779429 16090199125526241167771143)
  ·
    refine ⟨24135298688289361751656715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16090199125526241167771143 24135298688289361751656715)
    ·
      refine ⟨36202948032434042627485073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24135298688289361751656715 36202948032434042627485073)
      ·
        refine ⟨27152211024325531970613805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36202948032434042627485073 27152211024325531970613805)
        ·
          refine ⟨10182079134122074488980177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27152211024325531970613805 10182079134122074488980177)
          ·
            refine ⟨7636559350591555866735133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10182079134122074488980177 7636559350591555866735133)
            ·
              refine ⟨2863709756471833450025675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7636559350591555866735133 2863709756471833450025675)
              ·
                refine ⟨4295564634707750175038513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863709756471833450025675 4295564634707750175038513)
                ·
                  refine ⟨3221673476030812631278885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4295564634707750175038513 3221673476030812631278885)
                  ·
                    refine ⟨604063776755777368364791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221673476030812631278885 604063776755777368364791)
                    ·
                      rfl

theorem cell23_3529230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3529230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529230 prefixEnd_3529230 := by exact prefixLift 3529230
  have htrace : WordTrace (prefixWord ++ tailWord_3529230) baseStart_3529230 baseEnd_3529230 := by
    simpa [prefixWord, tailWord_3529230, baseEnd_3529230] using wordTrace_append hprefix tailTrace_3529230
  have hstable : (prefixWord ++ tailWord_3529230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529230).length < 2 ^ (prefixWord ++ tailWord_3529230).sum := by decide
  have hdescent : baseEnd_3529230 < baseStart_3529230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529249 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3529249 : Nat := 118140960795 + 3529249 * 2 ^ 59
def prefixEnd_3529249 : Nat := 4983230072969 + 3 ^ 40 * 3529249 * 2
def baseEnd_3529249 : Nat := 1812201086399767530756785

theorem tailTrace_3529249 : CollatzResearch.WordTrace tailWord_3529249 prefixEnd_3529249 1812201086399767530756785 := by
  unfold tailWord_3529249
  simp only [CollatzResearch.WordTrace]
  refine ⟨128722285991141095587110801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85814857327427397058073867 128722285991141095587110801)
  ·
    refine ⟨96541714493355821690333101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128722285991141095587110801 96541714493355821690333101)
    ·
      refine ⟨36203142935008433133874913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96541714493355821690333101 36203142935008433133874913)
      ·
        refine ⟨27152357201256324850406185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36203142935008433133874913 27152357201256324850406185)
        ·
          refine ⟨20364267900942243637804639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27152357201256324850406185 20364267900942243637804639)
          ·
            refine ⟨30546401851413365456706959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20364267900942243637804639 30546401851413365456706959)
            ·
              refine ⟨45819602777120048185060439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30546401851413365456706959 45819602777120048185060439)
              ·
                refine ⟨68729404165680072277590659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45819602777120048185060439 68729404165680072277590659)
                ·
                  refine ⟨103094106248520108416385989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68729404165680072277590659 103094106248520108416385989)
                  ·
                    refine ⟨19330144921597520328072373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103094106248520108416385989 19330144921597520328072373)
                    ·
                      refine ⟨1812201086399767530756785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19330144921597520328072373 1812201086399767530756785)
                      ·
                        rfl

theorem cell23_3529249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3529249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529249 prefixEnd_3529249 := by exact prefixLift 3529249
  have htrace : WordTrace (prefixWord ++ tailWord_3529249) baseStart_3529249 baseEnd_3529249 := by
    simpa [prefixWord, tailWord_3529249, baseEnd_3529249] using wordTrace_append hprefix tailTrace_3529249
  have hstable : (prefixWord ++ tailWord_3529249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529249).length < 2 ^ (prefixWord ++ tailWord_3529249).sum := by decide
  have hdescent : baseEnd_3529249 < baseStart_3529249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529270 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3529270 : Nat := 118140960795 + 3529270 * 2 ^ 59
def prefixEnd_3529270 : Nat := 4983230072969 + 3 ^ 40 * 3529270 * 2
def baseEnd_3529270 : Nat := 1812211869493511948594189

theorem tailTrace_3529270 : CollatzResearch.WordTrace tailWord_3529270 prefixEnd_3529270 1812211869493511948594189 := by
  unfold tailWord_3529270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045190745254063510851579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85815367949376677449083509 8045190745254063510851579)
  ·
    refine ⟨12067786117881095266277369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045190745254063510851579 12067786117881095266277369)
    ·
      refine ⟨9050839588410821449708027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12067786117881095266277369 9050839588410821449708027)
      ·
        refine ⟨13576259382616232174562041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050839588410821449708027 13576259382616232174562041)
        ·
          refine ⟨10182194536962174130921531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13576259382616232174562041 10182194536962174130921531)
          ·
            refine ⟨15273291805443261196382297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182194536962174130921531 15273291805443261196382297)
            ·
              refine ⟨11454968854082445897286723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15273291805443261196382297 11454968854082445897286723)
              ·
                refine ⟨17182453281123668845930085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11454968854082445897286723 17182453281123668845930085)
                ·
                  refine ⟨3221709990210687908611891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17182453281123668845930085 3221709990210687908611891)
                  ·
                    refine ⟨4832564985316031862917837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3221709990210687908611891 4832564985316031862917837)
                    ·
                      refine ⟨1812211869493511948594189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832564985316031862917837 1812211869493511948594189)
                      ·
                        rfl

theorem cell23_3529270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3529270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529270 prefixEnd_3529270 := by exact prefixLift 3529270
  have htrace : WordTrace (prefixWord ++ tailWord_3529270) baseStart_3529270 baseEnd_3529270 := by
    simpa [prefixWord, tailWord_3529270, baseEnd_3529270] using wordTrace_append hprefix tailTrace_3529270
  have hstable : (prefixWord ++ tailWord_3529270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529270).length < 2 ^ (prefixWord ++ tailWord_3529270).sum := by decide
  have hdescent : baseEnd_3529270 < baseStart_3529270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529279 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3529279 : Nat := 118140960795 + 3529279 * 2 ^ 59
def prefixEnd_3529279 : Nat := 4983230072969 + 3 ^ 40 * 3529279 * 2
def baseEnd_3529279 : Nat := 1812216490819402413381647

theorem tailTrace_3529279 : CollatzResearch.WordTrace tailWord_3529279 prefixEnd_3529279 1812216490819402413381647 := by
  unfold tailWord_3529279
  simp only [CollatzResearch.WordTrace]
  refine ⟨128723380181032410710702891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85815586787354940473801927 128723380181032410710702891)
  ·
    refine ⟨193085070271548616066054337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128723380181032410710702891 193085070271548616066054337)
    ·
      refine ⟨144813802703661462049540753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193085070271548616066054337 144813802703661462049540753)
      ·
        refine ⟨108610352027746096537155565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144813802703661462049540753 108610352027746096537155565)
        ·
          refine ⟨40728882010404786201433337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108610352027746096537155565 40728882010404786201433337)
          ·
            refine ⟨30546661507803589651075003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40728882010404786201433337 30546661507803589651075003)
            ·
              refine ⟨45819992261705384476612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30546661507803589651075003 45819992261705384476612505)
              ·
                refine ⟨34364994196279038357459379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45819992261705384476612505 34364994196279038357459379)
                ·
                  refine ⟨51547491294418557536189069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34364994196279038357459379 51547491294418557536189069)
                  ·
                    refine ⟨19330309235406959076070901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51547491294418557536189069 19330309235406959076070901)
                    ·
                      refine ⟨1812216490819402413381647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19330309235406959076070901 1812216490819402413381647)
                      ·
                        rfl

theorem cell23_3529279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3529279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529279 prefixEnd_3529279 := by exact prefixLift 3529279
  have htrace : WordTrace (prefixWord ++ tailWord_3529279) baseStart_3529279 baseEnd_3529279 := by
    simpa [prefixWord, tailWord_3529279, baseEnd_3529279] using wordTrace_append hprefix tailTrace_3529279
  have hstable : (prefixWord ++ tailWord_3529279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529279).length < 2 ^ (prefixWord ++ tailWord_3529279).sum := by decide
  have hdescent : baseEnd_3529279 < baseStart_3529279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529287 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_3529287 : Nat := 118140960795 + 3529287 * 2 ^ 59
def prefixEnd_3529287 : Nat := 4983230072969 + 3 ^ 40 * 3529287 * 2
def baseEnd_3529287 : Nat := 1812220598664638382081611

theorem tailTrace_3529287 : CollatzResearch.WordTrace tailWord_3529287 prefixEnd_3529287 1812220598664638382081611 := by
  unfold tailWord_3529287
  simp only [CollatzResearch.WordTrace]
  refine ⟨128723671965003428076994115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85815781310002285384662743 128723671965003428076994115)
  ·
    refine ⟨193085507947505142115491173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128723671965003428076994115 193085507947505142115491173)
    ·
      refine ⟨36203532740157214146654595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193085507947505142115491173 36203532740157214146654595)
      ·
        refine ⟨54305299110235821219981893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36203532740157214146654595 54305299110235821219981893)
        ·
          refine ⟨10182243583169216478746605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54305299110235821219981893 10182243583169216478746605)
          ·
            refine ⟨3818341343688456179529977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10182243583169216478746605 3818341343688456179529977)
            ·
              refine ⟨2863756007766342134647483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818341343688456179529977 2863756007766342134647483)
              ·
                refine ⟨4295634011649513201971225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863756007766342134647483 4295634011649513201971225)
                ·
                  refine ⟨3221725508737134901478419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4295634011649513201971225 3221725508737134901478419)
                  ·
                    refine ⟨4832588263105702352217629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3221725508737134901478419 4832588263105702352217629)
                    ·
                      refine ⟨1812220598664638382081611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832588263105702352217629 1812220598664638382081611)
                      ·
                        rfl

theorem cell23_3529287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_3529287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529287 prefixEnd_3529287 := by exact prefixLift 3529287
  have htrace : WordTrace (prefixWord ++ tailWord_3529287) baseStart_3529287 baseEnd_3529287 := by
    simpa [prefixWord, tailWord_3529287, baseEnd_3529287] using wordTrace_append hprefix tailTrace_3529287
  have hstable : (prefixWord ++ tailWord_3529287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529287).length < 2 ^ (prefixWord ++ tailWord_3529287).sum := by decide
  have hdescent : baseEnd_3529287 < baseStart_3529287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529329 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3529329 : Nat := 118140960795 + 3529329 * 2 ^ 59
def prefixEnd_3529329 : Nat := 4983230072969 + 3 ^ 40 * 3529329 * 2
def baseEnd_3529329 : Nat := 604080721617375739252139

theorem tailTrace_3529329 : CollatzResearch.WordTrace tailWord_3529329 prefixEnd_3529329 604080721617375739252139 := by
  unfold tailWord_3529329
  simp only [CollatzResearch.WordTrace]
  refine ⟨128725203830851269250023041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85816802553900846166682027 128725203830851269250023041)
  ·
    refine ⟨96543902873138451937517281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128725203830851269250023041 96543902873138451937517281)
    ·
      refine ⟨72407927154853838953137961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96543902873138451937517281 72407927154853838953137961)
      ·
        refine ⟨54305945366140379214853471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72407927154853838953137961 54305945366140379214853471)
        ·
          refine ⟨81458918049210568822280207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54305945366140379214853471 81458918049210568822280207)
          ·
            refine ⟨122188377073815853233420311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81458918049210568822280207 122188377073815853233420311)
            ·
              refine ⟨183282565610723779850130467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122188377073815853233420311 183282565610723779850130467)
              ·
                refine ⟨274923848416085669775195701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183282565610723779850130467 274923848416085669775195701)
                ·
                  refine ⟨25774110789008031541424597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274923848416085669775195701 25774110789008031541424597)
                  ·
                    refine ⟨604080721617375739252139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25774110789008031541424597 604080721617375739252139)
                    ·
                      rfl

theorem cell23_3529329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3529329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529329 prefixEnd_3529329 := by exact prefixLift 3529329
  have htrace : WordTrace (prefixWord ++ tailWord_3529329) baseStart_3529329 baseEnd_3529329 := by
    simpa [prefixWord, tailWord_3529329, baseEnd_3529329] using wordTrace_append hprefix tailTrace_3529329
  have hstable : (prefixWord ++ tailWord_3529329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529329).length < 2 ^ (prefixWord ++ tailWord_3529329).sum := by decide
  have hdescent : baseEnd_3529329 < baseStart_3529329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529339 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_3529339 : Nat := 118140960795 + 3529339 * 2 ^ 59
def prefixEnd_3529339 : Nat := 4983230072969 + 3 ^ 40 * 3529339 * 2
def baseEnd_3529339 : Nat := 1812247299658672178631371

theorem tailTrace_3529339 : CollatzResearch.WordTrace tailWord_3529339 prefixEnd_3529339 1812247299658672178631371 := by
  unfold tailWord_3529339
  simp only [CollatzResearch.WordTrace]
  refine ⟨128725568560815040957887071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85817045707210027305258047 128725568560815040957887071)
  ·
    refine ⟨193088352841222561436830607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128725568560815040957887071 193088352841222561436830607)
    ·
      refine ⟨289632529261833842155245911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193088352841222561436830607 289632529261833842155245911)
      ·
        refine ⟨434448793892750763232868867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289632529261833842155245911 434448793892750763232868867)
        ·
          refine ⟨651673190839126144849303301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434448793892750763232868867 651673190839126144849303301)
          ·
            refine ⟨122188723282336152159244369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651673190839126144849303301 122188723282336152159244369)
            ·
              refine ⟨91641542461752114119433277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122188723282336152159244369 91641542461752114119433277)
              ·
                refine ⟨34365578423157042794787479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91641542461752114119433277 34365578423157042794787479)
                ·
                  refine ⟨51548367634735564192181219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34365578423157042794787479 51548367634735564192181219)
                  ·
                    refine ⟨77322551452103346288271829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51548367634735564192181219 77322551452103346288271829)
                    ·
                      refine ⟨1812247299658672178631371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77322551452103346288271829 1812247299658672178631371)
                      ·
                        rfl

theorem cell23_3529339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_3529339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529339 prefixEnd_3529339 := by exact prefixLift 3529339
  have htrace : WordTrace (prefixWord ++ tailWord_3529339) baseStart_3529339 baseEnd_3529339 := by
    simpa [prefixWord, tailWord_3529339, baseEnd_3529339] using wordTrace_append hprefix tailTrace_3529339
  have hstable : (prefixWord ++ tailWord_3529339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529339).length < 2 ^ (prefixWord ++ tailWord_3529339).sum := by decide
  have hdescent : baseEnd_3529339 < baseStart_3529339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529359 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 8]
def baseStart_3529359 : Nat := 118140960795 + 3529359 * 2 ^ 59
def prefixEnd_3529359 : Nat := 4983230072969 + 3 ^ 40 * 3529359 * 2
def baseEnd_3529359 : Nat := 604085856423920700127093

theorem tailTrace_3529359 : CollatzResearch.WordTrace tailWord_3529359 prefixEnd_3529359 604085856423920700127093 := by
  unfold tailWord_3529359
  simp only [CollatzResearch.WordTrace]
  refine ⟨128726298020742584373615131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85817532013828389582410087 128726298020742584373615131)
  ·
    refine ⟨193089447031113876560422697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128726298020742584373615131 193089447031113876560422697)
    ·
      refine ⟨144817085273335407420317023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193089447031113876560422697 144817085273335407420317023)
      ·
        refine ⟨217225627910003111130475535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144817085273335407420317023 217225627910003111130475535)
        ·
          refine ⟨325838441865004666695713303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217225627910003111130475535 325838441865004666695713303)
          ·
            refine ⟨488757662797507000043569955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325838441865004666695713303 488757662797507000043569955)
            ·
              refine ⟨733136494196260500065354933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488757662797507000043569955 733136494196260500065354933)
              ·
                refine ⟨68731546330899421881127025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733136494196260500065354933 68731546330899421881127025)
                ·
                  refine ⟨51548659748174566410845269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68731546330899421881127025 51548659748174566410845269)
                  ·
                    refine ⟨604085856423920700127093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51548659748174566410845269 604085856423920700127093)
                    ·
                      rfl

theorem cell23_3529359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_3529359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529359 prefixEnd_3529359 := by exact prefixLift 3529359
  have htrace : WordTrace (prefixWord ++ tailWord_3529359) baseStart_3529359 baseEnd_3529359 := by
    simpa [prefixWord, tailWord_3529359, baseEnd_3529359] using wordTrace_append hprefix tailTrace_3529359
  have hstable : (prefixWord ++ tailWord_3529359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529359).length < 2 ^ (prefixWord ++ tailWord_3529359).sum := by decide
  have hdescent : baseEnd_3529359 < baseStart_3529359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529453 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3529453 : Nat := 118140960795 + 3529453 * 2 ^ 59
def prefixEnd_3529453 : Nat := 4983230072969 + 3 ^ 40 * 3529453 * 2
def baseEnd_3529453 : Nat := 604101945484428244201949

theorem tailTrace_3529453 : CollatzResearch.WordTrace tailWord_3529453 prefixEnd_3529453 604101945484428244201949 := by
  unfold tailWord_3529453
  simp only [CollatzResearch.WordTrace]
  refine ⟨128729726482402038427537013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85819817654934692285024675 128729726482402038427537013)
  ·
    refine ⟨12068411857725191102581595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128729726482402038427537013 12068411857725191102581595)
    ·
      refine ⟨18102617786587786653872393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068411857725191102581595 18102617786587786653872393)
      ·
        refine ⟨13576963339940839990404295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18102617786587786653872393 13576963339940839990404295)
        ·
          refine ⟨20365445009911259985606443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576963339940839990404295 20365445009911259985606443)
          ·
            refine ⟨30548167514866889978409665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20365445009911259985606443 30548167514866889978409665)
            ·
              refine ⟨22911125636150167483807249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30548167514866889978409665 22911125636150167483807249)
              ·
                refine ⟨17183344227112625612855437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22911125636150167483807249 17183344227112625612855437)
                ·
                  refine ⟨6443754085167234604820789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17183344227112625612855437 6443754085167234604820789)
                  ·
                    refine ⟨604101945484428244201949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6443754085167234604820789 604101945484428244201949)
                    ·
                      rfl

theorem cell23_3529453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3529453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529453 prefixEnd_3529453 := by exact prefixLift 3529453
  have htrace : WordTrace (prefixWord ++ tailWord_3529453) baseStart_3529453 baseEnd_3529453 := by
    simpa [prefixWord, tailWord_3529453, baseEnd_3529453] using wordTrace_append hprefix tailTrace_3529453
  have hstable : (prefixWord ++ tailWord_3529453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529453).length < 2 ^ (prefixWord ++ tailWord_3529453).sum := by decide
  have hdescent : baseEnd_3529453 < baseStart_3529453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529470 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3529470 : Nat := 118140960795 + 3529470 * 2 ^ 59
def prefixEnd_3529470 : Nat := 4983230072969 + 3 ^ 40 * 3529470 * 2
def baseEnd_3529470 : Nat := 604104855208137055364423

theorem tailTrace_3529470 : CollatzResearch.WordTrace tailWord_3529470 prefixEnd_3529470 604104855208137055364423 := by
  unfold tailWord_3529470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091293315417556291363233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85820231015560300220603909 16091293315417556291363233)
  ·
    refine ⟨12068469986563167218522425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16091293315417556291363233 12068469986563167218522425)
    ·
      refine ⟨9051352489922375413891819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12068469986563167218522425 9051352489922375413891819)
      ·
        refine ⟨13577028734883563120837729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051352489922375413891819 13577028734883563120837729)
        ·
          refine ⟨10182771551162672340628297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13577028734883563120837729 10182771551162672340628297)
          ·
            refine ⟨7637078663372004255471223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10182771551162672340628297 7637078663372004255471223)
            ·
              refine ⟨11455617995058006383206835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637078663372004255471223 11455617995058006383206835)
              ·
                refine ⟨17183426992587009574810253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455617995058006383206835 17183426992587009574810253)
                ·
                  refine ⟨6443785122220128590553845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17183426992587009574810253 6443785122220128590553845)
                  ·
                    refine ⟨604104855208137055364423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6443785122220128590553845 604104855208137055364423)
                    ·
                      rfl

theorem cell23_3529470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3529470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529470 prefixEnd_3529470 := by exact prefixLift 3529470
  have htrace : WordTrace (prefixWord ++ tailWord_3529470) baseStart_3529470 baseEnd_3529470 := by
    simpa [prefixWord, tailWord_3529470, baseEnd_3529470] using wordTrace_append hprefix tailTrace_3529470
  have hstable : (prefixWord ++ tailWord_3529470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529470).length < 2 ^ (prefixWord ++ tailWord_3529470).sum := by decide
  have hdescent : baseEnd_3529470 < baseStart_3529470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529500 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_3529500 : Nat := 118140960795 + 3529500 * 2 ^ 59
def prefixEnd_3529500 : Nat := 4983230072969 + 3 ^ 40 * 3529500 * 2
def baseEnd_3529500 : Nat := 604109990014682016239377

theorem tailTrace_3529500 : CollatzResearch.WordTrace tailWord_3529500 prefixEnd_3529500 604109990014682016239377 := by
  unfold tailWord_3529500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64365720356615882727248977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85820960475487843636331969 64365720356615882727248977)
  ·
    refine ⟨48274290267461912045436733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64365720356615882727248977 48274290267461912045436733)
    ·
      refine ⟨18102858850298217017038775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48274290267461912045436733 18102858850298217017038775)
      ·
        refine ⟨27154288275447325525558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18102858850298217017038775 27154288275447325525558163)
        ·
          refine ⟨40731432413170988288337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27154288275447325525558163 40731432413170988288337245)
          ·
            refine ⟨15274287154939120608126467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40731432413170988288337245 15274287154939120608126467)
            ·
              refine ⟨22911430732408680912189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15274287154939120608126467 22911430732408680912189701)
              ·
                refine ⟨4295893262326627671035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22911430732408680912189701 4295893262326627671035569)
                ·
                  refine ⟨3221919946744970753276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4295893262326627671035569 3221919946744970753276677)
                  ·
                    refine ⟨604109990014682016239377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221919946744970753276677 604109990014682016239377)
                    ·
                      rfl

theorem cell23_3529500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_3529500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529500 prefixEnd_3529500 := by exact prefixLift 3529500
  have htrace : WordTrace (prefixWord ++ tailWord_3529500) baseStart_3529500 baseEnd_3529500 := by
    simpa [prefixWord, tailWord_3529500, baseEnd_3529500] using wordTrace_append hprefix tailTrace_3529500
  have hstable : (prefixWord ++ tailWord_3529500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529500).length < 2 ^ (prefixWord ++ tailWord_3529500).sum := by decide
  have hdescent : baseEnd_3529500 < baseStart_3529500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529501 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3529501 : Nat := 118140960795 + 3529501 * 2 ^ 59
def prefixEnd_3529501 : Nat := 4983230072969 + 3 ^ 40 * 3529501 * 2
def baseEnd_3529501 : Nat := 1812330483524700544805627

theorem tailTrace_3529501 : CollatzResearch.WordTrace tailWord_3529501 prefixEnd_3529501 1812330483524700544805627 := by
  unfold tailWord_3529501
  simp only [CollatzResearch.WordTrace]
  refine ⟨128731477186228142625284357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85820984790818761750189571 128731477186228142625284357)
  ·
    refine ⟨24137151972417776742240817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128731477186228142625284357 24137151972417776742240817)
    ·
      refine ⟨18102863979313332556680613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24137151972417776742240817 18102863979313332556680613)
      ·
        refine ⟨3394286996121249854377615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18102863979313332556680613 3394286996121249854377615)
        ·
          refine ⟨5091430494181874781566423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394286996121249854377615 5091430494181874781566423)
          ·
            refine ⟨7637145741272812172349635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091430494181874781566423 7637145741272812172349635)
            ·
              refine ⟨11455718611909218258524453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637145741272812172349635 11455718611909218258524453)
              ·
                refine ⟨2147947239732978423473335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11455718611909218258524453 2147947239732978423473335)
                ·
                  refine ⟨3221920859599467635210003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147947239732978423473335 3221920859599467635210003)
                  ·
                    refine ⟨4832881289399201452815005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3221920859599467635210003 4832881289399201452815005)
                    ·
                      refine ⟨1812330483524700544805627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832881289399201452815005 1812330483524700544805627)
                      ·
                        rfl

theorem cell23_3529501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3529501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529501 prefixEnd_3529501 := by exact prefixLift 3529501
  have htrace : WordTrace (prefixWord ++ tailWord_3529501) baseStart_3529501 baseEnd_3529501 := by
    simpa [prefixWord, tailWord_3529501, baseEnd_3529501] using wordTrace_append hprefix tailTrace_3529501
  have hstable : (prefixWord ++ tailWord_3529501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529501).length < 2 ^ (prefixWord ++ tailWord_3529501).sum := by decide
  have hdescent : baseEnd_3529501 < baseStart_3529501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529530 : List Nat := [3, 1, 1, 1, 6, 1, 3, 7]
def baseStart_3529530 : Nat := 118140960795 + 3529530 * 2 ^ 59
def prefixEnd_3529530 : Nat := 4983230072969 + 3 ^ 40 * 3529530 * 2
def baseEnd_3529530 : Nat := 67123902757914108568259

theorem tailTrace_3529530 : CollatzResearch.WordTrace tailWord_3529530 prefixEnd_3529530 67123902757914108568259 := by
  unfold tailWord_3529530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183133725780770144522511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85821689935415387052060029 32183133725780770144522511)
  ·
    refine ⟨48274700588671155216783767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32183133725780770144522511 48274700588671155216783767)
    ·
      refine ⟨72412050883006732825175651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48274700588671155216783767 72412050883006732825175651)
      ·
        refine ⟨108618076324510099237763477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72412050883006732825175651 108618076324510099237763477)
        ·
          refine ⟨5091472327711410901770163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108618076324510099237763477 5091472327711410901770163)
          ·
            refine ⟨7637208491567116352655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091472327711410901770163 7637208491567116352655245)
            ·
              refine ⟨2863953184337668632245717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7637208491567116352655245 2863953184337668632245717)
              ·
                refine ⟨67123902757914108568259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2863953184337668632245717 67123902757914108568259)
                ·
                  rfl

theorem cell23_3529530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_3529530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529530 prefixEnd_3529530 := by exact prefixLift 3529530
  have htrace : WordTrace (prefixWord ++ tailWord_3529530) baseStart_3529530 baseEnd_3529530 := by
    simpa [prefixWord, tailWord_3529530, baseEnd_3529530] using wordTrace_append hprefix tailTrace_3529530
  have hstable : (prefixWord ++ tailWord_3529530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529530).length < 2 ^ (prefixWord ++ tailWord_3529530).sum := by decide
  have hdescent : baseEnd_3529530 < baseStart_3529530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529573 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_3529573 : Nat := 118140960795 + 3529573 * 2 ^ 59
def prefixEnd_3529573 : Nat := 4983230072969 + 3 ^ 40 * 3529573 * 2
def baseEnd_3529573 : Nat := 604122484710608087701765

theorem tailTrace_3529573 : CollatzResearch.WordTrace tailWord_3529573 prefixEnd_3529573 604122484710608087701765 := by
  unfold tailWord_3529573
  simp only [CollatzResearch.WordTrace]
  refine ⟨128734103241967298921905373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85822735494644865947936915 128734103241967298921905373)
  ·
    refine ⟨48275288715737737095714515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128734103241967298921905373 48275288715737737095714515)
    ·
      refine ⟨72412933073606605643571773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48275288715737737095714515 72412933073606605643571773)
      ·
        refine ⟨27154849902602477116339415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72412933073606605643571773 27154849902602477116339415)
        ·
          refine ⟨40732274853903715674509123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27154849902602477116339415 40732274853903715674509123)
          ·
            refine ⟨61098412280855573511763685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40732274853903715674509123 61098412280855573511763685)
            ·
              refine ⟨11455952302660420033455691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61098412280855573511763685 11455952302660420033455691)
              ·
                refine ⟨17183928453990630050183537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455952302660420033455691 17183928453990630050183537)
                ·
                  refine ⟨12887946340492972537637653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17183928453990630050183537 12887946340492972537637653)
                  ·
                    refine ⟨604122484710608087701765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12887946340492972537637653 604122484710608087701765)
                    ·
                      rfl

theorem cell23_3529573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_3529573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529573 prefixEnd_3529573 := by exact prefixLift 3529573
  have htrace : WordTrace (prefixWord ++ tailWord_3529573) baseStart_3529573 baseEnd_3529573 := by
    simpa [prefixWord, tailWord_3529573, baseEnd_3529573] using wordTrace_append hprefix tailTrace_3529573
  have hstable : (prefixWord ++ tailWord_3529573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529573).length < 2 ^ (prefixWord ++ tailWord_3529573).sum := by decide
  have hdescent : baseEnd_3529573 < baseStart_3529573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529583 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_3529583 : Nat := 118140960795 + 3529583 * 2 ^ 59
def prefixEnd_3529583 : Nat := 4983230072969 + 3 ^ 40 * 3529583 * 2
def baseEnd_3529583 : Nat := 1812372588938369223980249

theorem tailTrace_3529583 : CollatzResearch.WordTrace tailWord_3529583 prefixEnd_3529583 1812372588938369223980249 := by
  unfold tailWord_3529583
  simp only [CollatzResearch.WordTrace]
  refine ⟨128734467971931070629769403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85822978647954047086512935 128734467971931070629769403)
  ·
    refine ⟨193101701957896605944654105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128734467971931070629769403 193101701957896605944654105)
    ·
      refine ⟨144826276468422454458490579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193101701957896605944654105 144826276468422454458490579)
      ·
        refine ⟨217239414702633681687735869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144826276468422454458490579 217239414702633681687735869)
        ·
          refine ⟨81464780513487630632900951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217239414702633681687735869 81464780513487630632900951)
          ·
            refine ⟨122197170770231445949351427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81464780513487630632900951 122197170770231445949351427)
            ·
              refine ⟨183295756155347168924027141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122197170770231445949351427 183295756155347168924027141)
              ·
                refine ⟨34367954279127594173255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183295756155347168924027141 34367954279127594173255089)
                ·
                  refine ⟨25775965709345695629941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34367954279127594173255089 25775965709345695629941317)
                  ·
                    refine ⟨4832993570502317930613997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25775965709345695629941317 4832993570502317930613997)
                    ·
                      refine ⟨1812372588938369223980249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4832993570502317930613997 1812372588938369223980249)
                      ·
                        rfl

theorem cell23_3529583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_3529583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529583 prefixEnd_3529583 := by exact prefixLift 3529583
  have htrace : WordTrace (prefixWord ++ tailWord_3529583) baseStart_3529583 baseEnd_3529583 := by
    simpa [prefixWord, tailWord_3529583, baseEnd_3529583] using wordTrace_append hprefix tailTrace_3529583
  have hstable : (prefixWord ++ tailWord_3529583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529583).length < 2 ^ (prefixWord ++ tailWord_3529583).sum := by decide
  have hdescent : baseEnd_3529583 < baseStart_3529583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529597 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_3529597 : Nat := 118140960795 + 3529597 * 2 ^ 59
def prefixEnd_3529597 : Nat := 4983230072969 + 3 ^ 40 * 3529597 * 2
def baseEnd_3529597 : Nat := 1812379777667532169205185

theorem tailTrace_3529597 : CollatzResearch.WordTrace tailWord_3529597 prefixEnd_3529597 1812379777667532169205185 := by
  unfold tailWord_3529597
  simp only [CollatzResearch.WordTrace]
  refine ⟨128734978593880351020779045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85823319062586900680519363 128734978593880351020779045)
  ·
    refine ⟨24137808486352565816396071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128734978593880351020779045 24137808486352565816396071)
    ·
      refine ⟨36206712729528848724594107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24137808486352565816396071 36206712729528848724594107)
      ·
        refine ⟨54310069094293273086891161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36206712729528848724594107 54310069094293273086891161)
        ·
          refine ⟨40732551820719954815168371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54310069094293273086891161 40732551820719954815168371)
          ·
            refine ⟨61098827731079932222752557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40732551820719954815168371 61098827731079932222752557)
            ·
              refine ⟨22912060399154974583532209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61098827731079932222752557 22912060399154974583532209)
              ·
                refine ⟨17184045299366230937649157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22912060399154974583532209 17184045299366230937649157)
                ·
                  refine ⟨3222008493631168300809217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17184045299366230937649157 3222008493631168300809217)
                  ·
                    refine ⟨2416506370223376225606913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222008493631168300809217 2416506370223376225606913)
                    ·
                      refine ⟨1812379777667532169205185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416506370223376225606913 1812379777667532169205185)
                      ·
                        rfl

theorem cell23_3529597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_3529597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529597 prefixEnd_3529597 := by exact prefixLift 3529597
  have htrace : WordTrace (prefixWord ++ tailWord_3529597) baseStart_3529597 baseEnd_3529597 := by
    simpa [prefixWord, tailWord_3529597, baseEnd_3529597] using wordTrace_append hprefix tailTrace_3529597
  have hstable : (prefixWord ++ tailWord_3529597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529597).length < 2 ^ (prefixWord ++ tailWord_3529597).sum := by decide
  have hdescent : baseEnd_3529597 < baseStart_3529597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529631 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3529631 : Nat := 118140960795 + 3529631 * 2 ^ 59
def prefixEnd_3529631 : Nat := 4983230072969 + 3 ^ 40 * 3529631 * 2
def baseEnd_3529631 : Nat := 1812397236009785036180029

theorem tailTrace_3529631 : CollatzResearch.WordTrace tailWord_3529631 prefixEnd_3529631 1812397236009785036180029 := by
  unfold tailWord_3529631
  simp only [CollatzResearch.WordTrace]
  refine ⟨128736218675757174827516747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85824145783838116551677831 128736218675757174827516747)
  ·
    refine ⟨193104328013635762241275121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128736218675757174827516747 193104328013635762241275121)
    ·
      refine ⟨144828246010226821680956341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193104328013635762241275121 144828246010226821680956341)
      ·
        refine ⟨13577648063458764532589657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144828246010226821680956341 13577648063458764532589657)
        ·
          refine ⟨10183236047594073399442243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13577648063458764532589657 10183236047594073399442243)
          ·
            refine ⟨15274854071391110099163365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183236047594073399442243 15274854071391110099163365)
            ·
              refine ⟨2864035138385833143593131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15274854071391110099163365 2864035138385833143593131)
              ·
                refine ⟨4296052707578749715389697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864035138385833143593131 4296052707578749715389697)
                ·
                  refine ⟨3222039530684062286542273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4296052707578749715389697 3222039530684062286542273)
                  ·
                    refine ⟨2416529648013046714906705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222039530684062286542273 2416529648013046714906705)
                    ·
                      refine ⟨1812397236009785036180029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416529648013046714906705 1812397236009785036180029)
                      ·
                        rfl

theorem cell23_3529631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3529631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529631 prefixEnd_3529631 := by exact prefixLift 3529631
  have htrace : WordTrace (prefixWord ++ tailWord_3529631) baseStart_3529631 baseEnd_3529631 := by
    simpa [prefixWord, tailWord_3529631, baseEnd_3529631] using wordTrace_append hprefix tailTrace_3529631
  have hstable : (prefixWord ++ tailWord_3529631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529631).length < 2 ^ (prefixWord ++ tailWord_3529631).sum := by decide
  have hdescent : baseEnd_3529631 < baseStart_3529631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529680 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_3529680 : Nat := 118140960795 + 3529680 * 2 ^ 59
def prefixEnd_3529680 : Nat := 4983230072969 + 3 ^ 40 * 3529680 * 2
def baseEnd_3529680 : Nat := 604140798853951781489101

theorem tailTrace_3529680 : CollatzResearch.WordTrace tailWord_3529680 prefixEnd_3529680 604140798853951781489101 := by
  unfold tailWord_3529680
  simp only [CollatzResearch.WordTrace]
  refine ⟨64369002926289828098025247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85825337235053104130700329 64369002926289828098025247)
  ·
    refine ⟨96553504389434742147037871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64369002926289828098025247 96553504389434742147037871)
    ·
      refine ⟨144830256584152113220556807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96553504389434742147037871 144830256584152113220556807)
      ·
        refine ⟨217245384876228169830835211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144830256584152113220556807 217245384876228169830835211)
        ·
          refine ⟨325868077314342254746252817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217245384876228169830835211 325868077314342254746252817)
          ·
            refine ⟨244401057985756691059689613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325868077314342254746252817 244401057985756691059689613)
            ·
              refine ⟨91650396744658759147383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244401057985756691059689613 91650396744658759147383605)
              ·
                refine ⟨8592224694811758670067213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91650396744658759147383605 8592224694811758670067213)
                ·
                  refine ⟨3222084260554409501275205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8592224694811758670067213 3222084260554409501275205)
                  ·
                    refine ⟨604140798853951781489101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222084260554409501275205 604140798853951781489101)
                    ·
                      rfl

theorem cell23_3529680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_3529680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529680 prefixEnd_3529680 := by exact prefixLift 3529680
  have htrace : WordTrace (prefixWord ++ tailWord_3529680) baseStart_3529680 baseEnd_3529680 := by
    simpa [prefixWord, tailWord_3529680, baseEnd_3529680] using wordTrace_append hprefix tailTrace_3529680
  have hstable : (prefixWord ++ tailWord_3529680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529680).length < 2 ^ (prefixWord ++ tailWord_3529680).sum := by decide
  have hdescent : baseEnd_3529680 < baseStart_3529680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529701 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_3529701 : Nat := 118140960795 + 3529701 * 2 ^ 59
def prefixEnd_3529701 : Nat := 4983230072969 + 3 ^ 40 * 3529701 * 2
def baseEnd_3529701 : Nat := 604144393218533254101569

theorem tailTrace_3529701 : CollatzResearch.WordTrace tailWord_3529701 prefixEnd_3529701 604144393218533254101569 := by
  unfold tailWord_3529701
  simp only [CollatzResearch.WordTrace]
  refine ⟨128738771785503576782564957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85825847857002384521709971 128738771785503576782564957)
  ·
    refine ⟨48277039419563841293461859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128738771785503576782564957 48277039419563841293461859)
    ·
      refine ⟨72415559129345761940192789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48277039419563841293461859 72415559129345761940192789)
      ·
        refine ⟨3394479334188082590946537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72415559129345761940192789 3394479334188082590946537)
        ·
          refine ⟨2545859500641061943209903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394479334188082590946537 2545859500641061943209903)
          ·
            refine ⟨3818789250961592914814855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545859500641061943209903 3818789250961592914814855)
            ·
              refine ⟨5728183876442389372222283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818789250961592914814855 5728183876442389372222283)
              ·
                refine ⟨8592275814663584058333425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728183876442389372222283 8592275814663584058333425)
                ·
                  refine ⟨6444206860997688043750069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592275814663584058333425 6444206860997688043750069)
                  ·
                    refine ⟨604144393218533254101569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6444206860997688043750069 604144393218533254101569)
                    ·
                      rfl

theorem cell23_3529701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_3529701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529701 prefixEnd_3529701 := by exact prefixLift 3529701
  have htrace : WordTrace (prefixWord ++ tailWord_3529701) baseStart_3529701 baseEnd_3529701 := by
    simpa [prefixWord, tailWord_3529701, baseEnd_3529701] using wordTrace_append hprefix tailTrace_3529701
  have hstable : (prefixWord ++ tailWord_3529701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529701).length < 2 ^ (prefixWord ++ tailWord_3529701).sum := by decide
  have hdescent : baseEnd_3529701 < baseStart_3529701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529743 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_3529743 : Nat := 118140960795 + 3529743 * 2 ^ 59
def prefixEnd_3529743 : Nat := 4983230072969 + 3 ^ 40 * 3529743 * 2
def baseEnd_3529743 : Nat := 1812454745843088597979513

theorem tailTrace_3529743 : CollatzResearch.WordTrace tailWord_3529743 prefixEnd_3529743 1812454745843088597979513 := by
  unfold tailWord_3529743
  simp only [CollatzResearch.WordTrace]
  refine ⟨128740303651351417955593883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85826869100900945303729255 128740303651351417955593883)
  ·
    refine ⟨193110455477027126933390825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128740303651351417955593883 193110455477027126933390825)
    ·
      refine ⟨144832841607770345200043119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193110455477027126933390825 144832841607770345200043119)
      ·
        refine ⟨217249262411655517800064679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144832841607770345200043119 217249262411655517800064679)
        ·
          refine ⟨325873893617483276700097019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217249262411655517800064679 325873893617483276700097019)
          ·
            refine ⟨488810840426224915050145529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325873893617483276700097019 488810840426224915050145529)
            ·
              refine ⟨366608130319668686287609147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488810840426224915050145529 366608130319668686287609147)
              ·
                refine ⟨549912195479503029431413721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366608130319668686287609147 549912195479503029431413721)
                ·
                  refine ⟨412434146609627272073560291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549912195479503029431413721 412434146609627272073560291)
                  ·
                    refine ⟨618651219914440908110340437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 412434146609627272073560291 618651219914440908110340437)
                    ·
                      refine ⟨1812454745843088597979513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 618651219914440908110340437 1812454745843088597979513)
                      ·
                        rfl

theorem cell23_3529743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_3529743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529743 prefixEnd_3529743 := by exact prefixLift 3529743
  have htrace : WordTrace (prefixWord ++ tailWord_3529743) baseStart_3529743 baseEnd_3529743 := by
    simpa [prefixWord, tailWord_3529743, baseEnd_3529743] using wordTrace_append hprefix tailTrace_3529743
  have hstable : (prefixWord ++ tailWord_3529743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529743).length < 2 ^ (prefixWord ++ tailWord_3529743).sum := by decide
  have hdescent : baseEnd_3529743 < baseStart_3529743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529764 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3529764 : Nat := 118140960795 + 3529764 * 2 ^ 59
def prefixEnd_3529764 : Nat := 4983230072969 + 3 ^ 40 * 3529764 * 2
def baseEnd_3529764 : Nat := 1812465528936833015816917

theorem tailTrace_3529764 : CollatzResearch.WordTrace tailWord_3529764 prefixEnd_3529764 1812465528936833015816917 := by
  unfold tailWord_3529764
  simp only [CollatzResearch.WordTrace]
  refine ⟨64370534792137669271054173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85827379722850225694738897 64370534792137669271054173)
  ·
    refine ⟨24138950547051625976645315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64370534792137669271054173 24138950547051625976645315)
    ·
      refine ⟨36208425820577438964967973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24138950547051625976645315 36208425820577438964967973)
      ·
        refine ⟨6789079841358269805931495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36208425820577438964967973 6789079841358269805931495)
        ·
          refine ⟨10183619762037404708897243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789079841358269805931495 10183619762037404708897243)
          ·
            refine ⟨15275429643056107063345865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183619762037404708897243 15275429643056107063345865)
            ·
              refine ⟨11456572232292080297509399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15275429643056107063345865 11456572232292080297509399)
              ·
                refine ⟨17184858348438120446264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456572232292080297509399 17184858348438120446264099)
                ·
                  refine ⟨25777287522657180669396149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17184858348438120446264099 25777287522657180669396149)
                  ·
                    refine ⟨2416620705249110687755889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25777287522657180669396149 2416620705249110687755889)
                    ·
                      refine ⟨1812465528936833015816917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416620705249110687755889 1812465528936833015816917)
                      ·
                        rfl

theorem cell23_3529764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3529764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529764 prefixEnd_3529764 := by exact prefixLift 3529764
  have htrace : WordTrace (prefixWord ++ tailWord_3529764) baseStart_3529764 baseEnd_3529764 := by
    simpa [prefixWord, tailWord_3529764, baseEnd_3529764] using wordTrace_append hprefix tailTrace_3529764
  have hstable : (prefixWord ++ tailWord_3529764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529764).length < 2 ^ (prefixWord ++ tailWord_3529764).sum := by decide
  have hdescent : baseEnd_3529764 < baseStart_3529764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529777 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3529777 : Nat := 118140960795 + 3529777 * 2 ^ 59
def prefixEnd_3529777 : Nat := 4983230072969 + 3 ^ 40 * 3529777 * 2
def baseEnd_3529777 : Nat := 1812472204185341464954357

theorem tailTrace_3529777 : CollatzResearch.WordTrace tailWord_3529777 prefixEnd_3529777 1812472204185341464954357 := by
  unfold tailWord_3529777
  simp only [CollatzResearch.WordTrace]
  refine ⟨128741543733228241762331585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85827695822152161174887723 128741543733228241762331585)
  ·
    refine ⟨96556157799921181321748689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128741543733228241762331585 96556157799921181321748689)
    ·
      refine ⟨72417118349940885991311517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96556157799921181321748689 72417118349940885991311517)
      ·
        refine ⟨27156419381227832246741819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72417118349940885991311517 27156419381227832246741819)
        ·
          refine ⟨40734629071841748370112729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27156419381227832246741819 40734629071841748370112729)
          ·
            refine ⟨30550971803881311277584547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40734629071841748370112729 30550971803881311277584547)
            ·
              refine ⟨45826457705821966916376821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30550971803881311277584547 45826457705821966916376821)
              ·
                refine ⟨4296230409920809398410327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45826457705821966916376821 4296230409920809398410327)
                ·
                  refine ⟨6444345614881214097615491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296230409920809398410327 6444345614881214097615491)
                  ·
                    refine ⟨9666518422321821146423237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444345614881214097615491 9666518422321821146423237)
                    ·
                      refine ⟨1812472204185341464954357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9666518422321821146423237 1812472204185341464954357)
                      ·
                        rfl

theorem cell23_3529777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3529777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529777 prefixEnd_3529777 := by exact prefixLift 3529777
  have htrace : WordTrace (prefixWord ++ tailWord_3529777) baseStart_3529777 baseEnd_3529777 := by
    simpa [prefixWord, tailWord_3529777, baseEnd_3529777] using wordTrace_append hprefix tailTrace_3529777
  have hstable : (prefixWord ++ tailWord_3529777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529777).length < 2 ^ (prefixWord ++ tailWord_3529777).sum := by decide
  have hdescent : baseEnd_3529777 < baseStart_3529777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529788 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_3529788 : Nat := 118140960795 + 3529788 * 2 ^ 59
def prefixEnd_3529788 : Nat := 4983230072969 + 3 ^ 40 * 3529788 * 2
def baseEnd_3529788 : Nat := 1812477852472540921916807

theorem tailTrace_3529788 : CollatzResearch.WordTrace tailWord_3529788 prefixEnd_3529788 1812477852472540921916807 := by
  unfold tailWord_3529788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64370972468094195320491009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85827963290792260427321345 64370972468094195320491009)
  ·
    refine ⟨48278229351070646490368257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64370972468094195320491009 48278229351070646490368257)
    ·
      refine ⟨36208672013302984867776193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48278229351070646490368257 36208672013302984867776193)
      ·
        refine ⟨27156504009977238650832145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36208672013302984867776193 27156504009977238650832145)
        ·
          refine ⟨20367378007482928988124109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27156504009977238650832145 20367378007482928988124109)
          ·
            refine ⟨7637766752806098370546541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20367378007482928988124109 7637766752806098370546541)
            ·
              refine ⟨2864162532302286888954953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7637766752806098370546541 2864162532302286888954953)
              ·
                refine ⟨2148121899226715166716215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864162532302286888954953 2148121899226715166716215)
                ·
                  refine ⟨3222182848840072750074323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148121899226715166716215 3222182848840072750074323)
                  ·
                    refine ⟨4833274273260109125111485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222182848840072750074323 4833274273260109125111485)
                    ·
                      refine ⟨1812477852472540921916807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4833274273260109125111485 1812477852472540921916807)
                      ·
                        rfl

theorem cell23_3529788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_3529788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529788 prefixEnd_3529788 := by exact prefixLift 3529788
  have htrace : WordTrace (prefixWord ++ tailWord_3529788) baseStart_3529788 baseEnd_3529788 := by
    simpa [prefixWord, tailWord_3529788, baseEnd_3529788] using wordTrace_append hprefix tailTrace_3529788
  have hstable : (prefixWord ++ tailWord_3529788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529788).length < 2 ^ (prefixWord ++ tailWord_3529788).sum := by decide
  have hdescent : baseEnd_3529788 < baseStart_3529788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529800 : List Nat := [2, 1, 3, 1, 1, 1, 6, 8]
def baseStart_3529800 : Nat := 118140960795 + 3529800 * 2 ^ 59
def prefixEnd_3529800 : Nat := 4983230072969 + 3 ^ 40 * 3529800 * 2
def baseEnd_3529800 : Nat := 67129037564459069443213

theorem tailTrace_3529800 : CollatzResearch.WordTrace tailWord_3529800 prefixEnd_3529800 67129037564459069443213 := by
  unfold tailWord_3529800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64371191306072458345209427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85828255074763277793612569 64371191306072458345209427)
  ·
    refine ⟨96556786959108687517814141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64371191306072458345209427 96556786959108687517814141)
    ·
      refine ⟨36208795109665757819180303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96556786959108687517814141 36208795109665757819180303)
      ·
        refine ⟨54313192664498636728770455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36208795109665757819180303 54313192664498636728770455)
        ·
          refine ⟨81469788996747955093155683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54313192664498636728770455 81469788996747955093155683)
          ·
            refine ⟨122204683495121932639733525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81469788996747955093155683 122204683495121932639733525)
            ·
              refine ⟨5728344538833840592487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122204683495121932639733525 5728344538833840592487509)
              ·
                refine ⟨67129037564459069443213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5728344538833840592487509 67129037564459069443213)
                ·
                  rfl

theorem cell23_3529800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 8].length) (baseStart_3529800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529800 prefixEnd_3529800 := by exact prefixLift 3529800
  have htrace : WordTrace (prefixWord ++ tailWord_3529800) baseStart_3529800 baseEnd_3529800 := by
    simpa [prefixWord, tailWord_3529800, baseEnd_3529800] using wordTrace_append hprefix tailTrace_3529800
  have hstable : (prefixWord ++ tailWord_3529800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529800).length < 2 ^ (prefixWord ++ tailWord_3529800).sum := by decide
  have hdescent : baseEnd_3529800 < baseStart_3529800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529831 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_3529831 : Nat := 118140960795 + 3529831 * 2 ^ 59
def prefixEnd_3529831 : Nat := 4983230072969 + 3 ^ 40 * 3529831 * 2
def baseEnd_3529831 : Nat := 1812499932140684253679109

theorem tailTrace_3529831 : CollatzResearch.WordTrace tailWord_3529831 prefixEnd_3529831 1812499932140684253679109 := by
  unfold tailWord_3529831
  simp only [CollatzResearch.WordTrace]
  refine ⟨128743513275032608984797347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85829008850021739323198231 128743513275032608984797347)
  ·
    refine ⟨193115269912548913477196021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128743513275032608984797347 193115269912548913477196021)
    ·
      refine ⟨18104556554301460638487127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193115269912548913477196021 18104556554301460638487127)
      ·
        refine ⟨27156834831452190957730691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18104556554301460638487127 27156834831452190957730691)
        ·
          refine ⟨40735252247178286436596037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27156834831452190957730691 40735252247178286436596037)
          ·
            refine ⟨7637859796345928706861757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40735252247178286436596037 7637859796345928706861757)
            ·
              refine ⟨2864197423629723265073159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7637859796345928706861757 2864197423629723265073159)
              ·
                refine ⟨4296296135444584897609739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864197423629723265073159 4296296135444584897609739)
                ·
                  refine ⟨6444444203166877346414609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296296135444584897609739 6444444203166877346414609)
                  ·
                    refine ⟨4833333152375158009810957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444444203166877346414609 4833333152375158009810957)
                    ·
                      refine ⟨1812499932140684253679109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4833333152375158009810957 1812499932140684253679109)
                      ·
                        rfl

theorem cell23_3529831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_3529831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529831 prefixEnd_3529831 := by exact prefixLift 3529831
  have htrace : WordTrace (prefixWord ++ tailWord_3529831) baseStart_3529831 baseEnd_3529831 := by
    simpa [prefixWord, tailWord_3529831, baseEnd_3529831] using wordTrace_append hprefix tailTrace_3529831
  have hstable : (prefixWord ++ tailWord_3529831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529831).length < 2 ^ (prefixWord ++ tailWord_3529831).sum := by decide
  have hdescent : baseEnd_3529831 < baseStart_3529831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529900 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3529900 : Nat := 118140960795 + 3529900 * 2 ^ 59
def prefixEnd_3529900 : Nat := 4983230072969 + 3 ^ 40 * 3529900 * 2
def baseEnd_3529900 : Nat := 1812535362305844483716291

theorem tailTrace_3529900 : CollatzResearch.WordTrace tailWord_3529900 prefixEnd_3529900 1812535362305844483716291 := by
  unfold tailWord_3529900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64373014955891316884529577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85830686607855089179372769 64373014955891316884529577)
  ·
    refine ⟨48279761216918487663397183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64373014955891316884529577 48279761216918487663397183)
    ·
      refine ⟨72419641825377731495095775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48279761216918487663397183 72419641825377731495095775)
      ·
        refine ⟨108629462738066597242643663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72419641825377731495095775 108629462738066597242643663)
        ·
          refine ⟨162944194107099895863965495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108629462738066597242643663 162944194107099895863965495)
          ·
            refine ⟨244416291160649843795948243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162944194107099895863965495 244416291160649843795948243)
            ·
              refine ⟨366624436740974765693922365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244416291160649843795948243 366624436740974765693922365)
              ·
                refine ⟨137484163777865537135220887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366624436740974765693922365 137484163777865537135220887)
                ·
                  refine ⟨206226245666798305702831331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137484163777865537135220887 206226245666798305702831331)
                  ·
                    refine ⟨309339368500197458554246997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206226245666798305702831331 309339368500197458554246997)
                    ·
                      refine ⟨1812535362305844483716291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 309339368500197458554246997 1812535362305844483716291)
                      ·
                        rfl

theorem cell23_3529900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3529900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529900 prefixEnd_3529900 := by exact prefixLift 3529900
  have htrace : WordTrace (prefixWord ++ tailWord_3529900) baseStart_3529900 baseEnd_3529900 := by
    simpa [prefixWord, tailWord_3529900, baseEnd_3529900] using wordTrace_append hprefix tailTrace_3529900
  have hstable : (prefixWord ++ tailWord_3529900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529900).length < 2 ^ (prefixWord ++ tailWord_3529900).sum := by decide
  have hdescent : baseEnd_3529900 < baseStart_3529900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
